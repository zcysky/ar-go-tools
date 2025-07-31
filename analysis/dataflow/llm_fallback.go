package dataflow

import (
	"context"
	"encoding/json"
	"fmt"
	"go/ast"
	"go/parser"
	"go/token"
	"io/ioutil"
	"regexp"
	"strconv"
	"strings"
	"time"

	"github.com/aws/aws-sdk-go/aws"
	"github.com/aws/aws-sdk-go/aws/session"
	"github.com/aws/aws-sdk-go/service/bedrockruntime"
	"golang.org/x/tools/go/ssa"
	"gopkg.in/yaml.v3"
)

// LLMDataflowSummary represents the YAML structure returned by LLM
type LLMDataflowSummary struct {
	DataflowSummaries []LLMFlowSummary `yaml:"dataflow-summaries"`
}

type LLMFlowSummary struct {
	Function string    `yaml:"function,omitempty"`
	Receiver string    `yaml:"receiver,omitempty"`
	Method   string    `yaml:"method,omitempty"`
	Flows    []LLMFlow `yaml:"flows"`
}

type LLMFlow struct {
	From string `yaml:"from"`
	To   string `yaml:"to"`
}

// GetLLMSummary recovers the source code for the given function, calls AWS Bedrock LLM, and returns a SummaryGraph.
func GetLLMSummary(ctx context.Context, fn *ssa.Function, promptPath string, modelName string) (*SummaryGraph, error) {
	// Step 1: Recover function source code using go/ast
	file := fn.Syntax()
	if file == nil {
		return nil, fmt.Errorf("no syntax available for function %s", fn.Name())
	}
	fset := token.NewFileSet()
	var srcFile string
	if fn.Pos() != 0 {
		pos := fset.Position(fn.Pos())
		srcFile = pos.Filename
	} else {
		return nil, fmt.Errorf("cannot determine source file for function %s", fn.Name())
	}
	codeBytes, err := ioutil.ReadFile(srcFile)
	if err != nil {
		return nil, fmt.Errorf("failed to read source file: %v", err)
	}
	fileAst, err := parser.ParseFile(fset, srcFile, codeBytes, parser.ParseComments)
	if err != nil {
		return nil, fmt.Errorf("failed to parse source file: %v", err)
	}
	var funcSrc string
	ast.Inspect(fileAst, func(n ast.Node) bool {
		if fnDecl, ok := n.(*ast.FuncDecl); ok {
			if fnDecl.Name.Name == fn.Name() {
				start := fset.Position(fnDecl.Pos()).Offset
				end := fset.Position(fnDecl.End()).Offset
				funcSrc = string(codeBytes[start:end])
				return false
			}
		}
		return true
	})
	if funcSrc == "" {
		return nil, fmt.Errorf("could not extract source for function %s", fn.Name())
	}

	// Step 2: Read prompt
	promptBytes, err := ioutil.ReadFile(promptPath)
	if err != nil {
		return nil, fmt.Errorf("failed to read prompt: %v", err)
	}
	prompt := string(promptBytes)

	// Step 3: Call AWS Bedrock LLM
	sess, err := session.NewSession(&aws.Config{
		Region: aws.String("us-west-2"),
	})
	if err != nil {
		return nil, fmt.Errorf("error creating AWS session: %v", err)
	}
	bedrockRuntimeClient := bedrockruntime.New(sess)
	requestBody := map[string]interface{}{
		"anthropic_version": "bedrock-2023-05-31",
		"max_tokens":        2048,
		"temperature":       0.7,
		"messages": []map[string]interface{}{
			{
				"role":    "user",
				"content": prompt + "\n\n### Input Program:\n```go\n" + funcSrc + "\n```",
			},
		},
	}
	requestJSON, err := json.Marshal(requestBody)
	if err != nil {
		return nil, fmt.Errorf("error marshaling request: %v", err)
	}
	var invokeOutput *bedrockruntime.InvokeModelOutput
	baseWaitingTime := 1.0 * time.Second
	maxRetries := 5
	for attemptTimes := 0; attemptTimes <= maxRetries; attemptTimes++ {
		modelID := modelName
		invokeOutput, err = bedrockRuntimeClient.InvokeModelWithContext(ctx, &bedrockruntime.InvokeModelInput{
			ModelId: aws.String(modelID),
			Body:    requestJSON,
		})
		if err == nil {
			break
		} else if strings.Contains(err.Error(), "Too many tokens") {
			sleepTime := baseWaitingTime * (1 << attemptTimes)
			time.Sleep(sleepTime)
			continue
		} else {
			return nil, fmt.Errorf("error invoking model: %v", err)
		}
	}
	var responseBody map[string]interface{}
	if err := json.Unmarshal(invokeOutput.Body, &responseBody); err != nil {
		return nil, fmt.Errorf("error unmarshaling response: %v", err)
	}
	var generatedText string
	if content, ok := responseBody["content"].([]interface{}); ok {
		if len(content) > 0 {
			if contentMap, ok := content[0].(map[string]interface{}); ok {
				if text, ok := contentMap["text"].(string); ok {
					generatedText = text
				} else {
					return nil, fmt.Errorf("response body does not contain text")
				}
			} else {
				return nil, fmt.Errorf("response body does not contain text")
			}
		} else {
			return nil, fmt.Errorf("response body does not contain text")
		}
	} else {
		return nil, fmt.Errorf("response body does not contain text")
	}

	// Step 4: Extract YAML summary from LLM response
	re := regexp.MustCompile("(?s)```yaml\\s*(.*?)```")
	matches := re.FindStringSubmatch(generatedText)
	if len(matches) < 2 {
		return nil, fmt.Errorf("no YAML summary found in LLM response")
	}
	yamlSummary := matches[1]

	// Step 5: Parse YAML and build SummaryGraph
	return parseLLMYAMLAndBuildSummary(fn, yamlSummary)
}

// parseLLMYAMLAndBuildSummary parses the LLM YAML response and builds a SummaryGraph
func parseLLMYAMLAndBuildSummary(fn *ssa.Function, yamlContent string) (*SummaryGraph, error) {
	var llmSummary LLMDataflowSummary
	if err := yaml.Unmarshal([]byte(yamlContent), &llmSummary); err != nil {
		return nil, fmt.Errorf("failed to parse YAML: %v", err)
	}

	if len(llmSummary.DataflowSummaries) == 0 {
		return nil, fmt.Errorf("no dataflow summaries found in YAML")
	}

	// For now, we'll use the first summary (assuming single function analysis)
	flowSummary := llmSummary.DataflowSummaries[0]

	// Create a new SummaryGraph using the proper constructor
	summaryGraph := NewSummaryGraph(nil, fn, 0,
		func(*State, ssa.Node) bool { return true },
		func(*IntraAnalysisState) {},
	)

	summaryGraph.Constructed = true
	summaryGraph.IsPreSummarized = true

	// Process LLM flows and create actual edges
	for _, flow := range flowSummary.Flows {
		srcIndex, srcType, err := parseLLMNode(flow.From, fn)
		if err != nil {
			fmt.Printf("Warning: failed to parse source node '%s': %v\n", flow.From, err)
			continue
		}
		destIndex, destType, err := parseLLMNode(flow.To, fn)
		if err != nil {
			fmt.Printf("Warning: failed to parse destination node '%s': %v\n", flow.To, err)
			continue
		}
		// 直接用包内未导出方法创建边
		if srcType == "argument" || srcType == "receiver" {
			if destType == "argument" || destType == "receiver" {
				summaryGraph.addParamEdgeByPos(srcIndex, destIndex)
			} else if destType == "return" {
				summaryGraph.addReturnEdgeByPos(srcIndex, destIndex)
			}
		}
	}

	return summaryGraph, nil
}

// parseLLMNode parses a node description from LLM and returns the index and type
func parseLLMNode(nodeDesc string, fn *ssa.Function) (int, string, error) {
	// Handle receiver
	if nodeDesc == "!receiver" || nodeDesc == "receiver" {
		if fn.Signature.Recv() == nil {
			return -1, "", fmt.Errorf("function has no receiver")
		}
		return 0, "receiver", nil
	}

	// Handle arguments: !arg 0, !arg 1, etc.
	if strings.HasPrefix(nodeDesc, "!arg ") {
		indexStr := strings.TrimPrefix(nodeDesc, "!arg ")
		index, err := strconv.Atoi(indexStr)
		if err != nil {
			return -1, "", fmt.Errorf("invalid argument index: %s", indexStr)
		}
		// Adjust index for receiver if present
		if fn.Signature.Recv() != nil {
			index++
		}
		return index, "argument", nil
	}

	// Handle returns: !ret 0, !ret 1, etc.
	if strings.HasPrefix(nodeDesc, "!ret ") {
		indexStr := strings.TrimPrefix(nodeDesc, "!ret ")
		index, err := strconv.Atoi(indexStr)
		if err != nil {
			return -1, "", fmt.Errorf("invalid return index: %s", indexStr)
		}
		return index, "return", nil
	}

	// Handle simple !ret (equivalent to !ret 0)
	if nodeDesc == "!ret" {
		return 0, "return", nil
	}

	// Try to parse as argument name: !arg <name>
	if strings.HasPrefix(nodeDesc, "!arg <") && strings.HasSuffix(nodeDesc, ">") {
		name := strings.TrimPrefix(nodeDesc, "!arg <")
		name = strings.TrimSuffix(name, ">")
		// Find parameter by name
		for i := 0; i < fn.Signature.Params().Len(); i++ {
			if fn.Signature.Params().At(i).Name() == name {
				// Adjust index for receiver if present
				if fn.Signature.Recv() != nil {
					return i + 1, "argument", nil
				}
				return i, "argument", nil
			}
		}
		return -1, "", fmt.Errorf("parameter name not found: %s", name)
	}

	return -1, "", fmt.Errorf("unrecognized node format: %s", nodeDesc)
}
