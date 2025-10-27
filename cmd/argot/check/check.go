// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package check

import (
	"fmt"
	"os"
	"runtime"
	"time"

	"github.com/awslabs/ar-go-tools/analysis"
	"github.com/awslabs/ar-go-tools/analysis/config"
	"github.com/awslabs/ar-go-tools/analysis/dataflow"
	"github.com/awslabs/ar-go-tools/analysis/loadprogram"
	"github.com/awslabs/ar-go-tools/analysis/ptr"
	"github.com/awslabs/ar-go-tools/analysis/refactor/statefulrewrite"
	"github.com/awslabs/ar-go-tools/cmd/argot/tools"
	"github.com/awslabs/ar-go-tools/internal/formatutil"
	"github.com/awslabs/ar-go-tools/internal/funcutil/result"
	"golang.org/x/tools/go/ssa"
)

const usage = ` Perform external summary soundness check on your packages.
Usage:
  argot check [options] [package path(s)]
Examples:
  % argot check -config config.yaml package...
`

// Flags represents the parsed flags for the check analysis.
type Flags struct {
	tools.CommonFlags
	maxDepth int
	dryRun   bool
}

// NewFlags returns the parsed flags for the check analysis with args.
func NewFlags(args []string) (Flags, error) {
	flags := tools.NewUnparsedCommonFlags("check")
	maxDepth := flags.FlagSet.Int("unsafe-df-max-depth", -1, "override dataflow max depth in config: unsafe!")
	dryRun := flags.FlagSet.Bool("dry-run", false, "analysis dry-run: only identify code locations")
	tools.SetUsage(flags.FlagSet, usage)
	if err := flags.FlagSet.Parse(args); err != nil {
		return Flags{}, fmt.Errorf("failed to parse command check with args %v: %v", args, err)
	}

	return Flags{
		CommonFlags: tools.CommonFlags{
			FlagSet:    flags.FlagSet,
			ConfigPath: *flags.ConfigPath,
			Verbose:    *flags.Verbose,
			WithTest:   *flags.WithTest,
			Tag:        *flags.Tag,
			Targets:    *flags.Targets,
			Platform:   *flags.Platform,
			Out:        *flags.Out,
		},
		maxDepth: *maxDepth,
		dryRun:   *dryRun,
	}, nil
}

// Run runs the check analysis with flags.
func Run(flags Flags) error {
	cfg, err := tools.LoadConfig(flags.CommonFlags, false)
	if err != nil {
		return err
	}
	tmpLogger := config.NewLogGroup(cfg)
	tmpLogger.Infof(formatutil.Faint("Argot check tool - " + analysis.Version))
	// Override config parameters with command-line parameters
	if flags.maxDepth > 0 {
		cfg.UnsafeMaxDepth = flags.maxDepth
		tmpLogger.Warnf("%s %d\n", "UNSAFE config max data-flow depth set to: %s", flags.maxDepth)
	}
	if flags.dryRun {
		tmpLogger.Infof("dry-run command line flag sets on demand summarization to true")
		cfg.SummarizeOnDemand = true
	}
	if flags.Tag != "" {
		tmpLogger.Infof("tag specified on command-line, will analyze only problem with tag \"%s\"", flags.Tag)
	}
	if flags.Targets != "" {
		tmpLogger.Infof("target specified on command-line, will analyze only for problems with targets in \"%s\"",
			flags.Targets)
	}

	hasUnsound := false
	overallReport := config.NewReport()

	actualTargets, err := tools.GetTargets(cfg, tools.TargetReqs{
		CmdlineArgs: flags.FlagSet.Args(),
		Tag:         flags.Tag,
		Targets:     flags.Targets,
		Platform:    flags.Platform,
		Tool:        config.CheckTool,
	})
	if err != nil {
		return fmt.Errorf("failed to get check targets: %s", err)
	}
	// Loop over every target of the check analysis
	for targetName, target := range actualTargets {
		targetHasUnsound, report, err := runTarget(cfg, targetName, target, flags)
		if err != nil {
			// allow continuing to other targets even if one fails
			tmpLogger.Errorf("Error analyzing target %s: %v", targetName, err)
		}
		hasUnsound = targetHasUnsound || hasUnsound
		overallReport.Merge(report)
	}

	overallReport.Dump(config.ConfiguredLogger{Config: cfg, Logger: tmpLogger})
	if hasUnsound {
		return fmt.Errorf("check analysis found problems, inspect logs for more information")
	}
	return nil
}

func runTarget(
	cfg *config.Config,
	targetName string,
	targetInfo config.TargetInfo,
	flags Flags,
) (bool, *config.ReportInfo, error) {
	var err error
	loadOptions := config.LoadOptions{
		PackageConfig: nil,
		BuildMode:     ssa.InstantiateGenerics,
		LoadTests:     flags.WithTest,
		Platform:      targetInfo.Platform,
		ApplyRewrites: true,
	}
	// Starting the analysis
	c := config.NewState(cfg, targetName, targetInfo.Patterns, loadOptions)

	c.Logger.PushContext(formatutil.Faint(targetName))
	defer c.Logger.PopContext()
	c.Logger.Infof("Check analysis of target \"%s\" = %v", targetName, targetInfo.Patterns)
	var actual result.Result[config.State]
	if targetInfo.UseProgramTransforms && len(targetInfo.ReflectValueCallInstances) >= 1 {
		c.Logger.Infof("Reflect value call instances specified. Tool supports only 1 for now, will use the first.")
		// TODO: handle more rewrites later
		actual = statefulrewrite.StatefulRewritesOverlayTransform(c,
			statefulrewrite.StatefulRewritesOverlayTransformSpec{ReflectValueCallInstanceCid: targetInfo.ReflectValueCallInstances[0]})
	} else {
		actual = result.Ok(c)
	}
	df, err := result.Bind(
		result.Bind(
			result.Bind(
				actual,
				loadprogram.NewState),
			ptr.NewState),
		dataflow.NewState).Value()
	if err != nil {
		return false, nil, fmt.Errorf("failed to initialize dataflow state: %s", err)
	}

	// Run intra-procedural pass to build summaries for all functions.
	// This is a necessary step before the inter-procedural graph can be built and checked.
	dataflow.RunIntraProceduralPass(df, runtime.NumCPU(),
		dataflow.IntraAnalysisParams{
			ShouldBuildSummary: dataflow.ShouldBuildSummary,
			ShouldTrack:        dataflow.IsNodeOfInterest,
		})

	// Now, run the external summary soundness check.
	// The CheckExternalSummaries function will internally call BuildGraph if needed.
	return RunCheck(targetName, flags.CommonFlags, df)
}

// RunCheck runs the external summary soundness check on the dataflow state
func RunCheck(targetName string, flags tools.CommonFlags, df *dataflow.State) (bool, *config.ReportInfo, error) {
	start := time.Now()
	// BuildGraph now returns unsound summaries found during loading.
	unsoundSummaries := df.FlowGraph.BuildGraph()
	// CheckExternalSummaries will check the rest and append.
	additionalUnsound, err := df.FlowGraph.CheckExternalSummaries()
	if err != nil {
		if df.Report != nil {
			for _, checkErr := range df.Report.CheckError() {
				fmt.Fprintf(os.Stderr, "\terror: %v\n", checkErr)
			}
		}
		return false, nil, fmt.Errorf("external summary soundness check failed: %v", err)
	}

	// Merge and deduplicate unsound summaries
	for _, summary := range additionalUnsound {
		isNew := true
		for _, existing := range unsoundSummaries {
			if existing == summary {
				isNew = false
				break
			}
		}
		if isNew {
			unsoundSummaries = append(unsoundSummaries, summary)
		}
	}

	duration := time.Since(start)

	// Printing final results
	targetStr := ""
	if targetName != "" {
		targetStr = "TARGET " + targetName + " "
	}
	df.Logger.Infof("")
	df.Logger.Infof("External summary soundness check took %3.4f s", duration.Seconds())
	df.Logger.Infof("")

	if len(unsoundSummaries) == 0 {
		df.Logger.Infof(
			"%sRESULT:\n\t\t%s",
			targetStr,
			formatutil.Green("All external summaries are sound ✓"))
	} else {
		df.Logger.Errorf(
			"%sRESULT:\n\t\t%s",
			targetStr,
			formatutil.Red(len(unsoundSummaries), " unsound external summaries detected!"))
		df.Logger.Errorf("Unsound summaries:")
		for _, summary := range unsoundSummaries {
			df.Logger.Errorf("\t- %s", summary.Parent.String())
		}
	}

	return len(unsoundSummaries) > 0, df.Report, nil
}
