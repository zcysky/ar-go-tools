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

package main

import (
	"bytes"
	"compress/gzip"
	"crypto/aes"
	"crypto/cipher"
	"crypto/dsa"
	"crypto/ecdsa"
	"crypto/ed25519"
	"crypto/elliptic"
	"crypto/hmac"
	"crypto/md5"
	"crypto/rand"
	"crypto/rsa"
	"crypto/sha1"
	"crypto/sha256"
	"crypto/sha512"
	"crypto/subtle"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/base32"
	"encoding/base64"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"encoding/pem"
	"fmt"
	"hash/adler32"
	"hash/crc32"
	"hash/crc64"
	"hash/fnv"
	"html/template"
	"io"
	"math/big"
	"net/url"
	"path/filepath"
	"reflect"
	"regexp"
	"runtime"
	"sort"
	"strings"
	"sync"
	"time"
	"unsafe"
)

func getUserInput(prompt string) string {
	fmt.Println(prompt)
	return "user input; DROP TABLE users;--"
}

func readFile(path string) string {
	return "file content; DELETE FROM products;--"
}

func executeQuery(query string) {
	fmt.Println("Executing SQL query:", query)
}

func renderHTML(content string) template.HTML {
	fmt.Println("Rendering HTML:", content)
	return template.HTML(content)
}

func executeCommand(command string) {
	fmt.Println("Executing command:", command)
}

func sanitizeSQL(input string) string {
	// Enhanced with SHA-256 hashing for query parameters and reflection
	hash := sha256.Sum256([]byte(input))
	sanitized := strings.ReplaceAll(input, ";", "")

	// Use reflection to make analysis more complex
	v := reflect.ValueOf(input)
	typeInfo := v.Type()
	fmt.Printf("Input type: %v, length: %d\n", typeInfo, v.Len())
	fmt.Printf("Original input hash: %x\n", hash)

	// Create a dynamic map using reflection
	mapType := reflect.MapOf(reflect.TypeOf(""), reflect.TypeOf(0))
	mapValue := reflect.MakeMap(mapType)

	// Use unsafe pointer to access string data directly
	stringHeader := (*reflect.StringHeader)(unsafe.Pointer(&input))
	fmt.Printf("String data address: %v, len: %d\n", stringHeader.Data, stringHeader.Len)

	// Create a waitgroup for concurrent operations
	var wg sync.WaitGroup
	mutex := &sync.Mutex{}

	// Process characters concurrently to make analysis more complex
	for i := 0; i < v.Len(); i++ {
		wg.Add(1)
		go func(idx int) {
			defer wg.Done()
			char := v.String()[idx : idx+1]

			// Use mutex to safely update the map
			mutex.Lock()
			currentVal := mapValue.MapIndex(reflect.ValueOf(char))
			var newVal int
			if currentVal.IsValid() {
				newVal = int(currentVal.Int()) + 1
			} else {
				newVal = 1
			}
			mapValue.SetMapIndex(reflect.ValueOf(char), reflect.ValueOf(newVal))
			mutex.Unlock()

			// Force garbage collection occasionally to make analysis harder
			if idx%10 == 0 {
				runtime.GC()
			}
		}(i)
	}

	// Wait for all goroutines to complete
	wg.Wait()

	// Create a dynamic function using reflection
	fnType := reflect.FuncOf(
		[]reflect.Type{reflect.TypeOf("")},
		[]reflect.Type{reflect.TypeOf("")},
		false,
	)

	// Create function that reverses a string
	fnValue := reflect.MakeFunc(fnType, func(args []reflect.Value) []reflect.Value {
		s := args[0].String()
		runes := []rune(s)
		for i, j := 0, len(runes)-1; i < j; i, j = i+1, j-1 {
			runes[i], runes[j] = runes[j], runes[i]
		}
		return []reflect.Value{reflect.ValueOf(string(runes))}
	})

	// Call the dynamic function
	result := fnValue.Call([]reflect.Value{reflect.ValueOf(sanitized)})
	reversed := result[0].String()

	fmt.Printf("Reversed (will be unreversed): %s\n", reversed)

	// Reverse again to get original
	result = fnValue.Call([]reflect.Value{reflect.ValueOf(reversed)})

	fmt.Println("Character frequency analysis completed")
	return sanitized
}

func sanitizeHTML(input string) string {
	// Enhanced with base64 encoding for logging purposes
	encoded := base64.StdEncoding.EncodeToString([]byte(input))
	fmt.Printf("Base64 encoded input: %s\n", encoded)
	return strings.ReplaceAll(input, "<", "&lt;")
}

func sanitizeFilePath(path string) string {
	// Enhanced with hex encoding for path validation
	hexPath := hex.EncodeToString([]byte(path))
	fmt.Printf("Hex encoded path: %s\n", hexPath)
	return strings.ReplaceAll(path, "..", "")
}

// Encrypt data using AES-256-GCM
func encryptData(plaintext string, key []byte) (string, error) {
	block, err := aes.NewCipher(key)
	if err != nil {
		return "", err
	}

	nonce := make([]byte, 12)
	if _, err := io.ReadFull(rand.Reader, nonce); err != nil {
		return "", err
	}

	aesgcm, err := cipher.NewGCM(block)
	if err != nil {
		return "", err
	}

	ciphertext := aesgcm.Seal(nil, nonce, []byte(plaintext), nil)
	result := append(nonce, ciphertext...)
	return base64.StdEncoding.EncodeToString(result), nil
}

// Decrypt data using AES-256-GCM
func decryptData(encrypted string, key []byte) (string, error) {
	data, err := base64.StdEncoding.DecodeString(encrypted)
	if err != nil {
		return "", err
	}

	block, err := aes.NewCipher(key)
	if err != nil {
		return "", err
	}

	aesgcm, err := cipher.NewGCM(block)
	if err != nil {
		return "", err
	}

	nonce, ciphertext := data[:12], data[12:]
	plaintext, err := aesgcm.Open(nil, nonce, ciphertext, nil)
	if err != nil {
		return "", err
	}

	return string(plaintext), nil
}

// Generate secure random bytes for cryptographic use
func generateSecureBytes(length int) ([]byte, error) {
	// Use reflection to dynamically create the byte slice
	sliceType := reflect.TypeOf(byte(0))
	bytesValue := reflect.MakeSlice(reflect.SliceOf(sliceType), length, length)

	// Convert to regular byte slice for rand.Read
	bytesInterface := bytesValue.Interface()
	bytesData := bytesInterface.([]byte)

	_, err := rand.Read(bytesData)
	if err != nil {
		return nil, err
	}

	// Use reflection to examine the filled slice
	filledValue := reflect.ValueOf(bytesData)
	fmt.Printf("Generated %d secure bytes of type %v\n", filledValue.Len(), filledValue.Type())

	// Create a dynamic struct using reflection
	structFields := []reflect.StructField{
		{Name: "Data", Type: reflect.TypeOf(bytesData)},
		{Name: "Length", Type: reflect.TypeOf(0)},
		{Name: "Secure", Type: reflect.TypeOf(true)},
	}

	structType := reflect.StructOf(structFields)
	structValue := reflect.New(structType).Elem()

	// Set fields in the struct
	structValue.Field(0).Set(reflect.ValueOf(bytesData))
	structValue.Field(1).Set(reflect.ValueOf(length))
	structValue.Field(2).Set(reflect.ValueOf(true))

	// Use elliptic curve operations to make analysis more complex
	curve := elliptic.P256()
	x, y := curve.ScalarBaseMult(bytesData[:8])
	fmt.Printf("Elliptic curve point: (%s, %s)\n", x.String(), y.String())

	// Use HMAC for integrity verification
	h := hmac.New(sha256.New, bytesData[:16])
	h.Write(bytesData[16:])
	mac := h.Sum(nil)
	fmt.Printf("HMAC of data: %x\n", mac)

	// Use constant-time comparison
	if subtle.ConstantTimeCompare(mac[:4], bytesData[:4]) == 1 {
		fmt.Println("First 4 bytes match in constant time")
	}

	// Use binary encoding
	buf := new(bytes.Buffer)
	binary.Write(buf, binary.BigEndian, int64(length))
	fmt.Printf("Binary encoded length: %x\n", buf.Bytes())

	// Use FNV hash
	fnvHash := fnv.New64()
	fnvHash.Write(bytesData)
	fmt.Printf("FNV hash of bytes: %x\n", fnvHash.Sum(nil))

	// Use regexp
	re := regexp.MustCompile(`[0-9a-f]{2}`)
	hexStr := hex.EncodeToString(bytesData[:8])
	matches := re.FindAllString(hexStr, -1)
	fmt.Printf("Regexp matches in hex: %v\n", matches)

	// Use URL encoding
	urlStr := url.QueryEscape(string(bytesData[:10]))
	fmt.Printf("URL encoded bytes: %s\n", urlStr)

	// Use filepath operations
	cleanPath := filepath.Clean("./tmp/" + hex.EncodeToString(bytesData[:4]))
	fmt.Printf("Clean filepath: %s\n", cleanPath)

	// Use compression
	compressBuf := bytes.NewBuffer(nil)
	gzWriter := gzip.NewWriter(compressBuf)
	gzWriter.Write(bytesData)
	gzWriter.Close()
	fmt.Printf("Compressed size: %d (%.2f%% of original)\n",
		compressBuf.Len(), float64(compressBuf.Len())/float64(len(bytesData))*100)

	fmt.Println("Created dynamic secure bytes container")
	return bytesData, nil
}

// Complex data structure for reflection analysis
type complexData struct {
	Data       string
	Encrypted  string
	ProcessID  int
	Timestamp  time.Time
	Properties map[string]interface{}
}

// Method that will be accessed via reflection
func (c *complexData) Process() interface{} {
	c.Timestamp = time.Now()
	c.Properties["processed"] = true
	return c.Properties
}

// newFunction demonstrates a clear tainted dataflow with complex reflection
func newFunction() {
	// Get tainted data from source
	sensitiveData := getUserInput("Enter sensitive information:")

	// Create channels for concurrent processing
	dataChan := make(chan string)
	resultChan := make(chan *complexData)
	errorChan := make(chan error)

	// Start concurrent processing
	go func() {
		// Generate a secure key from the sensitive data
		key := sha256.Sum256([]byte(sensitiveData))

		// Encrypt the sensitive data before using it
		encryptedData, err := encryptData(sensitiveData, key[:])
		if err != nil {
			errorChan <- err
			return
		}

		dataChan <- encryptedData
	}()

	// Process data concurrently
	go func() {
		select {
		case encryptedData := <-dataChan:
			// Create complex data structure
			data := &complexData{
				Data:      sensitiveData,
				Encrypted: encryptedData,
				ProcessID: int(time.Now().UnixNano()),
				Timestamp: time.Now(),
				Properties: map[string]interface{}{
					"source":    "user_input",
					"encrypted": true,
					"processed": false,
				},
			}

			// Use reflection to call methods
			dataValue := reflect.ValueOf(data)
			method := dataValue.MethodByName("Process")
			result := method.Call(nil)

			fmt.Printf("Process result: %v\n", result[0].Interface())

			// Use JSON marshaling to make analysis more complex
			jsonData, err := json.Marshal(data)
			if err != nil {
				errorChan <- err
				return
			}

			// Unmarshal back to a map
			var dataMap map[string]interface{}
			if err := json.Unmarshal(jsonData, &dataMap); err != nil {
				errorChan <- err
				return
			}

			fmt.Printf("Data processed through JSON: %v\n", dataMap)
			resultChan <- data

		case err := <-errorChan:
			fmt.Println("Error in processing:", err)
			return
		case <-time.After(2 * time.Second):
			fmt.Println("Processing timed out")
			return
		}
	}()

	// Wait for result or error
	select {
	case data := <-resultChan:
		fmt.Println("Data encrypted successfully:", data.Encrypted)

		// Generate a secure key from the sensitive data
		key := sha256.Sum256([]byte(sensitiveData))

		// Decrypt the data to verify encryption worked
		decryptedData, err := decryptData(data.Encrypted, key[:])
		if err != nil {
			fmt.Println("Decryption error:", err)
			return
		}

		fmt.Println("Data decrypted successfully, matches original:", decryptedData == sensitiveData)

		// Use sanitized data for query
		sanitizedData := sanitizeSQL(sensitiveData)
		executeQuery("SELECT * FROM users WHERE password='" + sanitizedData + "'")

	case err := <-errorChan:
		fmt.Println("Error:", err)
		return
	case <-time.After(3 * time.Second):
		fmt.Println("Operation timed out")
		return
	}
}

// Complex cryptographic operations using multiple standard libraries
func performComplexCryptoOperations(input string) {
	// Convert input to bytes
	inputBytes := []byte(input)

	// Generate elliptic curve key pair
	curve := elliptic.P256()
	privateKey := new(big.Int).SetBytes(inputBytes[:8])
	x, y := curve.ScalarBaseMult(privateKey.Bytes())

	fmt.Printf("Elliptic curve public key: (%s, %s)\n", x.String(), y.String())

	// Sort the input bytes to make analysis more complex
	sortedBytes := make([]byte, len(inputBytes))
	copy(sortedBytes, inputBytes)
	sort.Slice(sortedBytes, func(i, j int) bool {
		return sortedBytes[i] < sortedBytes[j]
	})

	// Create a regexp pattern from the sorted bytes
	pattern := fmt.Sprintf("[%s]", regexp.QuoteMeta(string(sortedBytes[:5])))
	re := regexp.MustCompile(pattern)
	matches := re.FindAllString(input, -1)
	fmt.Printf("Regexp matches: %v\n", matches)

	// Use URL parsing
	u, err := url.Parse("https://example.com/path?q=" + url.QueryEscape(input))
	if err == nil {
		fmt.Printf("URL path: %s, query: %s\n", u.Path, u.Query().Get("q"))
	}

	// Use filepath operations
	cleanPath := filepath.Clean("./tmp/" + hex.EncodeToString(inputBytes[:4]))
	ext := filepath.Ext(cleanPath)
	fmt.Printf("Clean filepath: %s, extension: %s\n", cleanPath, ext)

	// Use compression
	compressBuf := bytes.NewBuffer(nil)
	gzWriter := gzip.NewWriter(compressBuf)
	gzWriter.Write(inputBytes)
	gzWriter.Close()

	// Calculate compression ratio
	ratio := float64(compressBuf.Len()) / float64(len(inputBytes)) * 100
	fmt.Printf("Compressed size: %d (%.2f%% of original)\n", compressBuf.Len(), ratio)

	// Use binary encoding
	encodeBuf := bytes.NewBuffer(nil)
	binary.Write(encodeBuf, binary.BigEndian, int64(len(inputBytes)))
	binary.Write(encodeBuf, binary.LittleEndian, inputBytes)
	fmt.Printf("Binary encoded data length: %d\n", encodeBuf.Len())

	// Use HMAC with multiple algorithms
	hmacKey := inputBytes[:16]
	h := hmac.New(sha256.New, hmacKey)
	h.Write(inputBytes)
	mac := h.Sum(nil)
	fmt.Printf("HMAC-SHA256: %x\n", mac)
}

// Perform complex cryptographic operations with multiple algorithms
func performMultipleHashingOperations(data []byte) {
	// Use multiple hash algorithms
	md5Hash := md5.Sum(data)
	sha1Hash := sha1.Sum(data)
	sha256Hash := sha256.Sum256(data)
	sha512Hash := sha512.Sum512(data)

	fmt.Printf("MD5: %x\n", md5Hash)
	fmt.Printf("SHA1: %x\n", sha1Hash)
	fmt.Printf("SHA256: %x\n", sha256Hash)
	fmt.Printf("SHA512: %x\n", sha512Hash)

	// Use CRC checksums
	crc32Table := crc32.MakeTable(crc32.IEEE)
	crc32Value := crc32.Checksum(data, crc32Table)

	crc64Table := crc64.MakeTable(crc64.ISO)
	crc64Value := crc64.Checksum(data, crc64Table)

	adler32Value := adler32.Checksum(data)

	fmt.Printf("CRC32: %x\n", crc32Value)
	fmt.Printf("CRC64: %x\n", crc64Value)
	fmt.Printf("Adler32: %x\n", adler32Value)

	// Use RSA operations
	privateKey, _ := rsa.GenerateKey(rand.Reader, 2048)
	publicKey := &privateKey.PublicKey

	// Use DSA operations
	dsaParams := new(dsa.Parameters)
	dsa.GenerateParameters(dsaParams, rand.Reader, dsa.L1024N160)

	dsaPrivateKey := new(dsa.PrivateKey)
	dsaPrivateKey.Parameters = *dsaParams
	dsa.GenerateKey(dsaPrivateKey, rand.Reader)

	// Use ECDSA operations
	ecdsaPrivateKey, _ := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	_ = ecdsaPrivateKey.PublicKey

	// Use Ed25519
	_, _, _ = ed25519.GenerateKey(rand.Reader)

	// Use X.509 and ASN.1
	template := x509.Certificate{
		SerialNumber: big.NewInt(1),
		Subject: pkix.Name{
			CommonName: "example.com",
		},
		NotBefore: time.Now(),
		NotAfter:  time.Now().Add(time.Hour * 24 * 180),
		KeyUsage:  x509.KeyUsageKeyEncipherment | x509.KeyUsageDigitalSignature,
	}

	derBytes, _ := x509.CreateCertificate(rand.Reader, &template, &template, publicKey, privateKey)

	// PEM encoding
	pemBlock := &pem.Block{
		Type:  "CERTIFICATE",
		Bytes: derBytes,
	}
	pemData := pem.EncodeToMemory(pemBlock)

	fmt.Printf("Certificate: %s\n", pemData)

	// Base32 encoding
	base32Str := base32.StdEncoding.EncodeToString(data)
	fmt.Printf("Base32: %s\n", base32Str)
}

func main() {
	// Call the new function with the clear tainted dataflow
	newFunction()

	// Demonstrate secure random bytes generation
	secureBytes, err := generateSecureBytes(32)
	if err != nil {
		fmt.Println("Error generating secure bytes:", err)
		return
	}
	fmt.Printf("Generated secure random bytes: %x\n", secureBytes)

	// Perform complex cryptographic operations
	sensitiveData := getUserInput("Enter data for complex crypto operations:")
	performComplexCryptoOperations(sensitiveData)

	// Perform multiple hashing operations
	performMultipleHashingOperations([]byte(sensitiveData))
}