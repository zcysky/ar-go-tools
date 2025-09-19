package main

import (
	"io"
	"log"
)

// Simple function that should have callees but might not show them in summary
func ServerCodec(conn io.ReadWriteCloser, h interface{}) interface{} {
	return newRPCCodec(conn, h)
}

func newRPCCodec(conn io.ReadWriteCloser, h interface{}) interface{} {
	log.Println("Creating RPC codec")
	return conn
}

func main() {
	ServerCodec(nil, nil)
}
