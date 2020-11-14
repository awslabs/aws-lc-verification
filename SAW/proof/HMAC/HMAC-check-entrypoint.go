/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0
 */

package main

import (
	"fmt"
	"io/ioutil"
	"log"
	"os"
	"os/exec"
	"strconv"
	"strings"
)

// A utility function to terminate this program when err exists.
func checkError(e error) {
	if e != nil {
		log.Fatal(e)
	}
}

// A function to create and run "verify-HMAC-SHA384.saw".
func createAndRunSawScript(is_quickcheck_enabled bool) {
	log.Printf("Start creating saw script with quick_check=[%t].", is_quickcheck_enabled)
	// Create a new saw script for the target_num.
	file_name := fmt.Sprint("verify-SHA512-384.saw")
	file, err := os.Create(file_name)
	checkError(err)
	// Read file content of verification template.
	content, err := ioutil.ReadFile("verify-HMAC-SHA384-template.txt")
	checkError(err)
	verification_template := string(content)
	// Replace some placeholders of the file content with target values.
	text := strings.Replace(verification_template, "HMAC_QUICK_CEHCK_PLACEHOLDER", strconv.FormatBool(is_quickcheck_enabled), 1)
	defer file.Close()
	file.WriteString(text)
	defer os.Remove(file_name)
	// Run saw script.
	runSawScript(file_name)
}

// A function to run saw script.
func runSawScript(path_to_saw_file string) {
	log.Printf("Running saw script %s", path_to_saw_file)
	cmd := exec.Command("saw", path_to_saw_file)
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	err := cmd.Run()
	checkError(err)
}

func main() {
	log.Printf("Started HMAC check.")
	// When 'HMAC_SELECTCHECK' is undefined, quickcheck is executed.
	env_var := os.Getenv("HMAC_SELECTCHECK")
	is_quickcheck_enabled := len(env_var) == 0

	// Generate saw scripts based on above verification template and target num ranges.
	createAndRunSawScript(is_quickcheck_enabled)
	log.Printf("Completed HMAC check.")
}
