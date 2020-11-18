/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0
 */

package main

import (
	utility "aws-lc-verification/proof/common"
	"log"
	"os"
	"sync"
)

func main() {
	log.Printf("Started HMAC check.")
	// When 'HMAC_SELECTCHECK' is undefined, quickcheck is executed.
	env_var := os.Getenv("HMAC_SELECTCHECK")
	if len(env_var) == 0 {
		utility.RunSawScript("verify-HMAC-SHA384-quickcheck.saw")
		return
	}

	// When 'HMAC_SELECTCHECK' is defined, run 'HMAC-Init-ex' with diff parameters concurrently.
	var wg sync.WaitGroup
	count := 0
	for num := 0; num <= 129; num++ {
		wg.Add(1)
		saw_template := "verify-HMAC-Init-ex-selectcheck-template.txt"
		placeholder_name := "HMAC_TARGET_KEY_LEN_PLACEHOLDER"
		go utility.CreateAndRunSawScript(saw_template, placeholder_name, num, &wg)
		utility.Wait(&count, utility.HMAC_PROCESS_LIMIT, &wg)
		count++
	}
	wg.Wait()

	// When 'HMAC_SELECTCHECK' is defined, run 'HMAC-Final' with diff parameters concurrently.
	count = 0
	for num := 0; num <= 127; num++ {
		wg.Add(1)
		saw_template := "verify-HMAC-Final-selectcheck-template.txt"
		placeholder_name := "HMAC_TARGET_NUM_PLACEHOLDER"
		go utility.CreateAndRunSawScript(saw_template, placeholder_name, num, &wg)
		utility.Wait(&count, utility.HMAC_PROCESS_LIMIT, &wg)
		count++
	}

	wg.Wait()
	log.Printf("Completed HMAC check.")
}
