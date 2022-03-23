/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0
 */

package main

import (
	utility "aws-lc-verification/proof/common"
	"log"
	"math"
	"os"
	"sync"
)

// The HMAC  proofs use approximately 7 gb of memory each, round up to 8 gb for headroom
const memory_used_per_test uint64 = 8e9

func main() {
	log.Printf("Started HMAC check.")
	// When 'HMAC_SELECTCHECK' is undefined, quickcheck is executed.
	env_var := os.Getenv("HMAC_SELECTCHECK")
	if len(env_var) == 0 {
		utility.RunSawScript("verify-HMAC-SHA384-quickcheck.saw")
		return
	}
	// When 'HMAC_SELECTCHECK' is defined, selectcheck is executed.
	var wg sync.WaitGroup
	process_count := 0

	total_memory := utility.SystemMemory()
	num_parallel_process := int(math.Floor((float64(total_memory) / float64(memory_used_per_test))))
	log.Printf("System has %d bytes of memory, running %d jobs in parallel", total_memory, num_parallel_process)
	// Below code splits the range [0, 127] to multiple smaller intervals for parallel.
	start_indx := 0
	sha_cblock := 128
	range_len := sha_cblock / num_parallel_process
	if range_len <= 0 {
		range_len = 1
	}
	for start_indx < sha_cblock {
		wg.Add(1)
		end_indx := start_indx + range_len
		if end_indx > sha_cblock {
			end_indx = sha_cblock - 1
		}
		saw_template := "verify-HMAC-SHA384-selectcheck-template.txt"
		placeholder_map := map[string]int{
			"RANGE_START_INDX_PLACEHOLDER": start_indx,
			"RANGE_END_INDX_PLACEHOLDER":   end_indx,
		}
		go utility.CreateAndRunSawScript(saw_template, placeholder_map, &wg)
		utility.Wait(&process_count, num_parallel_process, &wg)
		start_indx += range_len
	}
	wg.Wait()

	log.Printf("Completed HMAC check.")
}
