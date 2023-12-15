#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

MEMFILE=$1
echo $MEMFILE
while true; do
    # (echo '' ; date '+TIME:%H:%M:%S' ; ps aux | grep 'saw\|z3\|yices') 2>&1 | tee -a $MEMFILE
    # sleep 2
    (echo '' ; date '+TIME:%H:%M:%S' ; ps aux ) 2>&1 | tee -a $MEMFILE
    sleep 10
done
