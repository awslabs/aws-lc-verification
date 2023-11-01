#!/bin/sh -ex

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

cd NSym
./scripts/build_aarch64.sh "Release" "neoverse-n1"
