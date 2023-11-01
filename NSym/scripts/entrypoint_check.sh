#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

./scripts/build_aarch64.sh "Release" "neoverse-n1"
./scripts/build_llvm.sh "Release"
./scripts/post_build.sh
