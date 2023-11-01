#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


set -ex

export BINUTILS_TARGET_PREFIX=aarch64-linux-gnu

mkdir -p build/llvm/crypto build/aarch64/crypto
cp build_src/llvm/crypto/crypto_test build/llvm/crypto/crypto_test
cp build_src/aarch64/crypto/crypto_test build/aarch64/crypto/crypto_test
extract-bc build/llvm/crypto/crypto_test
