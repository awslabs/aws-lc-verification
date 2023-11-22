#!/bin/sh

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

set -ex

PATH=/lc/bin:/go/bin:$PATH
PATCH=$(realpath ./patch)

apply_patch() {
  PATCH_NAME=$1

  (cd ../src; patch -p1 -r - --forward < "$PATCH"/"$PATCH_NAME".patch || true)
}

go env -w GOPROXY=direct

# First, apply some patches (TODO: remove them)...

apply_patch "rsa-encrypt"
apply_patch "nomuxrsp"
apply_patch "ec_GFp_nistp384_point_mul_public"
apply_patch "noinline-aes_gcm_from_cipher_ctx"
apply_patch "noinline-bn_mod_add_words"
apply_patch "noinline-bn_reduce_once_in_place"
apply_patch "noinline-bn_sub_words"
apply_patch "noinline-bn_is_bit_set_words"
apply_patch "noinline-ec_scalar_is_zero"
apply_patch "noinline-ec_point_mul_scalar"
apply_patch "noinline-ec_point_mul_scalar_base"
apply_patch "noinline-ec_get_x_coordinate_as_bytes"
apply_patch "noinline-ec_get_x_coordinate_as_scalar"
apply_patch "noinline-ec_compute_wNAF"
apply_patch "noinline-value_barrier_w"
apply_patch "noinline-value_barrier_u32"
apply_patch "noinline-GetInPlaceMethods"
apply_patch "noinline-fiat_p384_sub"
apply_patch "noinline-p384_get_bit"
apply_patch "noinline-constant_time_is_zero_w"
apply_patch "noinline-p384_felem_cmovznz"
apply_patch "noinline-p384_select_point"
apply_patch "noinline-p384_select_point_affine"
apply_patch "noinline-p384_felem_copy"
apply_patch "noinline-HMAC_Update"
apply_patch "noinline-HMAC_Final"
apply_patch "noinline-HKDF_extract"
apply_patch "noinline-HKDF_expand"
apply_patch "noinline-SHA384_Final"
apply_patch "noinline-SHA384_Update"
apply_patch "noinline-EVP_DigestSignUpdate"
apply_patch "noinline-EVP_DigestVerifyUpdate"

# The following warning seems like a bug in wllvm and are benign
# WARNING:Did not recognize the compiler flag "--target=aarch64-unknown-linux-gnu"
# WARNING:Did not recognize the compiler flag "-mcpu=neoverse-n1"
./scripts/aarch64/build_llvm.sh "Release" "neoverse-n1"
./scripts/aarch64/post_build.sh
