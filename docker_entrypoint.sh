#!/bin/sh -ex

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

(pushd SAW; ./scripts/entrypoint_check.sh; popd)
(pushd Coq; make; popd)
