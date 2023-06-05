#!/bin/bash -ex

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

(pushd Coq; make; popd)
(pushd SAW; ./scripts/install.sh; ./scripts/entrypoint_check.sh; popd)
