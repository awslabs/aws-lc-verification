# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0


FROM ubuntu:20.04
RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections
RUN apt-get update
RUN apt-get install -y wget unzip git cmake clang llvm golang python3-pip libncurses5 quilt
RUN pip3 install wllvm
   
ADD ./SAW/scripts /lc/scripts
RUN /lc/scripts/install.sh

# When running in GitHub, the entire repo is available, so these adds are not necessary.
# The adds below allow the container to be run outside of GitHub.
ADD ./SAW /SAW
ADD ./src /src
ADD ./cryptol-specs /cryptol-specs

ENTRYPOINT ["./SAW/scripts/docker_entrypoint.sh"]
