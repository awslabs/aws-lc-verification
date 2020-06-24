FROM ubuntu:18.04
RUN apt-get update
RUN apt-get install -y wget unzip git cmake clang llvm golang python3-pip
RUN pip3 install wllvm

WORKDIR /lc
ADD ./scripts /lc/scripts

RUN ./scripts/install.sh

ENTRYPOINT ["./scripts/docker_entrypoint.sh"]