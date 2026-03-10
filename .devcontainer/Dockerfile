# FROM mcr.microsoft.com/devcontainers/universal:2
FROM mcr.microsoft.com/devcontainers/base:ubuntu

# https://tex.stackexchange.com/questions/245982/differences-between-texlive-packages-in-linux
RUN apt-get update && apt-get install -y \
    texlive \
    texlive-latex-extra \
    texlive-extra-utils \
    latexmk \
    ripgrep

USER vscode
ENV ELAN_HOME="/home/vscode/.elan"
ENV PATH="${ELAN_HOME}/bin:${PATH}"
RUN sh -c 'curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y'
RUN elan self update
RUN elan default leanprover/lean4:stable
RUN lean --version
