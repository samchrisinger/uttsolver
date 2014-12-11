#!/bin/bash

rm ./src/coq/*.vo

cd ./src/coq
coqc ./types.v
coqc ./game.v
coqc ./players.v
coqc ./play.v
coqc ./build.v
coqc -byte build

mv *.hs ../../src/hs/




