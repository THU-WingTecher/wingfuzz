#!/bin/bash

LLVM_CONFIG=llvm-config

clang++ -g -c $($LLVM_CONFIG --cxxflags) -fPIC LoadCmpTracer.cc
clang++ -shared $($LLVM_CONFIG --ldflags) LoadCmpTracer.o -o LoadCmpTracer.so
