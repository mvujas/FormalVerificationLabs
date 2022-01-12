#!/bin/sh
stainless --solvers=smt-z3 --vc-cache=false --debug=verification src/*.scala
# stainless --solvers=smt-z3 --vc-cache=false --debug=verification src/*.scala > verification_results.out
