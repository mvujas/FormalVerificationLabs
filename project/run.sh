# stainless --solvers=smt-z3 --watch --vc-cache=false --timeout=10 src/*.scala
stainless --solvers=smt-z3 --watch --vc-cache=false --functions=insert src/*.scala
# stainless --solvers=smt-z3 --vc-cache=false src/*.scala
# stainless --solvers=smt-z3 --watch --vc-cache=false --timeout=10 src/Ordering.scala src/Math.scala src/StainlessUtils.scala
