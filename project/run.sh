# stainless --solvers=smt-z3 --watch --vc-cache=false --timeout=10 src/*.scala
# stainless --solvers=smt-z3 --watch --vc-cache=false --functions=partitionSmallerEmpty,partitionEmpty,partition src/*.scala
# stainless --solvers=smt-z3 --watch --vc-cache=false --functions=partitionSmallerSmaller src/*.scala
# stainless --solvers=smt-z3 --watch --vc-cache=false --functions=partition src/*.scala
stainless --solvers=smt-z3 --watch --vc-cache=false --functions=delMin src/*.scala
# stainless --solvers=smt-z3 --watch --vc-cache=false --functions=getMinTreeElTrivialCase,getMinTreeElRecursiveStep,getMinTreeEl src/*.scala
# stainless --solvers=smt-z3 --vc-cache=false src/*.scala
# stainless --solvers=smt-z3 --watch --vc-cache=false --timeout=10 src/Ordering.scala src/Math.scala src/StainlessUtils.scala
