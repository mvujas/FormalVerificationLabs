#!/bin/sh
# stainless --watch --timeout=5 Lab02.scala
stainless --watch --timeout=5 --functions=search --strict-arithmetic=false Lab02.scala
# stainless --watch --timeout=5 --functions=search --strict-arithmetic=true Lab02.scala