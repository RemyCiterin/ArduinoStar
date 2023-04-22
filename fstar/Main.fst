module Main

open Monotonic.ST

type test_type = | X0 | X1

let square (x: UInt32.t): UInt32.t =
  let open FStar.UInt32 in
  x *%^ x

