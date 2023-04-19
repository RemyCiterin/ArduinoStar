module Main


let square (x: UInt32.t): UInt32.t =
  let open FStar.UInt32 in
  x *%^ x
