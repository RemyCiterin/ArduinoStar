module Code

open RG_monad
open RG_atomic
module U8 = FStar.UInt8
module U16 = FStar.UInt16

let check_pre (test:state -> Type0) :
  Rg unit state rely guarantee test (fun s0 _ s1 -> s0 == s1)
  = ()


let prog (_:unit) :
  Rg unit state rely guarantee (fun _ -> True) (fun _ _ _ -> True) =
  match cas 0us 0uy 1uy with
  | Some v -> ()
  | None ->
    write 1us 42uy;
    write 2us 43uy;
    write 3us 44uy;
    write 4us 55uy;
    write 5us 6uy;
    write 6us 6uy;
    write 8us 6uy;
    write 7us 6uy;
    write 9us 6uy;
    write 2us 6uy;
    write 1us 6uy;
    check_pre (fun s -> Map.sel s 0us == 1uy);
    write 0us 0uy
