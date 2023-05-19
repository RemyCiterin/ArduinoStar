module RG_atomic

open RG_monad

module U16 = FStar.UInt16
module U8 = FStar.UInt8

//

//[@@ noextract_to "krml"]
assume val read (k:U16.t) :
  Rg U8.t state rely guarantee (fun _ -> True) (fun s0 v s1 -> s0 == s1 /\ Map.sel s0 k == v)
//  = Rg?.reflect (fun s0 -> Map.sel s0 k, s0)

//[@@ noextract_to "krml"]
assume val write (k:U16.t) (v:U8.t) :
  Rg unit state rely guarantee 
    (fun s0 ->
      guarantee s0 (Map.upd s0 k v)
    ) (fun s0 _ s1 ->
      s1 == Map.upd s0 k v
    )
//  = Rg?.reflect (fun s0 -> ((), Map.upd s0 k v))

//[@@ noextract_to "krml"]
assume val cas (k:U16.t) (old_v:U8.t) (new_v:U8.t) :
  Rg (option U8.t) state rely guarantee
    (fun s0 -> Map.sel s0 k == old_v ==> guarantee s0 (Map.upd s0 k new_v))
    (fun s0 out s1 -> 
      match out with
      | None -> 
         Map.sel s0 k == old_v /\ 
        s1 == Map.upd s0 k new_v
      | Some x -> 
        Map.sel s0 k == x /\ 
        x <> old_v /\ 
        s0 == s1
    )
(*
  = Rg?.reflect (
    fun s0 -> 
      if Map.sel s0 k = old_v then
        (None, Map.upd s0 k new_v)
      else
        (Some (Map.sel s0 k), s0)
  )
*)
