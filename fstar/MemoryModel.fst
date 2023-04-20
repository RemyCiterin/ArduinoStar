module MemoryModel

module U16 = FStar.UInt16
module U8 = FStar.UInt8
module Map = FStar.Map
module P = FStar.Preorder


// type pointer = x:U16.t{U16.lt 0us x}

noeq type state_t = {
     bytemap: Map.t U16.t U8.t;
  }



assume val r0: P.preorder state_t
assume val r1: P.preorder state_t

let state_prop = state_t -> prop

// pre-condition for write the value `v` at the index `k`
let write_pre0 (k:U16.t) (v:U8.t) (p0:state_prop) : prop =
  forall s. p0 s ==> r0 s {bytemap = Map.upd s.bytemap k v}

let write_post0 (k:U16.t) (v:U8.t) (p0:state_prop) (p1:state_prop) : prop =
  forall y. p1 y <==> (exists x.
    p0 x /\ r1 {bytemap = Map.upd x.bytemap k v} y
  )

let read_post0 (k:U16.t) (p0:state_prop) (v:U8.t) (p1:state_prop) : prop =
  let p (s:state_t) =
    p0 s /\ Map.sel s.bytemap k == v
  in (exists s. p s) /\ (forall y. p1 y <==> (
    exists x. p x /\ r1 x y
  ))

new_effect NONDET_STATE = STATE_h state_prop

unfold let lift_div_state (a:Type) (wp:pure_wp a) (p:a -> state_prop -> Type0) (h:state_prop) =
  wp (fun a -> p a h)

sub_effect DIV ~> NONDET_STATE = lift_div_state

effect ST (a:Type)
  (pre:state_prop -> Type0)
  (post: (h:state_prop -> a -> _:state_prop{pre h} -> Type0)) =
  NONDET_STATE a (fun (p:(a -> state_prop -> Type0)) (h:state_prop) ->
    pre h /\ (forall a h1. post h a h1 ==> p a h1))

effect St (a:Type) = ST a (fun h -> True) (fun h0 r h1 -> True)

assume val read0 (k:U16.t) :
  ST U8.t
    (fun p0 -> True)
    (read_post0 k)

assume val write0 (k:U16.t) (v:U8.t) :
  ST unit
    (write_pre0 k v)
    (fun p0 _ -> write_post0 k v p0)


assume val cas0 (key:U16.t) (old_v new_v:U8.t) :
  ST (option U8.t)
    (fun p0 -> True)
    (fun p0 r p1 ->
      (None? r ==>
        write_pre0 key new_v (fun s -> p0 s /\ Map.sel s.bytemap key == old_v) /\
        write_post0 key new_v (fun s -> p0 s /\ Map.sel s.bytemap key == old_v) p1
      ) /\ (Some? r ==> (r <> Some old_v /\
        read_post0 key p0 (match r with | Some x -> x) p1
      ))
    )
