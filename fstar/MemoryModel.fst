module MemoryModel

module U16 = FStar.UInt16
module U8 = FStar.UInt8
module Map = FStar.Map
module P = FStar.Preorder


// type pointer = x:U16.t{U16.lt 0us x}

noeq type state_t = {
     bytemap: Map.t U16.t U8.t;
  }

noeq type config = {
     r0: P.preorder state_t;
     r1: P.preorder state_t;
  }

let state_prop = state_t -> prop

// pre-condition for write the value `v` at the index `k`
let write_pre0 (c:config) (k:U16.t) (v:U8.t) (p0:state_prop) : prop =
  forall s. p0 s ==> c.r0 s {bytemap = Map.upd s.bytemap k v}

let write_post0 (c:config) (k:U16.t) (v:U8.t) (p0:state_prop) (y:state_t) : prop = 
  exists x. p0 x /\ c.r1 {bytemap = Map.upd x.bytemap k v} y


let read_post0 (c:config) (k:U16.t) (p0:state_prop) (v:U8.t) (y:state_t) : prop =
  exists x. p0 x /\ Map.sel x.bytemap k == v /\ c.r1 x y

let read_post0' (c:config) (k:U16.t) (p0:state_prop) (v:U8.t) : prop =
  exists s. p0 s /\ Map.sel s.bytemap k == v

new_effect NONDET_STATE = STATE_h state_prop

unfold let lift_div_state (a:Type) (wp:pure_wp a) (p:a -> state_prop -> Type0) (h:state_prop) =
  wp (fun a -> p a h)

sub_effect DIV ~> NONDET_STATE = lift_div_state

effect ST (a:Type) (c:config)
  (pre:state_prop -> Type0)
  (post: (h:state_prop -> a -> _:state_prop{pre h} -> Type0)) =
  NONDET_STATE a (fun (p:(a -> state_prop -> Type0)) (h:state_prop) ->
    pre h /\ (forall a h1. post h a h1 ==> p a h1))

effect St (a:Type) (c:config) = ST a c (fun h -> True) (fun h0 r h1 -> True)

assume val read0 (#c:config) (k:U16.t) :
  ST U8.t c
    (fun p0 -> True)
    (fun p0 v p1 -> read_post0' c k p0 v /\ p1 == read_post0 c k p0 v)

assume val write0 (#c:config) (k:U16.t) (v:U8.t) :
  ST unit c
    (write_pre0 c k v)
    (fun p0 _ p1 -> p1 == write_post0 c k v p0)


assume val cas0 (#c:config) (key:U16.t) (old_v new_v:U8.t) :
  ST (option U8.t) c
    (fun p0 -> True)
    (fun p0 r p1 ->
      (None? r ==>
        write_pre0 c key new_v (fun s -> p0 s /\ Map.sel s.bytemap key == old_v) /\
        p1 == write_post0 c key new_v (fun s -> p0 s /\ Map.sel s.bytemap key == old_v)
      ) /\ (Some? r ==> (r <> Some old_v /\
        p1 == read_post0 c key p0 (match r with | Some x -> x) /\
        read_post0' c key p0 (match r with | Some x -> x)
      ))
    )

let c0 = {
    r0 = (fun s1 s2 -> s1 == s2 \/
      ((
        Map.sel s1.bytemap 0us == 0uy \/
        Map.sel s1.bytemap 0us == 1uy
      ) /\ (
        Map.sel s2.bytemap 0us == 0uy \/
        Map.sel s2.bytemap 0us == 1uy
      )
    ));
    r1 = (fun s1 s2 -> s1 == s2 \/ (
      (
        Map.sel s1.bytemap 0us == 0uy \/
        Map.sel s1.bytemap 0us == 2uy
      ) /\ (
        Map.sel s1.bytemap 0us == 0uy \/
        Map.sel s2.bytemap 0us == 2uy
      )
    ))
  }

let c1 = {
    r1 = c0.r0;
    r0 = c0.r1
  }

#push-options "--z3rlimit 50"
let prog0 (_:unit) :
  St unit c0 =
  match cas0 #c0 0us 0uy 1uy with
  | Some v -> ()
  | None ->
    write0 #c0 1us 42uy;
    write0 #c0 2us 43uy;
    write0 #c0 0us 0uy
