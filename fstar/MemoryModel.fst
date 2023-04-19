module MemoryModel

module U16 = FStar.UInt16
module U8 = FStar.UInt8

assume val real_world_t:Type0

assume val real_world_bind : real_world_t -> UInt8.t * real_world_t

noeq type state_t' = {
     bytemap: U16.t -> U8.t;
     real_world: real_world_t
  }

assume val well_formed_state_t : state_t' -> prop

let state_t = s:state_t'{well_formed_state_t s}

new_effect STATE = STATE_h state_t

unfold let lift_div_state (a:Type) (wp:pure_wp a) (p:a -> state_t -> Type0) (h:state_t) =
  wp (fun a -> p a h)

sub_effect DIV ~> STATE = lift_div_state

effect ST (a:Type)
  (pre:state_t -> Type0)
  (post: (h:state_t -> a -> _:state_t{pre h} -> Type0)) =
  STATE a (fun (p:(a -> state_t -> Type0)) (h:state_t) ->
    pre h /\ (forall a h1. post h a h1 ==> p a h1))

effect St (a:Type) = ST a (fun h -> True) (fun h0 r h1 -> True)

