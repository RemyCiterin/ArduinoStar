module Monotonic.ST

module P = FStar.Preorder
module W = FStar.Monotonic.Witnessed
open FStar.Monotonic.Pure

let st_pre (state:Type0) = state -> Type0
let st_post (a:Type) (state:Type0) = a -> state -> Type0
let st_wp' (a:Type) (state:Type0) = st_post a state -> st_pre state

let st_wp_monotonic (#a:Type) (#state:Type0) (rel:P.preorder state)
  (w:st_wp' a state) =
  forall p q.
    (forall r s. p r s ==> q r s) ==>
    (forall s. w p s ==> w q s)

let st_wp (a:Type) (state:Type0) (rel:P.preorder state) =
  w:st_wp' a state{st_wp_monotonic rel w}

type repr (a:Type) (state:Type0) (rel:P.preorder state) (wp:st_wp a state rel) =
  s0:state -> PURE (a & state)
  (as_pure_wp (fun p -> wp (fun x s1 -> s0 `rel` s1 ==> p (x, s1)) s0))

let return (a:Type) (x:a) (state:Type0) (rel:P.preorder state) :
  repr a state rel (fun p s0 -> p x s0) =
  fun s0 -> (x, s0)

let bind (a b:Type) (state:Type0)
  (rel:P.preorder state)
  (wp_f:st_wp a state rel)
  (wp_g:a -> st_wp b state rel)
  (f:repr a state rel wp_f)
  (g:(x:a) -> repr b state rel (wp_g x))
  : repr b state rel
    (fun p -> wp_f (fun x -> wp_g x p))
  = fun s0 -> let (x, s1) = f s0 in g x s1

let subcomp (a:Type) (state:Type0)
  (rel:P.preorder state)
  (wp wp':st_wp a state rel)
  (f:repr a state rel wp) :
  Pure (repr a state rel wp')
    (requires forall p s. wp' p s ==> wp p s)
    (ensures fun _ -> True)
  = f

let if_then_else
  (a:Type)
  (state:Type0)
  (rel:P.preorder state)
  (wp wp':st_wp a state rel)
  (f:repr a state rel wp)
  (g:repr a state rel wp')
  (b:bool) : Type =
  repr a state rel (fun post s0 ->
    (b ==> wp post s0) /\
    ((~b) ==> wp' post s0)
  )

// definition of monotonic state effect
reifiable reflectable
effect {
  MSTATE
    (a:Type)
    ([@@@effect_param] state:Type0)
    ([@@@effect_param] rel:P.preorder state)
    (_:st_wp a state rel)
  with {repr; return; bind; subcomp; if_then_else}
}

let lift_pure_wp (#a:Type) (#state:Type0)
  (rel:P.preorder state) (wp:pure_wp a) : st_wp a state rel =
  elim_pure_wp_monotonicity wp;
  fun p s0 -> wp (fun x -> p x s0)

let lift_pure (a:Type) (state:Type0)
  (rel:P.preorder state) (wp:pure_wp a) (f:unit -> PURE a wp) :
  repr a state rel (lift_pure_wp rel wp) =
  elim_pure_wp_monotonicity_forall ();
  fun s0 -> (f (), s0)



effect
  MST
    (a:Type)
    (state:Type0)
    (rel:P.preorder state)
    (pre:state -> Type0)
    (post:(s0:state -> a -> _:state{pre s0} -> Type0)) =
    MSTATE a state rel (
      fun p s0 -> pre s0 /\ (forall x s1. post s0 x s1 ==> p x s1)
    )

effect Mst (a:Type) (state:Type0) (rel:P.preorder state) = MST a state rel (fun _ -> True) (fun _ _ _ -> True)

