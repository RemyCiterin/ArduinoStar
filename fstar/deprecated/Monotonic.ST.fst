module Monotonic.ST

module P = FStar.Preorder
module W = FStar.Monotonic.Witnessed
open FStar.Monotonic.Pure

let st_pre (state:Type0) = state -> Type0
let st_post (a:Type) (state:Type0) = a -> state -> Type0
let st_wp' (a:Type) (state:Type0) = st_post a state -> st_pre state

let st_wp_monotonic (#a:Type) (#state:Type0) (rel:P.preorder state)
  (w:st_wp' a state) =
  forall s p q.
    (forall r s. p r s ==> q r s) ==>
    w p s ==> w q s

let st_wp (a:Type) (state:Type0) (rel:P.preorder state) =
  w:st_wp' a state{st_wp_monotonic rel w}

type repr (a:Type) (state:Type0) (rel:P.preorder state) (wp:st_wp a state rel) =
  s0:state -> DIV (a & state)
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

let lift_div_wp (#a:Type) (#state:Type0)
  (rel:P.preorder state) (wp:pure_wp a) : st_wp a state rel =
  elim_pure_wp_monotonicity wp;
  fun p s0 -> wp (fun x -> p x s0)

let lift_div (a:Type) (state:Type0)
  (rel:P.preorder state) (wp:pure_wp a) (f:unit -> DIV a wp) :
  repr a state rel (lift_div_wp rel wp) =
  elim_pure_wp_monotonicity_forall ();
  fun s0 -> (f (), s0)

sub_effect DIV ~> MSTATE = lift_div

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

(* just to show that the following functino is not completly stupid *)
let lift_rel (a:Type) (state:Type0)
  (rel:P.preorder state)
  (rel':P.preorder state)
  (wp:st_wp a state rel)
  (f: repr a state rel' wp) :
  repr a state rel (fun post s0 -> (forall s1. rel' s0 s1 ==> rel s0 s1) /\ wp post s0) = f


assume val mstate_lift_rel (a:Type) (#state:Type)
  (rel rel':P.preorder state) (wp:st_wp a state rel')
  (f:unit -> MSTATE a state rel' wp) :
  MSTATE a state rel (fun post s0 -> 
    (forall s1. rel' s0 s1 ==> rel s0 s1) /\ wp post s0
  )


[@@"opaque_to_smt"]
let witnessed (#state:Type0) (rel:P.preorder state) (p:state -> Type0{P.stable p rel})
  = W.witnessed rel p

assume val witness (#state:Type0) (rel:P.preorder state)
  (p:state -> Type0) : MSTATE unit state rel
  (fun post s0 -> P.stable p rel /\ p s0 /\ (witnessed rel p ==> post () s0))

assume val recall (#state:Type0) (rel:P.preorder state)
  (p:state -> Type0) : MSTATE unit state rel
  (fun post s0 -> P.stable p rel /\ witnessed rel p /\ (p s0 ==> post () s0))

let witness_functoriality (#state:Type0) (rel:P.preorder state)
  (p:state -> Type0{P.stable p rel /\ witnessed rel p})
  (q:state -> Type0{P.stable q rel /\ (forall s. p s ==> q s)})
  : Lemma (ensures witnessed rel q) =
  reveal_opaque (`%witnessed) (witnessed rel);
  W.lemma_witnessed_weakening rel p q
