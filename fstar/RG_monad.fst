module RG_monad

open FStar.Monotonic.Pure
module Map = FStar.Map
module U = Utils

let rg_pre (state:Type0) = state -> Type0
let rg_post (a:Type) (state:Type0) (pre:rg_pre state) = 
  s0:state -> a -> state -> Type0
// I try to use s0:state -> a -> _:state{pre s0} -> Type0 but it's slow

let rg_repr (a:Type) (state:Type0) (rely guarantee:U.preorder state)
  (pre:rg_pre state) (post:rg_post a state pre) =
  s0:state ->
    Div (a & state) (pre s0) (fun out -> post s0 out._1 out._2) //  /\ U.closure (fun x y -> rely x y \/ guarantee x y) s0 out._2)

unfold let rg_return_pre (state:Type0) :
  rg_pre state = fun _ -> True

unfold let rg_return_post (a:Type) (x:a) (state:Type0) :
  rg_post a state (rg_return_pre state) 
  = fun s0 y s1 -> s0 == s1 /\ x == y

let rg_return (a:Type) (x:a) (state:Type0)
  (rely guarantee:U.preorder state)
  : rg_repr a state rely guarantee
    (rg_return_pre state) (rg_return_post a x state)
  = fun s0 -> (x, s0)


unfold let rg_bind_pre (a b:Type) (state:Type0)
  (rely:U.preorder state)
  (pre_f:rg_pre state)
  (post_f:rg_post a state pre_f)
  (pre_g:a -> rg_pre state)
  : rg_pre state
  = fun s0 -> pre_f s0 /\ (forall x s1 s2. post_f s0 x s1 /\ rely s1 s2 ==> pre_g x s2)

unfold let rg_bind_post (a b:Type) (state:Type0)
  (rely:U.preorder state)
  (pre_f:rg_pre state)
  (post_f:rg_post a state pre_f)
  (pre_g:a -> rg_pre state)
  (post_g:(x:a) -> rg_post b state (pre_g x))
  : rg_post b state (rg_bind_pre a b state rely pre_f post_f pre_g)
  = fun s0 y s3 -> exists x s1 s2. post_f s0 x s1 /\ rely s1 s2 /\ post_g x s2 y s3

let rg_bind (a b:Type) (state:Type0)
  (rely guarantee:U.preorder state)
  (pre_f:rg_pre state)
  (post_f:rg_post a state pre_f)
  (pre_g:a -> rg_pre state)
  (post_g:(x:a) -> rg_post b state (pre_g x))
  (f:rg_repr a state rely guarantee pre_f post_f)
  (g: (x:a) -> rg_repr b state rely guarantee (pre_g x) (post_g x))
  : rg_repr b state rely guarantee 
    (rg_bind_pre a b state rely pre_f post_f pre_g)
    (rg_bind_post a b state rely pre_f post_f pre_g post_g)
  = fun s0 -> let x, s1 = f s0 in g x s1


let rg_subcomp (a:Type) (state:Type0)
  (rely guarantee:U.preorder state)
  (pre pre':rg_pre state)
  (post:rg_post a state pre)
  (post':rg_post a state pre')
  (f:rg_repr a state rely guarantee pre post)
  : Pure (rg_repr a state rely guarantee pre' post')
    ((forall s0. pre' s0 ==> pre s0) /\ (forall s0 x s1. pre s0 /\ post s0 x s1 ==> post' s0 x s1))
    (fun _ -> True)
  = f


unfold let rg_ite_pre (a:Type) (state:Type0)
  (pre pre':rg_pre state)
  (b:bool)
  : rg_pre state
  = fun s0 -> (b ==> pre s0) /\ ((~b) ==> pre' s0)

unfold let rg_ite_post (a:Type) (state:Type0)
  (pre pre':rg_pre state)
  (post:rg_post a state pre)
  (post':rg_post a state pre')
  (b:bool)
  : rg_post a state (rg_ite_pre a state pre pre' b)
  = fun s0 x s1 -> (b ==> post s0 x s1) /\ ((~b) ==> post' s0 x s1)

let rg_ite (a:Type) (state:Type0)
  (rely guarantee:U.preorder state)
  (pre pre':rg_pre state)
  (post :rg_post a state pre)
  (post':rg_post a state pre')
  (_:rg_repr a state rely guarantee pre post)
  (_:rg_repr a state rely guarantee pre' post')
  (b:bool): Type =
  rg_repr a state rely guarantee
    (rg_ite_pre a state pre pre' b)
    (rg_ite_post a state pre pre' post post' b)

[@@ primitive_extraction]
// reifiable
reflectable
effect {
  Rg (a:Type) 
  ([@@@effect_param]state:Type0)
  ([@@@effect_param]rely:U.preorder state)
  ([@@@effect_param]guarantee:U.preorder state)
  (pre:rg_pre state)
  (_:rg_post a state pre)
  with
  {
    repr = rg_repr;
    return = rg_return;
    bind = rg_bind;
    subcomp = rg_subcomp;
    if_then_else = rg_ite
  }
}

unfold let lift_div_pre (a:Type) (state:Type0)
  (wp:pure_wp a) : rg_pre state =
  elim_pure_wp_monotonicity_forall ();
  fun _ -> wp (fun _ -> True)

unfold let lift_div_post (a:Type) (state:Type0)
  (wp:pure_wp a) : rg_post a state (lift_div_pre a state wp)
  = elim_pure_wp_monotonicity_forall ();
  fun s0 x s1 -> wp (fun _ -> True) /\ ~(wp (fun y -> x =!= y \/ s0 =!= s1))

assume val lift_div (a:Type) (state:Type0) (rely guarantee:U.preorder state)
  (wp:pure_wp a) (f:eqtype_as_type unit -> DIV a wp) :
  rg_repr a state rely guarantee
    (lift_div_pre a state wp)
    (lift_div_post a state wp)
(*  
  = elim_pure_wp_monotonicity wp;
  fun s0 -> 
    let x = f () in 
    x, s0
*)
sub_effect DIV ~> Rg = lift_div

module U8 = FStar.UInt8
module U16 = FStar.UInt16

type state: Type0 = Map.t U16.t U8.t

noextract
let rely : U.preorder state =
  fun s1 s2 -> s1 == s2 \/ ((
    Map.sel s1 0us == 0uy \/
    Map.sel s1 0us == 2uy
  ) /\ (
    Map.sel s2 0us == 0uy \/
    Map.sel s2 0us == 2uy
  ))

noextract
let guarantee : U.preorder state =
  fun s1 s2 -> s1 == s2 \/ ((
    Map.sel s1 0us == 0uy \/
    Map.sel s1 0us == 1uy
  ) /\ (
    Map.sel s2 0us == 0uy \/
    Map.sel s2 0us == 1uy
  ))
