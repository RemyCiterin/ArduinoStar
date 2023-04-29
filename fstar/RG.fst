module RG

open FStar.Monotonic.Pure
module Map = FStar.Map
module U = Utils

(*
let rg_pre (state:Type0) = state -> Type0
let rg_post (a:Type) (state:Type0) = a -> state -> Type0
let rg_wp' (a:Type) (state:Type0) = rg_post a state -> rg_pre state

let rg_wp_monotonic (#a:Type) (#state:Type0) (wp:rg_wp' a state) : Type0 =
  forall s0 p1 p2. (forall x s1. p1 x s1 ==> p2 x s1) ==> wp p1 s0 ==> wp p2 s0

type rg_wp (a:Type) (state:Type0) = w:(rg_wp' a state){rg_wp_monotonic w}

type rg_repr (a:Type) (state:Type0) (rely guarantee:U.preorder state)
  (wp:rg_wp a state) =
  s0:state -> DIV (a & state) (as_pure_wp (fun p -> wp (fun x s1 -> p (x, s1)) s0))

//inline_for_extraction
let rg_return (a:Type) (x:a) (state:Type0)
  (rely guarantee:U.preorder state)
  : rg_repr a state rely guarantee
    (fun p s0 -> p x s0)
  = fun s0 -> (x, s0)


//inline_for_extraction
let rg_bind (a b:Type) (state:Type0)
  (rely guarantee:U.preorder state)

  (wp_f:rg_wp a state)
  (wp_g:a -> rg_wp b state)

  (f:rg_repr a state rely guarantee wp_f)
  (g:(x:a) -> rg_repr b state rely guarantee (wp_g x))

  : rg_repr b state rely guarantee
    (fun p s0 -> wp_f (fun y s1 -> wp_g y p s1) s0)
    //(fun p s0 -> wp_f (fun y s1 -> forall s2. rely s1 s2 /\ wp_g y p s2) s0)
  = fun s0 -> let (x, s1) = f s0 in g x s1


let rg_subcomp (a:Type) (state:Type0)
  (rely guarantee:U.preorder state)
  (wp wp':rg_wp a state)
  (f:rg_repr a state rely guarantee wp)
  : Pure (rg_repr a state rely guarantee wp')
    (requires forall p s. wp' p s ==> wp p s)
    (ensures fun _ -> True)
  = f

let rg_if_then_else (a:Type) (state:Type0)
  (rely guarantee:U.preorder state)
  (wp wp':rg_wp a state)
  (f:rg_repr a state rely guarantee wp)
  (g:rg_repr a state rely guarantee wp')
  (b:bool) : Type =
  rg_repr a state rely guarantee (
    fun post s0 ->
      (b ==> wp post s0) /\
      ((~b) ==> wp' post s0)
  )

reifiable
reflectable
effect {
  RG (a:Type) 
  ([@@@effect_param] state:Type0)
  ([@@@effect_param] rely:U.preorder state)
  ([@@@effect_param] guarantee:U.preorder state)
  (_:rg_wp a state)
  with {
    repr= rg_repr; return=rg_return; bind=rg_bind;
    subcomp = rg_subcomp; if_then_else=rg_if_then_else
  }
}

let lift_div_wp a state (wp:pure_wp a) : rg_wp a state =
  elim_pure_wp_monotonicity_forall ();
  fun p s0 -> wp (fun x -> p x s0)

let lift_div a state rely guarantee
  (wp:pure_wp a) (f:unit -> DIV a wp) :
  rg_repr a state rely guarantee (lift_div_wp a state wp) =
  elim_pure_wp_monotonicity_forall ();
  fun s0 -> (f (), s0)

sub_effect DIV ~> RG = lift_div

let rg_wp_to_hoare (a:Type) (state:Type0) (pre:state -> Type0) 
  (post:(s0:state -> a -> _:state{pre s0} -> Type0)) : rg_wp a state =
  fun p s0 -> pre s0 /\ (forall x s1. post s0 x s1 ==> p x s1)

effect Rg (a:Type) (state:Type0) (rely guarantee:U.preorder state)
  (pre:state -> Type0) (post:(s0:state -> a -> _:state{pre s0} -> Type0)) =
  RG a state rely guarantee (rg_wp_to_hoare a state pre post)
*)

let rg_pre (state:Type0) = state -> Type0
let rg_post (a:Type) (state:Type0) = state -> a -> state -> Type0

let rg_repr (a:Type) (state:Type0) (rely guarantee:U.preorder state)
  (pre:rg_pre state) (post:rg_post a state) =
  s0:state ->
    Div (a & state) (pre s0) (fun out -> post s0 out._1 out._2)

let rg_return (a:Type) (x:a) (state:Type0)
  (rely guarantee:U.preorder state)
  : rg_repr a state rely guarantee
    (fun _ -> True) (fun s0 y s1 -> s0 == s1 /\ x == y)
  = fun s0 -> (x, s0)

assume val rg_bind (a b:Type) (state:Type0)
  (rely guarantee:U.preorder state)

  (pre_f:rg_pre state)
  (post_f:rg_post a state)

  (pre_g:a -> rg_pre state)
  (post_g:a -> rg_post b state)

  (f:rg_repr a state rely guarantee pre_f post_f)
  (g: (x:a) -> rg_repr b state rely guarantee (pre_g x) (post_g x))

  : rg_repr b state rely guarantee 
    (fun s0 -> pre_f s0 /\ (forall x s1 s2. post_f s0 x s1 /\ rely s1 s2 ==> pre_g x s2))
    (fun s0 y s3 -> exists x s1 s2. post_f s0 x s1 /\ rely s1 s2 /\ post_g x s2 y s3)
//  = fun s0 -> let x, s1 = f s0 in g x s1

let rg_subcomp (a:Type) (state:Type0)
  (rely guarantee:U.preorder state)
  (pre pre':rg_pre state)
  (post post':rg_post a state)
  (f:rg_repr a state rely guarantee pre post)
  : Pure (rg_repr a state rely guarantee pre' post')
    ((forall s0. pre' s0 ==> pre s0) /\ (forall s0 x s1. post s0 x s1 ==> post' s0 x s1))
    (fun _ -> True)
  = f

let rg_ite (a:Type) (state:Type0)
  (rely guarantee:U.preorder state)
  (pre pre':rg_pre state)
  (post post':rg_post a state)
  (_:rg_repr a state rely guarantee pre post)
  (_:rg_repr a state rely guarantee pre' post')
  (b:bool): Type =
  rg_repr a state rely guarantee
    (fun s0 -> (b ==> pre s0) /\ ((~b) ==> pre' s0))
    (fun s0 x s1 -> (b ==> post s0 x s1) /\ ((~b) ==> post' s0 x s1))

reifiable
reflectable
effect {
  Rg (a:Type) 
  ([@@@effect_param]state:Type0)
  ([@@@effect_param]rely:U.preorder state)
  ([@@@effect_param]guarantee:U.preorder state)
  (_:rg_pre state)
  (_:rg_post a state)
  with
  {
    repr = rg_repr;
    return = rg_return;
    bind = rg_bind;
    subcomp = rg_subcomp;
    if_then_else = rg_ite
  }
}

let lift_div (a:Type) (state:Type0) (rely guarantee:U.preorder state)
  (wp:pure_wp a) (f:unit -> DIV a wp) :
  rg_repr a state rely guarantee
    (fun s0 -> wp (fun _ -> True))
    (fun s0 x s1 -> s0 == s1 /\ ~(wp (fun y -> s0 =!= s1)))
  = elim_pure_wp_monotonicity_forall ();
  fun s0 -> (f (), s0)

sub_effect DIV ~> Rg = lift_div

module U8 = FStar.UInt8
module U16 = FStar.UInt16
type state: Type0 = Map.t U16.t U8.t

let rely : U.preorder state =
  fun s1 s2 -> s1 == s2 \/ ((
    Map.sel s1 0us == 0uy \/
    Map.sel s1 0us == 2uy
  ) /\ (
    Map.sel s2 0us == 0uy \/
    Map.sel s2 0us == 2uy
  ))

let guarantee : U.preorder state =
  fun s1 s2 -> s1 == s2 \/ ((
    Map.sel s1 0us == 0uy \/
    Map.sel s1 0us == 1uy
  ) /\ (
    Map.sel s2 0us == 0uy \/
    Map.sel s2 0us == 1uy
  ))

assume val read (k:U16.t) :
  Rg U8.t state rely guarantee (fun _ -> True) (fun s0 v s1 -> s0 == s1 /\ Map.sel s0 k == v)

assume val write (k:U16.t) (v:U8.t) :
  Rg unit state rely guarantee 
    (fun s0 ->
      guarantee s0 (Map.upd s0 k v)
    ) (fun s0 _ s1 ->
      s1 == Map.upd s0 k v
    )

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

let check_cond (cond:state -> Type0) :
  Rg unit state rely guarantee cond (fun s0 _ s1 -> s0 == s1) =
  ()


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
    write 0us 0uy

let unsafe_prog (_:unit) :
  Rg unit state rely guarantee (fun _ -> True) (fun _ _ _ -> True) =
  let value = read 0us in
  if value = 0uy then begin
    check_cond (fun s0 -> Map.sel s0 0us == 0uy);
    write 0us 1uy
  end else ()

