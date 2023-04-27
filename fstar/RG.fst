module RG

open FStar.Monotonic.Pure
module Map = FStar.Map
module U = Utils

let rg_pre (state:Type0) (rely:U.preorder state) =
  p:(state -> Type0){U.stable p rely}

let rg_post (a:Type) (state:Type0)
  (rely:U.preorder state) (pre:rg_pre state rely) =
  state -> a -> rg_pre state rely


type rg_repr (a:Type) (state:Type0) (rely guarantee:U.preorder state)
  (pre:rg_pre state rely) (post:rg_post a state rely pre) =
  s0:state -> Div (a & state)
    (requires pre s0)
    (ensures fun (x, s1) ->
      post s0 x s1
    )


let rg_return (a:Type) (state:Type0)
  (rely guarantee:U.preorder state) (x:a)
  : rg_repr a state rely guarantee
    (fun _ -> True) (fun s0 y s1 -> x == y /\ rely s0 s1)
  = fun s0 -> (x, s0)

let stabilize (a:Type) (p:U.predicate a) (r:U.preorder a) : 
  p':U.predicate a{U.stable p r} =
  admit()

let rg_bind (a b:Type) (state:Type0)
  (rely guarantee:U.preorder state)

  (pre_f: rg_pre state rely)
  (post_f:rg_post a state rely pre_f)

  (pre_g:a -> rg_pre state rely)
  (post_g:(x:a) -> rg_post b state rely (pre_g x))

  (f:rg_repr a state rely guarantee pre_f post_f)
  (g:(x:a) -> rg_repr b state rely guarantee (pre_g x) (post_g x))

  : rg_repr b state rely guarantee
    (fun s0 -> pre_f s0 /\ (forall x s1. post_f s0 x s1 ==> pre_g x s1))
    (fun s0 y s2 -> exists x s1. post_f s0 x s1 /\ post_g x s1 y s2)
  = fun s0 -> let (x, s1) = f s0 in g x s1
