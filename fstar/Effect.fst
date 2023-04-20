module Effect


open FStar.Preorder

module W = FStar.Monotonic.Witnessed
open FStar.Monotonic.Pure

// concurrent ST monad definition with a type for configuration
let cst_pre (config state:Type0) = config -> (state -> Type0) -> Type0
let cst_post (config state:Type0) (a:Type) = config -> (state -> Type0) -> a -> state -> Type0

(*
let cst_wp' (config state:Type0) (a:Type) = config -> (a -> state -> Type0) -> (state -> Type0) -> Type0

unfold let cst_wp_monotonic (config state:Type0) (a:Type) (wp:cst_wp' config state a) =
  forall (c:config) (p q: (a -> state -> Type0)).
    (forall x s. p x s ==> q x s) ==>
    (forall m. wp c p m ==> wp c q m)

type cst_wp config state a = wp:cst_wp' config state a{cst_wp_monotonic config state a wp}


type repr (config state:Type0) (a:Type) (wp:cst_wp config state a) =
  c:config -> p0:(state -> Type0) ->
  PURE (a & state -> state) (fun p -> cst_wp c (fun x s -> p ) p0)
*)

type repr (a:Type) (config state:Type0) (pre:cst_pre config state) (post:cst_post config state a) =
  (c:config) -> (p:(state -> Type0)) -> // {pre c p}) -> 
    Pure (a & (state -> state)) (requires pre c p) (ensures fun out ->
      forall s. p s ==> post c p out._1 (out._2 s)
    )
    // out:(a & (state -> state)){forall s. p s ==> post c p out._1 (out._2 s)}

let return (a:Type) (config state:Type0) (x:a) :
  repr a config state (fun _ _ -> True) (fun _ p out s -> p s /\ x == out) =
  fun c p -> (x, (fun s -> s))

let bind (a b:Type) (config state:Type0)
  (pre_f:cst_pre config state)
  (post_f:cst_post config state a)
  (pre_g:a -> cst_pre config state)
  (post_g:a -> cst_post config state b)
  (f:repr a config state pre_f post_f)
  (g:(x:a) -> repr b config state (pre_g x) (post_g x))
  : repr b config state
    (fun c p -> pre_f c p /\ (forall x. pre_g x c (post_f c p x)))
    (fun c p x s -> exists y. post_g y c (post_f c p y) x s)
  = fun c p ->
  let (x, f1) = f c p in
  let (y, f2) = g x c (post_f c p x) in
  (y, (fun s -> f2 (f1 s)))

#push-options "--query_stats"

total reifiable reflectable
effect {
  TEST (a:Type) (config state:Type0) (_:cst_pre config state) (_:cst_post config state a)
  with {repr; return; bind}
}
