module Effect


open FStar.Preorder
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module P = FStar.Preorder

module W = FStar.Monotonic.Witnessed
open FStar.Monotonic.Pure

// concurrent ST monad definition with a type for configuration
let cst_pre (state:Type0) = (state -> Type0) -> Type0
let cst_post (state:Type0) (a:Type) = (state -> Type0) -> a -> state -> Type0

type repr (a:Type) (state:Type0) (pre:cst_pre state) (post:cst_post state a) =
  (p:(state -> Type0) {pre p}) -> 
    //Pure (a & (state -> state)) (requires pre c p) (ensures fun out ->
    //  forall s. p s ==> post c p out._1 (out._2 s)
    //)
    out:(a & (s:state{p s} -> state)){forall s. p s ==> post p out._1 (out._2 s)}

inline_for_extraction
let return (a:Type) (x:a) (state:Type0) :
  repr a state (fun _ -> True) (fun p out s -> p s /\ x == out) =
  fun p -> (x, (fun (s:state{p s}) -> s))

let bind (a b:Type) (state:Type0)
  (pre_f:cst_pre state)
  (post_f:cst_post state a)
  (pre_g:a -> cst_pre state)
  (post_g:a -> cst_post state b)
  (f:repr a state pre_f post_f)
  (g:(x:a) -> repr b state (pre_g x) (post_g x))
  : repr b state
    (fun p -> pre_f p /\ (forall x. pre_g x (post_f p x)))
    (fun p x s -> exists y. post_g y (post_f p y) x s)
  = fun p ->
  let (x, f1) = f p in
  let (y, f2) = g x (post_f p x) in
  (y, (fun s -> f2 (f1 s)))

let ite_pre (#state:Type) (pre pre':cst_pre state) (b:bool)
  : cst_pre state = fun p ->
  (b ==> pre p) /\ ((~b) ==> pre' p)

let ite_post (#a:Type) (#state:Type) (post post':cst_post state a) (b:bool)
  : cst_post state a = fun p out s ->
  (b ==> post p out s) /\ ((~b) ==> post' p out s)

let if_then_else
  (a:Type) (state:Type0)
  (pre:cst_pre state)
  (post:cst_post state a)
  (pre':cst_pre state)
  (post':cst_post state a)
  (f:repr a state pre  post )
  (g:repr a state pre' post') (b:bool)
  = repr a state (ite_pre pre pre' b) (ite_post post post' b)

unfold let stronger
  (#a:Type) (#state:Type0)
  (pre pre':cst_pre state)
  (post post':cst_post state a)
  : Type0 =
  (forall p. pre' p ==> pre p) /\
  (forall p out s. pre p /\ post p out s ==> post' p out s)

let subcomp (a:Type) (state:Type0)
  (pre pre': cst_pre state)
  (post post': cst_post state a)
  (f:repr a state pre post)
  // : repr u#uu a config state pre post
  : Pure (repr a state pre' post')
    (requires stronger pre pre' post post')
    (ensures fun _ -> True)
  = f


total reifiable
reflectable
effect {
  ST (a:Type) 
    ([@@@ effect_param] state:Type0)
    (_:cst_pre state)
    (_:cst_post state a)
  with {repr; return; bind; subcomp; if_then_else}
}

let lift_pure (a:Type) (state:Type0) (wp:pure_wp a) (f:unit -> PURE a wp) :
  repr a state (fun _ -> wp (fun _ -> True)) (fun p r s -> p s /\ ~(wp (fun x -> x =!= r)))
  = elim_pure_wp_monotonicity_forall ();
  fun _ -> (f (), (fun s -> s))

sub_effect PURE ~> ST = lift_pure

noeq type state_t : Type0 = {
     bytemap: Map.t U16.t U8.t;
  }

noeq type config : Type = {
     r0: P.preorder state_t;
     r1: P.preorder state_t;
  }

let state_prop = state_t -> Type0

// pre-condition for write the value `v` at the index `k`
let write_pre0 (c:config) (k:U16.t) (v:U8.t) (p0:state_prop) : prop =
  forall s. p0 s ==> c.r0 s {bytemap = Map.upd s.bytemap k v}

let write_post0 (c:config) (k:U16.t) (v:U8.t) (p0:state_prop) (y:state_t) : prop = 
  exists x. p0 x /\ c.r1 {bytemap = Map.upd x.bytemap k v} y


let read_post0 (c:config) (k:U16.t) (p0:state_prop) (v:U8.t) (y:state_t) : prop =
  exists x. p0 x /\ Map.sel x.bytemap k == v /\ c.r1 x y

let read_post0' (c:config) (k:U16.t) (p0:state_prop) (v:U8.t) : prop =
  exists s. p0 s /\ Map.sel s.bytemap k == v


assume val read0 (#c:config) (k:U16.t) :
  ST U8.t state_t
    (fun p0 -> True)
    (fun p0 v s -> read_post0 c k p0 v s)

assume val write0 (#c:config) (k:U16.t) (v:U8.t) :
  ST unit state_t
    (write_pre0 c k v)
    (fun p0 _ s -> write_post0 c k v p0 s)


assume val cas0 (c:config) (key:U16.t) (old_v new_v:U8.t) :
  ST (option U8.t) state_t
    (fun p0 -> True)
    (fun p0 r s ->
      (None? r ==>
        write_pre0 c key new_v (fun s -> p0 s /\ Map.sel s.bytemap key == old_v) /\
        write_post0 c key new_v (fun s -> p0 s /\ Map.sel s.bytemap key == old_v) s
      ) /\ (Some? r ==> (r <> Some old_v /\
        read_post0 c key p0 (match r with | Some x -> x) s// /\
        //read_post0' c key p0 (match r with | Some x -> x)
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
  ST unit state_t (fun _ -> True) (fun _ _ _ -> True) =
  match cas0 c0 0us 0uy 1uy with
  | Some v -> ()
  | None ->
    write0 #c0 1us 42uy;
    write0 #c0 2us 43uy;
    write0 #c0 0us 0uy
