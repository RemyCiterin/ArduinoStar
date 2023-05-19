module Utils

module RT = FStar.ReflexiveTransitiveClosure

let fin (n:nat) = x:nat{x < n}

let get_some #a (x: (option a){Some? x})=
    match x with
    | Some _x -> _x

let relation (a:Type) = a -> a -> Type0
let predicate (a:Type) = a -> Type0


let stable (#a:Type) (p:predicate a) (r:relation a) : Type0 =
  forall x y. p x /\ r x y ==> p y

let reflexive (#a:Type) (r:relation a) : Type0 =
  forall x. r x x

let transitive (#a:Type) (r:relation a) : Type0 =
  forall x y z. r x y /\ r y z ==> r x z

let preorder (a:Type u#u) : Type u#(max 1 u) =
  r:relation a{reflexive r /\ transitive r}


val closure (#a:Type) (r:a -> a -> Type0) : preorder a
let closure #a r x y =RT.closure r x y

let closure_step (#a:Type) (r:a -> a -> Type0) (x y:a) :
  Lemma
    (requires r x y)
    (ensures closure r x y)
    [SMTPat (closure r x y)]
  = ()

let closure_inversion (#a:Type) (r:a -> a -> Type0) (x y:a) :
  Lemma 
    (requires closure r x y)
    (ensures x == y \/ (exists z. r x z /\ closure r z y))
  = RT.closure_inversion r x y

let stable_on_closure (#a:Type) (r:a -> a -> Type0) (p:a -> prop) :
  Lemma
    (requires forall x y.{:pattern (p y); (r x y)} p x /\ r x y ==> p y)
    (ensures forall x y.{:pattern (closure r x y)} p x /\ closure r x y ==> p y)
  = RT.stable_on_closure r p ()

let p_union (#a:Type) (l r:preorder a) : preorder a =
  closure (fun x y -> l x y \/ r x y)

let p_union_left (#a:Type) (l r:preorder a) (x y z:a) :
  Lemma (requires l x y /\ p_union l r y z)
    (ensures p_union l r x z)
    [SMTPat (p_union l r x z); SMTPat (l x y)]
  = assert(p_union l r x y)

let p_union_right (#a:Type) (l r:preorder a) (x y z: a) :
  Lemma (requires r x y /\ p_union l r y z)
    (ensures p_union l r x z)
    [SMTPat (p_union l r x z); SMTPat (r x y)]
  = assert(p_union l r x y)

