module Main

open LowStar.BufferOps

module B = LowStar.Buffer
module HS = FStar.HyperStack
module G = FStar.Ghost
module L = FStar.List.Tot
module U32 = FStar.UInt32
module MO = LowStar.Modifies

open FStar.HyperStack.ST

#set-options "--__no_positivity"

noeq type t (a:Type0) =
  B.pointer_or_null (cell a)

and cell (a: Type0) = {
  next: t a;
  data: a
}

let rec well_formed #a (h:HS.mem) (c:t a) (l:G.erased (list a)) :
  GTot Type0 (decreases (G.reveal l))
  = B.live h c /\ (
  match G.reveal l with
  | [] -> B.g_is_null c
  | a :: q ->
    B.length c == 1 /\ (
      let {data = data; next = next} = B.get h c 0 in
      a == data /\ well_formed h next (G.hide q)
    )
  )

let rec length_functional #a (h:HS.mem) (c:t a) (l1 l2:G.erased (list a)) :
  Lemma
    (requires well_formed h c l1 /\ well_formed h c l2)
    (ensures l1 == l2)
    (decreases G.reveal l1)
    [SMTPat (well_formed h c l1); SMTPat (well_formed h c l2)] =
  if B.g_is_null c then ()
  else
    let {next = next} = B.get h c 0 in
    length_functional h next (G.hide (L.tl (G.reveal l1))) (G.hide (L.tl (G.reveal l2)))

#set-options "--max_ifuel 1 --max_fuel 2"
val footprint: (#a: Type) -> (h: HS.mem) -> (l: t a) -> (n: G.erased (list a)) -> Ghost MO.loc
  (requires (well_formed h l n))
  (ensures (fun refs -> True))
  (decreases (G.reveal n))

let rec footprint #a h l n =
  if B.g_is_null l
  then MO.loc_none
  else
    let {next = next} = B.get h l 0 in
    let refs = footprint h next (G.hide (L.tl (G.reveal n))) in
    MO.loc_union (MO.loc_buffer l) refs
#reset-options

let rec modifies_disjoint_footprint
  (#a: Type)
  (h: HS.mem)
  (l: t a)
  (n: G.erased (list a))
  (r: MO.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    well_formed h l n /\
    MO.loc_disjoint r (footprint h l n) /\
    MO.modifies r h h'
  ))
  (ensures (
    well_formed h' l n /\
    footprint h' l n == footprint h l n
  ))
  (decreases (G.reveal n))
= if B.g_is_null l
  then ()
  else begin
    let {next = l'} = B.get h l 0 in
    modifies_disjoint_footprint h l' (G.hide (L.tl (G.reveal n))) r h'
  end

let rec well_formed_distinct_lengths_disjoint
  #a
  (c1: B.pointer (cell a))
  (c2: B.pointer (cell a))
  (n1: G.erased (list a))
  (n2: G.erased (list a))
  (h: HS.mem)
: Lemma
  (requires (
    well_formed h c1 n1 /\
    well_formed h c2 n2 /\
    L.length (G.reveal n1) <> L.length (G.reveal n2)
  ))
  (ensures (
    B.disjoint c1 c2
  ))
  (decreases (L.length (G.reveal n1) + L.length (G.reveal n2)))
= let {next = next1} = B.get h c1 0 in
  let {next = next2} = B.get h c2 0 in
  let f () : Lemma (next1 =!= next2) =
    if B.g_is_null next1 || B.g_is_null next2
    then ()
    else
      well_formed_distinct_lengths_disjoint next1 next2 (G.hide (L.tl (G.reveal n1))) (G.hide (L.tl (G.reveal n2))) h
  in
  f ();
  B.pointer_distinct_sel_disjoint c1 c2 h

let rec well_formed_gt_lengths_disjoint_from_list
  #a
  (h: HS.mem)
  (c1: B.pointer_or_null (cell a))
  (c2: B.pointer_or_null (cell a))
  (n1: G.erased (list a))
  (n2: G.erased (list a))
: Lemma
  (requires (well_formed h c1 n1 /\ well_formed h c2 n2 /\ L.length (G.reveal n1) > L.length (G.reveal n2)))
  (ensures (MO.loc_disjoint (MO.loc_buffer c1) (footprint h c2 n2)))
  (decreases (G.reveal n2))
= match G.reveal n2 with
  | [] -> ()
  | _ ->
    well_formed_distinct_lengths_disjoint c1 c2 n1 n2 h;
    well_formed_gt_lengths_disjoint_from_list h c1 (B.get h c2 0).next n1 (G.hide (L.tl (G.reveal n2)))

let well_formed_head_tail_disjoint
  (#a: Type)
  (h: HS.mem)
  (c: B.pointer (cell a))
  (n: G.erased (list a))
: Lemma
  (requires (well_formed h c n))
  (ensures (
    MO.loc_disjoint (MO.loc_buffer c) (footprint h (B.get h c 0).next (G.hide (L.tl (G.reveal n))))
  ))
= well_formed_gt_lengths_disjoint_from_list h c (B.get h c 0).next n (G.hide (L.tl (G.reveal n)))

let rec unused_in_well_formed_disjoint_from_list
  #a #b
  (h: HS.mem)
  (r: B.buffer a)
  (l: B.pointer_or_null (cell b))
  (n: G.erased (list b))
: Lemma
  (requires (r `B.unused_in` h /\ well_formed h l n))
  (ensures (MO.loc_disjoint (MO.loc_buffer r) (footprint h l n)))
  (decreases (G.reveal n))
= match G.reveal n with
  | [] -> ()
  | _ -> unused_in_well_formed_disjoint_from_list h r (B.get h l 0).next (G.hide (L.tl (G.reveal n)))



val pop: (#a: Type) -> (#n: G.erased (list a)) -> (pl: B.pointer (t a)) ->
  Stack a
  (requires (fun h ->
    let l = B.get h pl 0 in
    B.live h pl /\
    well_formed h l n /\
    MO.loc_disjoint (MO.loc_buffer pl) (footprint h l n) /\
    Cons? (G.reveal n)
  ))
  (ensures (fun h0 v h1 ->
    let l = B.get h1 pl 0 in
    let n' = G.hide (L.tl (G.reveal n)) in
    B.live h1 pl /\
    MO.modifies (MO.loc_buffer pl) h0 h1 /\
    well_formed h1 l n' /\
    MO.loc_disjoint (MO.loc_buffer pl) (footprint h1 l n')
  ))

let pop #a #n pl =
  let l = !* pl in
  let lcell = !* l in
  let h0 = get () in
  pl *= lcell.next;
  let h1 = get () in
  well_formed_head_tail_disjoint h0 l n;
  modifies_disjoint_footprint h0 l n (MO.loc_buffer pl) h1;
  lcell.data

val push: (#a: Type) -> (#n: G.erased (list a)) -> (pl: B.pointer (t a)) -> (x: a) ->
  ST unit
    (requires (fun h ->
      let l = B.get h pl 0 in
      B.live h pl /\
      well_formed h l n /\
      MO.loc_disjoint (MO.loc_buffer pl) (footprint h l n)
    ))
    (ensures (fun h0 _ h1 ->
      let n' = G.hide (x :: G.reveal n) in
      let l = B.get h1 pl 0 in
      MO.modifies (MO.loc_buffer pl) h0 h1 /\
      B.live h1 pl /\
      well_formed h1 l n' /\
      MO.loc_disjoint (MO.loc_buffer pl) (footprint h1 l n')
    ))

let push #a #n pl x =
  let h0 = get () in
  let l = !* pl in
  let c = {
    data = x;
    next = l;
  }
  in
  let pc: B.pointer (cell a) = B.malloc HS.root c 1ul in
  unused_in_well_formed_disjoint_from_list h0 pc l n;
  let h1 = get () in
  modifies_disjoint_footprint h0 l n (MO.loc_buffer pc) h1;
  pl *= pc;
  let h2 = get () in
  modifies_disjoint_footprint h1 l n (MO.loc_buffer pl) h2


val length (#a: Type) (gn: G.erased (list a)) (l: t a): Stack UInt32.t
  (requires (fun h -> well_formed h l gn))
  (ensures (fun h0 n h1 ->
    h0 == h1 /\
    U32.v n = L.length (G.reveal gn)
  ))

let rec length #a gn l =
  if B.is_null l
  then 0ul
  else
    let open U32 in
    let c = !* l in
    let next = c.next in
    let n = length (G.hide (L.tail (G.reveal gn))) next in
    if n = 0xfffffffful then begin
      C.String.(print !$"Integer overflow while computing length");
      C.exit 255l;
      0ul // dummy return value, this point is unreachable
    end else
      n +^ 1ul

val main: unit -> ST (Int32.t) (fun _ -> true) (fun _ _ _ -> true)

let main () =
  let l: B.pointer_or_null (t Int32.t) = B.malloc HS.root B.null 1ul in
  push #Int32.t #(G.hide []) l 1l;
  push #Int32.t #(G.hide [1l]) l 0l;
  let r = pop #Int32.t #(G.hide [0l; 1l]) l in
  TestLib.checku32 (length (G.hide [1l]) !*l) 1ul;
  r

