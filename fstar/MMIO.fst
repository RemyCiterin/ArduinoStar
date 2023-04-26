module MMIO

/// definition of MMIO memory region
module M = FStar.Map
module U16 = FStar.UInt16
module U8 = FStar.UInt8
open Utils


// represent a mmio of n bits
let mmio' (n:nat) = M.t (fin n) bool

let sel' (#n:nat) (addr:mmio' n) (x:fin n) : bool
    = M.sel addr x

let upd' (#n:nat) (addr:mmio' n) (x:fin n) (b:bool) : mmio' n
  = M.upd addr x b

let sel_update_lemma' (#n:nat) (addr:mmio' n) (x y:fin n) (b:bool) :
  Lemma (sel' (upd' addr x b) y == (if x = y then b else sel' addr y))
  = ()
