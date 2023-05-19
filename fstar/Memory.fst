(*
this file define a small memory model of arduino with a system of users and permissions
*)
module Memory

open Utils
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module Map = FStar.Map
module Seq = FStar.Seq
module List = FStar.List.Tot
module UInt = FStar.UInt
open FStar.Ghost

unfold let timer_number = 20

type memory_user =
  | CPU // CPU can read and write memory
  | Main // main thread, can be interrupted by a timer
  | Timer of fin timer_number

type memory_owner =
  | Owned of memory_user
  | Shared of list memory_user

let byte = U8.t

// memory is a finite list of block
// each block contain a finite list of byte an a memory owner of thses bytes
// a user can write to a byte if they own it
// heap memory block are define at compile time
// stack memory block are define at runtime
type block = {
  alive: bool;
  block_size:U16.t;
  owner: memory_user;
  bytes: s:Seq.seq byte {Seq.length s == U16.v block_size}
}

type memory = Seq.seq block
  
[@@must_erase_for_extraction]
let block_id (size:U16.t) = erased nat

assume HasEq_bock_id : (size:U16.t) -> hasEq (block_id size)

let has_block (#size:U16.t) (m:memory) (ref:block_id size) : GTot bool =
  let ref = reveal ref in
  ref < Seq.length m && (Seq.index m (reveal ref)).alive && (Seq.index m (reveal ref)).block_size = size

let get_block (#size:U16.t) (m:memory) (ref:block_id size{has_block m ref}) 
  : GTot (b:block{b.block_size == size})  = 
  let ref = reveal ref in
  Seq.index m (reveal ref)

let get_block_opt (#size:U16.t) (m:memory) (ref:block_id size) : GTot (option block) = 
  if has_block m ref then Some (get_block m ref) else None

noeq type buffer : Type0 =
  | Null
  | Buffer:
    block_size:U16.t ->
    content:block_id block_size ->
    idx:U16.t ->
    length:erased U16.t{UInt.size (U16.v idx + U16.v (reveal length)) 16} ->
    buffer

