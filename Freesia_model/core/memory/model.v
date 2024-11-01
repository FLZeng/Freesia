Require Import List Arith.

Inductive MemoryObject := 
  | MemInt (n : nat)
  | MemBool (b : bool)
  | MemPointer (p : Pointer)
with Pointer := mkPointer (x : MemoryObject).

Definition getObjectFromPointer(p : Pointer) : MemoryObject :=
  match p with
  | mkPointer x => x
  end.

Compute getObjectFromPointer (mkPointer (MemInt (0))).

Record MemoryBlock := mkBlock {
  object : MemoryObject;
  length : nat;
}.

Record AccessPointer := mkAccPtr {
  acctag : nat;
  ptr : nat;
}.

Record MemoryItem := mkItem {
  block : MemoryBlock;
  addr : nat;
  memtag : nat;
}.

Definition MemoryArray := list MemoryItem.

Axiom distinctAddr :
  forall (m : MemoryArray) (i j : MemoryItem),
    (In i m) /\ (In j m)
    -> i.(addr) <> j.(addr).

Fixpoint getObject (m : MemoryArray) (p : AccessPointer) : option MemoryObject :=
  match m with
  | nil => None
  | i::n => if i.(memtag) =? p.(acctag) then
            (if i.(addr) =? p.(ptr) then Some(i.(block).(object)) else None)
          else None
  end.



