import Mathlib.Data.Nat.Basic

import Mathlib.Data.Stream.Init

structure FiniteStream (α : Type) where
   underlaying : Stream' α
   start : Nat
   length : Nat

def FiniteStream.toList {α : Type} (fs : FiniteStream α) : List α :=
   (List.range fs.length).map fun n => fs.underlaying (fs.start + n)

def Stream'.slice (start length : Nat) (s : Stream' α) : FiniteStream α :=
   ⟨s, start, length⟩

abbrev Time := Nat
def Time.Stream : Type := Stream' Time
def Time.all : Stream := fun n => n

instance Time.inhabited : Inhabited Time := Inhabited.mk 0
instance Time.Stream.inhabited : Inhabited Time.Stream := Inhabited.mk Time.all

def Time.Stream.add (s : Stream) (offset : Time) : Stream' {t : Time // t ≥ offset}
   := fun n => ⟨offset + s n, Nat.le_add_right offset (s n)⟩

abbrev NoProof := False -> Prop
instance NoProof.inhabited : Inhabited NoProof := Inhabited.mk (
   by
   intro f
   contradiction
)

structure Process where
   id : Nat
   isCorrect : Bool
   aliveAt : Time -> Bool
   staysDead : ∀t, aliveAt t = false -> aliveAt (t + 1) = false
   pCorrct : isCorrect = true -> ∀t, aliveAt t = true

namespace Synchronous


end Synchronous

structure Synchronous where
   Ps : List Process

structure ProcessGroup where
