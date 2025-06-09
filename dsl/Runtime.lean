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
structure Time.Stream where
   start : Time
   stream : Stream' {t : Time // t ≥ start}
   monotonic : ∀n, (stream n).val < (stream (n + 1)).val

def Time.all : Stream := {
   start := 0
   stream n := ⟨n, by simp⟩
   monotonic n := by simp
}

def Time.Stream.add (s : Stream) (offset : Time) : Stream := {
   start := offset + s.start
   stream n := let ⟨n', p_n'⟩ := s.stream n;
   ⟨
      offset + n',
      Nat.add_le_add_left p_n' offset
   ⟩
   monotonic n := by
      simp
      exact s.monotonic n
}

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
