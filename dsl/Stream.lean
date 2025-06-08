import Mathlib.Data.Stream.Init

structure FiniteStream (α : Type) where
   underlaying : Stream' α
   start : Nat
   length : Nat

namespace FiniteStream

variable {α : Type}

def toList (fs : FiniteStream α) : List α :=
   (List.range fs.length).map fun n => fs.underlaying (fs.start + n)

-- Maybe something here later

end FiniteStream

namespace Stream'

def slice (start length : Nat) (s : Stream' α) : FiniteStream α :=
   ⟨s, start, length⟩

end Stream'
