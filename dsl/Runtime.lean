import Mathlib.Data.Nat.Basic

abbrev Time := Nat

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
