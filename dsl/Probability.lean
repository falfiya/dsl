import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init


structure ProbabilitySpace where
  Ω : Time -> Type
  P : (t: Time) -> Finset (Ω t) -> Rat
  universalOne : ∀ t, P t Finset.univ = 1

inductive CointossOutcome where
  | heads
  | tails
deriving DecidableEq

def DecidableSet (t: Type) := t -> Bool

def CointossProbability (event: DecidableSet CointossOutcome) : Rat :=
  if (∀ c, event c) then 1
  else if (∀ c, ¬event c) then 0
  else 0.5

def Cointoss (t: Time): ProbabilitySpace := {
  Ω t' := if t = t' then CointossOutcome else Empty
  P t' event :=
    if t != t' then 0
    else if event = {Coinside.heads} then 0.5
    else if event = {Coinside.tails} then 0.5
    else 1
}
