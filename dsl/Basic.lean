def hello := "Hello"

def tuple (n: Nat) : Type :=
  match n with
  | 0 => Unit
  | 1 => Nat
  | .succ n => Nat × tuple n

structure Process where
  id : Nat
  isCorrect : Bool

structure Message where
  id : Nat

abbrev Time := Nat

structure Delivery where
  frm : Process
  to : Process
  message : Message

structure EventualDelivery where
  frm : Process
  to : Process
  message : Message

  delivery : Time -> Option Deliver
  
  eventually : ∃t, (delivery t) = some (Delivery.mk frm to message)


structure PerfectLink where
  self : Process

def Send (p: PerfectLink) (to: Process) (m: Message) : EventualDelivery := EventualDelivery.mk p.self to m sorry sorry

def pl1 := PerfectLink.mk ⟨1, true⟩
def p2 : Process := ⟨2, true⟩
def r := Send pl1 p2 ⟨1⟩
def q := r.to
