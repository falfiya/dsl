import dsl.Runtime

namespace Synchronous

variable {𝓜 : Type}

structure FairLossLink.Deliver where
   src : Process
   dest : Process
   msg : 𝓜
   sentAt : Time

def FairLossLink.TryDeliver (pred : @Deliver 𝓜 -> Prop) : Type
   := Option {d // pred d}

structure FairLossLink.TryDeliverStream (pred : @Deliver 𝓜 -> Prop) where
   Td := TryDeliver pred
   stream : Stream' <| Td
   uniqueTimes :
      ∀ n, ¬∃ m, n != m ∧ 
      -> 

structure FairLossLink where
   send : {_ : Unit}
      -> (src : Process)
      -> (dest : Process)
      -> (msg : 𝓜)
      -> (sendAt : Time)
      -> FairLossLink.TryDeliver (· = ⟨src, dest, msg, sendAt⟩)
   selfSend : ∀ (p : Process) (msg : 𝓜) (t : Time),
      send p p msg t = some ⟨⟨p, p, msg, t⟩, by rfl⟩
   fairLoss : {Message : Type}
      -> (src : Process)
      -> (dest : Process)
      -> (msg : Message)
      -> (sendAt : Time)
      -- Add proof that all of the options have different times
      -> Stream' (Option {d : FairLossLink.Deliver // d.src = src ∧ d.dest = dest ∧ d.msg = msg ∧ d.sentAt ≥ sendAt})
      -> Stream' {d : FairLossLink.Deliver // d.src = src ∧ d.dest = dest ∧ d.msg = msg ∧ d.sentAt ≥ sendAt}
   -- This one is obvious and follows from fairLoss
   eventualDelivery : {Message : Type}
      -> (src : Process)
      -> (dest : Process)
      -> (msg : Message)
      -> (sendAt : Time)
      -> Stream' (Option {d : FairLossLink.Deliver // d.src = src ∧ d.dest = dest ∧ d.msg = msg ∧ d.sentAt ≥ sendAt})
      -> ∃t, t ≥ sendAt ∧ send src dest msg t = some ⟨⟨src, dest, msg, t⟩, by rfl⟩
   finiteDuplication : NoProof
   noCreation : NoProof

structure StubbornLink.Deliver {Message : Type} where
   src : Process
   dest : Process
   msg : Message
   sentAt : Time

structure StubbornLink where
   fll : FairLossLink
   -- This is also stubborn delivery
   send : {Message : Type}
      -> (src : Process)
      -> (dest : Process)
      -> (msg : Message)
      -> (sendAt : Time)
      -> Stream' {d : StubbornLink.Deliver // d.src = src ∧ d.dest = dest ∧ d.msg = msg ∧ d.sentAt ≥ sendAt}
   noCreation : NoProof

-- This is defined after the StubbornLink because it's the StubbornLink's job
-- to prove this.
def FairLossLink.infiniteSend
   (fll : FairLossLink) (src : Process) (dest : Process) (msg : Message) (sendAt : Time)
   : Stream' (Option {d : FairLossLink.Deliver // d.src = src ∧ d.dest = dest ∧ d.msg = msg ∧ d.sentAt ≥ sendAt})
   :=
      (Time.all.add sendAt).map fun ⟨sendAt', p_sendAt'⟩ =>
         (fll.send src dest msg sendAt').map (by
            intro ⟨delivery, p_delivery⟩
            constructor
            case val => exact delivery
            refine ⟨?_, ?_, ?_, ?_⟩
            · rw [p_delivery]
            · rw [p_delivery]
            · rw [p_delivery]
            · {
               rw [p_delivery]
               simp
               exact p_sendAt'
            }
         )

def StubbornLink.fromFLL (fll : FairLossLink) : StubbornLink := {
   fll := fll,
   send
      {Message : Type} (src : Process) (dest : Process) (msg : Message) (sendAt : Time)
      : Stream' {d : StubbornLink.Deliver // d.src = src ∧ d.dest = dest ∧ d.msg = msg ∧ d.sentAt ≥ sendAt}
      := by
         let infinteSends := fll.infiniteSend src dest msg sendAt
         let unfairLoss := fll.fairLoss src dest msg sendAt infinteSends
         exact unfairLoss.map (by
            intro ⟨fld, ⟨p_fldSrc, p_fldDest, p_fldMsg, p_fldSentAt⟩⟩
            constructor
            -- first construct Stubborn Delivery from Fair Loss Delivery
            case val => exact ⟨fld.src, fld.dest, fld.msg, fld.sentAt⟩
            simp
            exact ⟨p_fldSrc, p_fldDest, p_fldMsg, p_fldSentAt⟩
         )
   noCreation := default
}

end Synchronous
