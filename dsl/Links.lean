import dsl.Runtime

namespace Synchronous

structure FairLossLink.Deliver {Message : Type} where
   src : Process
   dest : Process
   msg : Message
   sentAt : Time

structure FairLossLink where
   send : {Message : Type}
      -> (src : Process)
      -> (dest : Process)
      -> (msg : Message)
      -> (sendAt : Time)
      -> Option ({d : FairLossLink.Deliver // d = ⟨src, dest, msg, sendAt⟩})
   selfSend : ∀ {Message : Type} (p : Process) (msg : Message) (t : Time),
      send p p msg t = some ⟨⟨p, p, msg, t⟩, by rfl⟩
   fairLoss : {Message : Type}
      -> (src : Process)
      -> (dest : Process)
      -> (msg : Message)
      -> (sendAt : Time)
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
   := (Time.all.add sendAt).map (by
      intro ⟨sendAt', p_sendAt'⟩
      exact (fll.send src dest msg sendAt').map (by
         intro ⟨delivery, p_delivery⟩
         constructor
         case val => exact delivery
         simp
         refine ⟨?_, ?_, ?_, ?_⟩
         · rw [p_delivery]
         · rw [p_delivery]
         · rw [p_delivery]
         · rw [p_delivery]; simp; exact p_sendAt'
      ))

def StubbornLink.fromFLL (fll : FairLossLink) : StubbornLink := {
   fll := fll,
   send
      {Message : Type} (src : Process) (dest : Process) (msg : Message) (sendAt : Time)
      : Stream' {d : StubbornLink.Deliver // d.src = src ∧ d.dest = dest ∧ d.msg = msg ∧ d.sentAt ≥ sendAt}
      := by
         let infinteSends := fll.infiniteSend src dest msg sendAt
         let fairLoss := fll.fairLoss src dest msg sendAt infinteSends
         exact fairLoss.map (by
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
