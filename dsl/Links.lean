import dsl.Runtime

namespace Synchronous

variable {𝓜 : Type}

namespace FairLossLink
   inductive Request where
      | nothing
      | send (src dest : Process) (msg : 𝓜)
   def Requests := Stream' <| @Request 𝓜
   inductive Indication where
      | nothing
      | deliver (src dest : Process) (msg : 𝓜)
   structure EventStream (reqs : Requests) where
      inds : Stream' <| @Indication 𝓜
      selfSend : {_ : Unit}
         -> (p : Process)
         -> (msg : 𝓜)
         -> (∃ t, reqs t = .send p p msg)
         -> (∃ t' > t, inds t' = .deliver p p msg)
      fairLoss : {_ : Unit}
         -> (src dest : Process)
         -> (msg : 𝓜)
         -> (startAt : Time)
         -> (∀ T ≥ startAt, ∃ t ≥ T, reqs t = .send src dest msg)
         -> (∀ T ≥ startAt, ∃ t ≥ T, inds t = .deliver src dest msg)
      finiteDuplication : {_ : Unit}
         -> (src dest : Process)
         -> (msg : 𝓜)
         -> (∃ T1, ∀ t < T1, reqs t ≠ .send src dest msg)
         -> (∃ T2, ∀ t < T2, inds t ≠ .deliver src dest msg)
      noCreation : {_ : Unit}
         -> (src dest : Process)
         -> (msg : 𝓜)
         -> (deliveredAt : Time)
         -> (inds deliveredAt = .deliver src dest msg)
         -> (∃ sentAt < deliveredAt, reqs sentAt = .send src dest msg)
      -- causality : {_ : Unit}
      --    -> (src dest : Process)
      --    -> (msg : 𝓜)
      --    -> ()
end FairLossLink
structure FairLossLink where
   request : (reqs : @FairLossLink.Requests 𝓜)
      -> FairLossLink.EventStream reqs

namespace StubbornLink
   inductive Request where
      | nothing
      | send (src dest : Process) (msg : 𝓜)
   def Requests := Stream' <| @Request 𝓜
   inductive Indication where
      | nothing
      | deliver (src dest : Process) (msg : 𝓜)
   def Indications := Stream' <| @Indication 𝓜
   structure EventStream (reqs : Requests) where
      inds : Indications
      stubbornDelivery : {_ : Unit}
         -> (src dest : Process)
         -> (msg : 𝓜)
         -> (sentAt : Time)
         -> (reqs sentAt = .send src dest msg)
         -> (∀ T ≥ sentAt, ∃ t ≥ T, inds t = .deliver src dest msg)
      noCreation : {_ : Unit}
         -> (src dest : Process)
         -> (msg : 𝓜)
         -> (deliveredAt : Time)
         -> (inds deliveredAt = .deliver src dest msg)
         -> (∃ sentAt < deliveredAt, reqs sentAt = .send src dest msg)
end StubbornLink
structure StubbornLink where
   request : (reqs : @StubbornLink.Requests 𝓜)
      -> StubbornLink.EventStream reqs
-- def StubbornLink._request (fll : @FairLossLink 𝓜) (reqs : @StubbornLink.Requests) :=
   

def StubbornLink.fromFLL (fll : @FairLossLink 𝓜) : @StubbornLink 𝓜 := {
   request reqs : EventStream reqs := {
      inds :=
         let rec inds : @Indications 𝓜
         | 0 => .nothing
         | (n + 1) => inds n
         inds
   }
} where indsHandler := 

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

-- This is defined after the StubbornLink because it's the StubbornLink's job
-- to prove this.
-- def FairLossLink.infiniteSend
--    (fll : FairLossLink) (src : Process) (dest : Process) (msg : Message) (sendAt : Time)
--    : Stream' (Option {d : FairLossLink.Deliver // d.src = src ∧ d.dest = dest ∧ d.msg = msg ∧ d.sentAt ≥ sendAt})
--    :=
--       (Time.all.add sendAt).map fun ⟨sendAt', p_sendAt'⟩ =>
--          (fll.send src dest msg sendAt').map (by
--             intro ⟨delivery, p_delivery⟩
--             constructor
--             case val => exact delivery
--             refine ⟨?_, ?_, ?_, ?_⟩
--             · rw [p_delivery]
--             · rw [p_delivery]
--             · rw [p_delivery]
--             · {
--                rw [p_delivery]
--                simp
--                exact p_sendAt'
--             }
--          )



end Synchronous
