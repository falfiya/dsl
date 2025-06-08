import dsl.Runtime
import dsl.Stream

namespace Synchronous

namespace FairLossLink
   structure Deliver {Message : Type} where
      src : Process
      dest : Process
      msg : Message
      sentAt : Time
end FairLossLink
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
      -> Stream' (Option {d : FairLossLink.Deliver // d.src = p ∧ d.dest = dest ∧ d.msg = msg})
      -> ∃t, send src dest msg t = some ⟨⟨src, dest, msg, t⟩, by rfl⟩

end Synchronous
