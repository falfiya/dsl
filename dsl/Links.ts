namespace Synchronous {
   export namespace FairLossLink {
      /**
       * Deliver indication
       */
      export type deliver = {src: Process, dest: Process, msg: Message} | null;
   }
   export interface FairLossLink extends Component {
      send(to: Process, msg: Message): FairLossLink.deliver;
      /**
       * Who knows if you'll ever have one of these, but hypothetically if you
       * did... ;)
       */
      fairLoss: Proof<"Stream' FairLossLink.deliver -> exists deliver">;
      finiteDuplication: Proof<[
         "No way to get Stream' FairLossLink.deliver without another Stream'...",
         "Alternatively, sending infinitely and then slicing it so that it's not",
         "infinite anymore leaves you with a finite amount of deliveries.",
      ]>;
      noCreation: Proof<[
         "If a delivery occured, there was a send method call at some point.",
      ]>;
   }
}
