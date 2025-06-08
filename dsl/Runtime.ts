type Proof<_> = never;

type Time = number;

type Process = {
   id: number;
   isCorrect: boolean;
   aliveAt(t: Time): boolean;
   pCorrect: Proof<"isCorrect = true -> forall t, aliveAt t = true">
}

type Message = any;

type Synchronous = {
   Ps: Process[];
};

/**
 * Non-byzantine, synchronous components.
 */
namespace Synchronous {
   /**
    * Number of processes in the group.
    */
   export type N = number;

   export type Component = {
      id: number;
   }
}
