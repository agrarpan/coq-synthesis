Require Import SynthesisPlugin.

Theorem fiff_2 : (2 + 2 = 5) -> (2 + 2 = 3) -> False.
Proof.
  intros. 
  ShowGoals.
  (* RunProverbot. *)
Admitted.

(* Decompile fiff_2. *)