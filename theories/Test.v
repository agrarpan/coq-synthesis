Require Import SynthesisPlugin.

Theorem fiff_2 : (2 + 2 = 5) -> (2 + 2 = 3) -> (2 + 2 = 7) <-> False.
Proof.
  split. 
  - PredictTactic.
  (* RunProverbot. *)
Admitted.

(* Decompile fiff_2. *)