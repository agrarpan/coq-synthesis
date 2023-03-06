Require Import SynthesisPlugin.

Theorem fiff_2 : (2 + 2 = 5) -> (2 + 2 = 3) -> (2 + 2 = 7) <-> False.
Proof.
  (* RunProverbotOnFile (IDENT "~/Downloads/coq-synthesis/theories/Test.v"). *)
  (* StringInput abc. *)
  (* split.  *)
  (* - PredictTactic. *)
  RunProverbot.
Admitted.

(* Decompile fiff_2. *)