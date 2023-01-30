Require Import SynthesisPlugin.

Theorem fiff_2 : (2 + 2 = 5) <-> (2 + 2 = 3).
Proof.
  RunProverbot.
Abort.