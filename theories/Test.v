Require Import SynthesisPlugin.

Set Proverbot Path "/home/arpan/Downloads/proverbot9001-plugin/".

Set Current File Path "/home/arpan/Downloads/coq-synthesis/theories/Test.v".

Theorem fiff_2 : (2 + 2 = 7) -> False.
Proof.
  intros.
  RunProverbot2.
Admitted.
