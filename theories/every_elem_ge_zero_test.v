Require Import SynthesisPlugin.

Set Proverbot Path "/home/arpan/Downloads/proverbot9001-plugin/".

Set Current File Path "/home/arpan/Downloads/coq-synthesis/theories/every_elem_ge_zero_test.v".

Theorem every_elem_ge_zero: forall (n:nat), 0 <= n.
Proof.
    RunProverbot.
Admitted.