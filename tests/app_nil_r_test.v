Require Import SynthesisPlugin.

Set Proverbot Path "/home/arpan/Downloads/proverbot9001-plugin/".

Set Current File Path "/home/arpan/Downloads/coq-synthesis/theories/app_nil_r_test.v".

Require Import List.
Import ListNotations.

Theorem app_nil_r: forall {A: Type} (l: list A), l ++ [] = l.
Proof.
  RunProverbot.
Admitted.