Require Import SynthesisPlugin.

Set Proverbot Path "/home/arpan/Downloads/proverbot9001-plugin/".

Set Current File Path "/home/arpan/Downloads/coq-synthesis/theories/list_forall2_app_test.v".


Require Export List.
Variable A: Type.
Variable B: Type.
Variable P: A -> B -> Prop.

Inductive list_forall2: list A -> list B -> Prop :=
  | list_forall2_nil:
      list_forall2 nil nil
  | list_forall2_cons:
      forall a1 al b1 bl,
      P a1 b1 ->
      list_forall2 al bl ->
      list_forall2 (a1 :: al) (b1 :: bl).

Theorem list_forall2_app:
  forall a2 b2 a1 b1,
  list_forall2 a1 b1 -> list_forall2 a2 b2 ->
  list_forall2 (a1 ++ a2) (b1 ++ b2).
Proof.
induction 1.
  RunProverbot.
Admitted.