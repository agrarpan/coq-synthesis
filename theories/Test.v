Require Import SynthesisPlugin.

(* Fail ExploreProof.

Theorem bar:
  forall (T : Set) (t : T), T.
Proof.
  ExploreProof. my_intro T. ExploreProof. my_intro t. ExploreProof. apply t.
Qed.

Fail NameProof. *)

Fail TryThis.

Theorem foo:
    forall (T: Set) (t: T), T.
Proof.
    (* NameProof. my_intro T. *)
    NameProof.
Abort.


Theorem fiff: (2 + 2 = 5) <-> (2 + 2 = 3).
Proof.
  TryThis.
  intros.
  split.
  TryThis.
Abort.

Theorem fiff_2 : (2 + 2 = 5) <-> (2 + 2 = 3).
Proof.
  PrintGoals.
  intros.
  split.
  PrintGoals.
Abort.