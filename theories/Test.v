Require Import SynthesisPlugin.

(* Fail ExploreProof. *)

Theorem bar:
  forall (T : Set) (t : T), T.
Proof.
  ExploreProof. my_intro T. ExploreProof. my_intro t. ExploreProof. apply t.
Qed.

(* Fail NameProof. *)

(* Fail TryThis. *)

(* Theorem foo:
    forall (T: Set) (t: T), T.
Proof.
    NameProof. my_intro T.
    NameProof. TryThis.
Abort. *)
