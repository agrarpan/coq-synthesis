Require Import SynthesisPlugin.

Definition definition := 5.
What's definition.
What kind of term is definition.
What kind of identifier is definition.

What is 1 2 3 a list of.
What is a list of.

Is 1 2 3 nonempty.
And is 1 provided.
And is provided.

Intern 3.
Intern definition.
Intern (fun (x : Prop) => x).
Intern (fun (x : Type) => x).
Intern (forall (T : Type), T).
Intern (fun (T : Type) (t : T) => t).
Intern _.
Intern (Type : Type).

MyDefine n := 1.
Print n.

MyDefine f := (fun (x : Type) => x).
Print f.

MyPrint f.
MyPrint n.
Fail MyPrint nat.

DefineLookup n' := 1.
DefineLookup f' := (fun (x : Type) => x).

Check1 3.
Check1 definition.
Check1 (fun (x : Prop) => x).
Check1 (fun (x : Type) => x).
Check1 (forall (T : Type), T).
Check1 (fun (T : Type) (t : T) => t).
Check1 _.
Check1 (Type : Type).

Check2 3.
Check2 definition.
Check2 (fun (x : Prop) => x).
Check2 (fun (x : Type) => x).
Check2 (forall (T : Type), T).
Check2 (fun (T : Type) (t : T) => t).
Check2 _.
Check2 (Type : Type).

Convertible 1 1.
Convertible (fun (x : Type) => x) (fun (x : Type) => x).
Convertible Type Type.
Convertible 1 ((fun (x : nat) => x) 1).

Convertible 1 2.
Convertible (fun (x : Type) => x) (fun (x : Prop) => x).
Convertible Type Prop.
Convertible 1 ((fun (x : nat) => x) 2).


Fail ExploreProof.

Theorem bar:
  forall (T : Set) (t : T), T.
Proof.
  ExploreProof. my_intro T. ExploreProof. my_intro t. ExploreProof. apply t.
Qed.

Fail NameProof.

Theorem foo:
    forall (T: Set) (t: T), T.
Proof.
    NameProof. my_intro T.
    NameProof.
Abort.

Count.
Count.
Count.