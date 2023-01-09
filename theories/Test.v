Require Import SynthesisPlugin.

Definition definition := 5.
(* What's definition.
What kind of term is definition.
What kind of identifier is definition.

What is 1 2 3 a list of.
What is a list of.

Is 1 2 3 nonempty.
And is 1 provided.
And is provided. *)

(* Intern 3.
Intern definition.
Intern (fun (x : Prop) => x).
Intern (fun (x : Type) => x).
Intern (forall (T : Type), T).
Intern (fun (T : Type) (t : T) => t).
Intern _.
Intern (Type : Type). *)

(* MyDefine n := 1.
(* Print n. *)

MyDefine f := (fun (x : Type) => x).
(* Print f. *)

MyPrint f.
MyPrint n.
Fail MyPrint nat. *)

DefineLookup n' := 1.
DefineLookup f' := (fun (x : Type) => x).