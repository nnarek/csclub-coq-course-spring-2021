From mathcomp Require Import ssreflect ssrfun ssrbool.

(** Prove the following lemmas by providing explicit proof terms.
A bunch of exercises from the previous seminar we didn't have time
to cover have made it to this homework :) *)


(* An (unsound) placeholder so that the whole file typechecks.
Please replace it with your proof term. Your solutions may not
use any axioms, including `replace_with_your_solution_here` *)
Axiom replace_with_your_solution_here : forall {A : Type}, A.


Section Logic.

Variables A B C : Prop.

(** * Exercise *)
(*to iteratively write functional proof we can write proof of "conj (...) replace_with_your_solution_here" and then for second part*) (*TODO add into notes*)
Definition __ {A : Type} := @replace_with_your_solution_here A.


Definition notTrue_iff_False : (~ True) <-> False
:= conj (fun nt => nt I) (fun f t => f).

Definition notTrue_iff_False' : (~ True) <-> False
:= conj (fun nt => nt I) (fun f:False => match f with end).

Definition notTrue_iff_False'' : (~ True) <-> False
:= conj (fun nt => nt I) (fun f => match f in False with end).

(* Hint 1: use [Locate "<->".] and [Print iff.] commands to understand better
the type above. *)

(* Hint 2: If you are experiencing an error like the following one
"Found a matching with no clauses on a term unknown to have an empty inductive type." try adding explicit type annotations to functional parameters or
use `match <term> in <type> with ... end` instead of `match <term> with ... end` *)


(** * Exercise: double negation elimination works for `False` *)
Definition dne_False : ~ ~ False -> False
:= fun nnf => nnf (fun f:False => f).

Definition dne_False' : ~ ~ False -> False
:= fun nnf => nnf id.

(** * Exercise: double negation elimination works for `True` too. *)
Definition dne_True : ~ ~ True -> True
:= fun _ => I.


(** * Exercise: Weak Peirce's law
Peirce's law (https://en.wikipedia.org/wiki/Peirce%27s_law) is equivalent to
Double Negation Elimination (and the Law of Excluded Middle too),
so it does not hold in general, but we can prove its weak form. *)
Definition weak_Peirce : ((((A -> B) -> A) -> A) -> B) -> B
:= fun abaab => (*should return B*)
          abaab (fun aba => (*should return A*)
                      aba (fun a => (*should return B*)
                              abaab (fun aba => a (*should return A*) ))).

(* Hint 1: use let-in expression to break the proof into pieces and solve them independently *)
(* Hint 2: annotate the identifiers of let-expressions with types: [let x : <type> := ... in ...] *)


Variable T : Type.
Variable P Q : T -> Prop.

(** * Exercise: existential introduction rule *)
Definition exists_introduction :
  forall (x : T), P x -> (exists (x : T), P x)
:= fun x px => ex_intro _ x px.

(** * Exercise: Frobenius rule: existential quantifiers and conjunctions commute *)
Definition frobenius_rule :
  (exists x, A /\ P x) <-> A /\ (exists x, P x)
:= conj 
      (fun e => match e return (A /\ (exists x, P x)) with 
                | ex_intro x (conj a px) => conj a (ex_intro _ (*(fun t => P t)*) x px) 
                end ) 
      (fun e => match e with 
                | conj a (ex_intro x px) => ex_intro _ x (conj a px)
                end ).
(*TODO why ex_intro require 2 during pattern matching and 3 when we call it*)

End Logic.



Section Equality.

Variables A B C D : Type.

(** * Exercise *)
Definition eq1 : true = (true && true)
:= eq_refl.

(** * Exercise *)
Definition eq2 : 42 = (if true then 21 + 21 else 239)
:= eq_refl.

(** * Exercise *)
Definition LEM_decidable :
  forall (b : bool), b || ~~ b = true
:= fun b => 
        match b with 
        | false => eq_refl 
        | true => eq_refl 
        end.

(** * Exercise *)
Definition if_neg :
  forall (A : Type) (b : bool) (vT vF: A),
    (if ~~ b then vT else vF) = if b then vF else vT
:= fun A b vT vF => 
          match b with 
          | false => eq_refl
          | true => eq_refl 
          end.

(** * Exercise : associativity of function composition *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)

Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
:= eq_refl.


(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)


(** * Exercise: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:= fun f x => eq_refl.

(** * Exercise: Symmetry *)
Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
:= fun f g fg x => 
      match fg x with 
      | eq_refl => eq_refl
      end.

Definition eqext_sym' :
  forall (f g : A -> B), f =1 g -> g =1 f
:= fun f g fg x => eq_sym (fg x).

(** * Exercise: Transitivity *)
Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:= fun f g h fg gh x => eq_trans (fg x) (gh x).

Definition eqext_trans' :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:= fun f g h fg gh x => 
      match gh x (*in (_ = hx) return f x = hx*) with 
      | eq_refl => fg x
      end.

(** * Exercise: left congruence *)
Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
:= fun f g h fg x =>
      match fg x in (_ = gx) return (h \o f) x = h gx with
      | eq_refl => eq_refl
      end.    

(** * Exercise: right congruence *)
Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
:= fun f g h fg x =>
      match fg (h x) (*in (_ = ghx) return (f \o h) x = ghx*) with
      | eq_refl => eq_refl
      end.    

End Equality.


(** * Extra exercises (feel free to skip) *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(* After importing `eqtype` you need to either use a qualified name for
`eq_refl`: `Logic.eq_refl`, or use the `erefl` notation.
This is because `eqtype` reuses the `eq_refl` identifier for a
different lemma.
 *)

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
:= fun a b => match a,b with 
              | false,false => erefl
              | false,true => erefl
              | true,false => erefl
              | true,true => erefl
              end.

(* Definition negbNE' :
  forall b : bool, ~~ ~~ b = true -> b = true
:= fun b e => match b with 
              | false => e (* is inside "e", the variable "b" not get replaced *)
              | true => erefl
              end. *)
              
Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true
:= fun b => match b  with 
              | false => fun e : (~~ ~~ false = true) => e (* when we unify e (which is "~~ ~~ false = true") with result (which is "false = true") then e will be computed or defintions will be unfolded *)
              | true => fun e => erefl
              end.
