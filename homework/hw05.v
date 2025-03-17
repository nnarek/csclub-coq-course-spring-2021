From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Use SSReflect tactics.
    DO NOT use automation like [tauto], [intuition], [firstorder], etc.,
    except for [by], [done], [exact] tactic(al)s. *)


(** * Exercise *)
Lemma nlem (A : Prop):
  ~ (A \/ ~ A) -> A.
Proof.
move=> h.
have: False.
- apply h.
  right=> a.
  apply h.
  by left.
- case.
Qed.
(** Hint: you might want to use a separate lemma here to make progress.
Or, use the `have` tactic: `have: statement` creates a new subgoal and asks
you to prove the statement. This is like a local lemma. *)


(** * Exercise *)
Lemma weak_Peirce (A B : Prop) :
  ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
move => abaab.
apply abaab => aba.
apply aba => a.
apply abaab => _.
exact a.
Qed.


(** * Exercise *)
(* Prove that having a general fixed-point combinator in Coq would be incosistent *)
Definition FIX := forall A : Type, (A -> A) -> A.

Lemma fix_inconsistent :
  FIX -> False.
Proof.
move=> FIX.
apply FIX.
case.
Qed.


Section Boolean.
(** * Exercise *)
Lemma negbNE b : ~~ ~~ b -> b.
Proof.
case b=>//.
Show Proof.
Qed.


(** * Exercise *)
Lemma negbK : involutive negb.
Proof.
rewrite /involutive /cancel => b.
case b=>//.
Qed.


(** * Exercise *)
Lemma negb_inj : injective negb.
Proof.
rewrite /injective => x1 x2.
case x1; case x2=>//.
Qed.

Lemma aa : true. (* TODO how it is possible to create such propositions?? *)
Proof. done. Qed.

End Boolean.


(** * Exercise *)
Fixpoint triple (n : nat) : nat :=
  if n is n'.+1 then (triple n').+3
  else n.

Lemma triple_mul3 n :
  triple n = 3 * n.
Proof.
elim n=>// => n' h //=.
rewrite h.
Search (?a * (S ?b)).
rewrite mulnS.
done.
Qed.
(** Hints:
- use the /= action to simplify your goal: e.g. move=> /=.
- use `Search (<pattern>)` to find a useful lemma about multiplication
*)


(** * Exercise
Prove by it induction: you may re-use the addnS and addSn lemmas only *)
Lemma double_inj m n :
  m + m = n + n -> m = n.
Proof.
move: n.
elim m => [ | m' h n].
- by case n in *.
- case n in * => //=.
  rewrite !addSn !addnS.
  case.
  move /h.
  apply congr1.
Qed.
(* This is a harder exercise than the previous ones but
   the tactics you already know are sufficient *)




(** * Optional exercise
    [negb \o odd] means "even".
    The expression here says, informally,
    the sum of two numbers is even if the summands have the same "evenness",
    or, equivalently, "even" is a morphism from [nat] to [bool] with respect
    to addition and equivalence correspondingly.
    Hint: [Unset Printing Notations.] and [rewrite /definition] are your friends :)
 *)
Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Proof.

Admitted.


(** * Optional exercise *)
Lemma DNE_iff_nppp :
  (forall P, ~ ~ P -> P) <-> (forall P, (~ P -> P) -> P).
Proof.
split => h1 P h2.
- apply h1 => np. apply: np (h2 np). 
- apply h1 => np. case: (h2 np).   
Qed.


(** * Optional exercise *)
Lemma leq_add1l p m n :
  m <= n -> m <= p + n.
Proof.
Search (_ <= _ + _).
move => h.
apply (@leq_add 0) =>//.
Qed.
(** Hint: this lemmas does not require induction, just look for a couple lemmas *)





(* ================================================ *)

(*
More fun with functions, OPTIONAL
*)

Section PropertiesOfFunctions.

Section SurjectiveEpic.
Context {A B : Type}.

(* https://en.wikipedia.org/wiki/Surjective_function *)
(** Note: This definition is too strong in Coq's setting, see [epic_surj] below *)
Definition surjective (f : A -> B) :=
  exists g : B -> A, f \o g =1 id.

(** This is a category-theoretical counterpart of surjectivity:
    https://en.wikipedia.org/wiki/Epimorphism *)
Definition epic (f : A -> B) :=
  forall C (g1 g2 : B -> C), g1 \o f =1 g2 \o f -> g1 =1 g2.

(** * Optional exercise *)
Lemma surj_epic f : surjective f -> epic f.
Proof.
rewrite /surjective /epic /eqfun /comp.
move=> [g h] C g1 g2 g1fg2f x.
move: (h x) => hx.
rewrite <-hx.
apply g1fg2f.
Qed.

(** * Optional exercise *)
Lemma epic_surj f : epic f -> surjective f.
  (** Why is this not provable? *)
  (*TODO*)
Abort.

Lemma epic_surj_contr : (forall f, epic f -> surjective f) -> False.
Proof.
rewrite /surjective /epic /eqfun /comp => h.
Abort.


End SurjectiveEpic.


Section EpicProperties.
Context {A B C : Type}.

(** * Optional exercise *)
Lemma epic_comp (f : B -> C) (g : A -> B) :
  epic f -> epic g -> epic (f \o g).
Proof.
rewrite /epic /eqfun /comp.
move=> hf hg C' g1 g2 h x. 
apply hf.
apply: hg h.
Qed.

(** * Optional exercise *)
Lemma comp_epicl (f : B -> C) (g : A -> B) :
  epic (f \o g) -> epic f.
Proof.
rewrite /epic /eqfun /comp.
move=> hefg C' g1 g2 h c.
apply hefg => a.
apply h.
Qed.

(** * Optional exercise *)
Lemma retraction_epic (f : B -> A) (g : A -> B) :
  (f \o g =1 id) -> epic f.
Proof.
rewrite /epic /eqfun /comp.
move=> hid C' g1 g2 h a.
move: (h (g a)) => ha.
by rewrite hid in ha.
Qed.

End EpicProperties.


(** The following section treats some properties of injective functions:
    https://en.wikipedia.org/wiki/Injective_function *)

Section InjectiveMonic.

Context {B C : Type}.

(** This is a category-theoretical counterpart of injectivity:
    https://en.wikipedia.org/wiki/Monomorphism *)
Definition monic (f : B -> C) :=
  forall A (g1 g2 : A -> B), f \o g1 =1 f \o g2 -> g1 =1 g2.

(** * Optional exercise *)
Lemma inj_monic f : injective f -> monic f.
Proof.
rewrite /injective /monic /eqfun /comp.
move=> hinjf A g1 g2 h a.
apply hinjf.
apply h.
Qed.


(** * Optional exercise *)
Lemma monic_inj f : monic f -> injective f.
Proof.
rewrite /injective /monic /eqfun /comp.
move=> hmf x1 x2 fx1fx2.
apply (@hmf unit (fun _ => x1) (fun _ => x2)) =>//.
Qed.

End InjectiveMonic.


Section MonicProperties.
Context {A B C : Type}.

(** * Optional exercise *)
Lemma monic_comp (f : B -> C) (g : A -> B) :
  monic f -> monic g -> monic (f \o g).
Proof.
rewrite /monic /eqfun /comp.
move=> hmf hmg C' g1 g2 h x.
apply hmg => x'.
move: (h x') => hx.
apply (monic_inj hmf hx).
Qed.

(** * Optional exercise *)
Lemma comp_monicr (f : B -> C) (g : A -> B) :
  monic (f \o g) -> monic g.
Proof.
rewrite /monic /eqfun /comp.
move=> hmfg C' g1 g2 h x.
apply hmfg => x'.
rewrite (h x') =>//.
Qed.

(** * Optional exercise *)
Lemma section_monic (f : B -> A) (g : A -> B) :
  (g \o f =1 id) -> monic f.
Proof.
rewrite /monic /eqfun /comp.
move=> hid C' g1 g2 h x.
move: (h x) => hx.
have: g (f (g1 x)) = g (f (g2 x)) by rewrite hx.
rewrite !(hid _) =>//.
Qed.

End MonicProperties.

End PropertiesOfFunctions.
