From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(* An (unsound) placeholder so that the whole file typechecks.
Please replace it with your proof term. Your solutions may not
use any axioms, including `replace_with_your_solution_here` *)
Axiom replace_with_your_solution_here : forall {A : Type}, A.


(* WARNING!
 Since we import `eqtype` module which redefines `eq_refl` to mean something else
 other than the equality type constructor, beware of using `eq_refl` in
 pattern-matching.
 For instance, in a `match`-expression like this one
    match foo in ... return ... with
    | eq_refl => ...
    end
 eq_refl is a new identifier which just shadows the `eq_refl` lemma,
 hence no index rewriting is happening. If you see weird type errors,
 just make sure you spelled the equality type constructor correctly
 in this context:
    match foo in ... return ... with
    | erefl => ...
    end
*)


(** * Exercise: show that [ex] is a more general case of [and].
    This is because terms of type [ex] are dependent pairs, while terms of type [and]
    are non-dependent pairs, i.e. the type of the second component in independent of the
    value of the first one. *)

Definition and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B
:= conj 
      (fun e => 
            match e with 
            | ex_intro a b => conj a b 
            end) 
      (fun ab => 
            match ab with 
            | conj a b => ex_intro (fun a => B) a b
            end).


(** * Exercise *)
Section Symmetric_Transitive_Relation.

Variables (D : Type)
          (R : D -> D -> Prop).

(* R's type D -> D -> Prop means R is a binary relation *)

(* The lemma refl_if read informally, means
"if R is a symmetric and transitive relation
then each element x which is related to some
element y is also related to itself" *)
Definition refl_if :
  (forall x y, R x y -> R y x) ->
  (forall x y z, R x y -> R y z -> R x z) ->
  forall x : D, (exists y, R x y) -> R x x
:= fun sym trans x e => 
      match e with
      | ex_intro y rxy => let ryx := sym _ _ rxy in
                              trans _ _ _ rxy ryx
      end.

End Symmetric_Transitive_Relation.


(** * Exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:= fun peq => match peq in _ = (a2, b2) return (_ = a2) /\ (_ = b2) with
              | erefl => conj erefl erefl
              end.


(** * Exercise *)
Inductive trilean : Type :=
  | Yes
  | No
  | Maybe.

Definition yes_no_disj :
  Yes <> No
:= fun yneq => let to_prop := (fun a => if a is Yes then True else False) in
               match yneq with
               | erefl => (I : to_prop Yes)
                          (* same as "let yes_prop : to_prop Yes := I in yes_prop" *)
                          (*"to_prop Yes" will be replaced by "to_prop No"*)

               end.


(** * Exercise *)
(*
0 + (y + z) = 0 + y + z
y + z = 0 + y + z
y + z = y + z


x'.+1 + (y + z) = x'.+1 + y + z
(x' + (y + z)).+1 = (x'.+1 + y) + z
(x' + (y + z)).+1 = (x' + y).+1 + z
(x' + (y + z)).+1 = ((x' + y) + z).+1

S (x' + (y + z)) = S ((x' + y) + z)

(x' + (y + z))   =   ((x' + y) + z)
*)
Check congr1.
Definition addA : associative addn
 (* forall x y z : nat, x + (y + z) = x + y + z *)
:= fix IHx x y z :=
     match x as x
       return (x + (y + z) = x + y + z)
     with
     | 0 => erefl (y + z)
     | x'.+1 =>
       let IHx' : x' + (y + z) = x' + y + z :=
           IHx x' y z
       in congr1 S IHx'
     end.
Definition addA' : associative addn
:= fix IHx {x y z} :=
     if x is x'.+1 then congr1 S IHx else erefl.

Print associative.
Eval hnf in associative addn.
Print addn.
Check tt.
Print nosimpl.
Print addn_rec.
Print Nat.add.


Definition addsuccn : forall x y, S (addn x y) = addn x (S y)
:= fix self x y := if x is n.+1 then 
                      congr1 S (self n y)
                   else erefl.

(** * Exercise: *)
Definition addnCA : left_commutative addn
:= fix self x y z := if x is n.+1 then 
                        match addsuccn y (n+z) in _ = w return (n + (y + z)).+1 = w with 
                        | erefl => congr1 S (self n y z) 
                        end 
                     else erefl.

(* Hint: re-use addnS lemma and some general lemmas about equality *)






(** * ====== Optional exercises (feel free to skip) ====== *)

(** * Exercise (optional) *)
Definition J :
  forall (A : Type) (P : forall (x y : A), x = y -> Prop),
    (forall x : A, P x x erefl) ->
    forall x y (p : x = y), P x y p
:= fun A P pxx x y pxy => match pxy in _ = y' return P x y' pxy with 
                          | erefl => pxx x 
                          end.





(** * Exercise (optional): *)
Definition addnC : commutative addn
:= fix self x y := if x is n.+1 then 
                      match addsuccn y n with 
                      | erefl => congr1 S (self n y) 
                      end 
                   else 
                      match addn0 y with 
                      | erefl => erefl
                      end.


(** * Exercise (optional):
Formalize and prove
 - bool ≡ unit + unit,
 - A + B ≡ {b : bool & if b then A else B},
 - A * B ≡ forall b : bool, if b then A else B,
where ≡ means "is isomorphic to".
 *)
Record Iso (A B : Type) := {
  to : A -> B;
  from : B -> A;
  to_from : forall b, to (from b) = b;
  from_to : forall a, from (to a) = a
}.

Definition bequu : Iso bool (unit + unit) := {|
  to := (fun b => if b is true then inl tt else inr tt);
  from := (fun uu => if uu is inl tt then true else false);
  to_from := fun uu => match uu with 
                      | inl tt => erefl 
                      | inr tt => erefl
                      end;
  from_to := fun b => if b is true then erefl else erefl |}.



Definition sumif (A B : Type): Iso (A + B) {b : bool & if b then A else B} := {|
  to := (fun sab => match sab with 
                    | inl a => existT _ true a
                    | inr b => existT _ false b
                    end);
  from := (fun eb => match eb with 
                     | existT true a => inl a
                     | existT false b => inr b
                     end );
  (* functional code generated by tactics *)
  (* TODO try to understand and simplify *)
  to_from := fun b : {b : bool & if b then A else B} =>
  let
    (x, y) as s
     return
       (match
          (let (x, b0) := s in
           (if x as x0 return ((if x0 then A else B) -> A + B)
            then (fun a => inl a) 
            else (fun b => inr b) ) b0)
        with
        | inl a =>
            existT (fun b0 : bool => if b0 then A else B) true a
        | inr b0 =>
            existT _ false b0
        end = s) := b in
  let b0 := x in
  let hx : x = b0 := erefl b0 in
  (if b0 as b1
    return
      (x = b1 ->
       forall y0 : if b1 then A else B,
       match
         (if b1 as x0 return ((if x0 then A else B) -> A + B)
          then [eta inl]
          else [eta inr]) y0
       with
       | inl a =>
           existT (fun b2 : bool => if b2 then A else B) true a
       | inr b2 =>
           existT _ false b2
       end = existT (fun b2 : bool => if b2 then A else B) b1 y0)
   then
    fun _ => (fun y0 : A => erefl)
   else
    fun _ => (fun y0 : B => erefl))
    hx y;

  from_to := (fun sab => match sab with 
                         | inl a => erefl
                         | inr b => erefl
                         end); |}.



(* same as above one *)
Definition sumif' (A B : Type): Iso (A + B) {b : bool & if b then A else B}.  
Proof.
exists (fun sab => match sab with 
| inl a => existT (fun b => if b then A else B) true a
| inr b => existT (fun b => if b then A else B) false b
end) (fun eb => match eb with 
 | existT true a => inl a
 | existT false b => inr b
 end ).
- intros.
  destruct b; simpl.
  destruct x eqn:hx; reflexivity.
- exact (fun sab => match sab with 
  | inl a => erefl
  | inr b => erefl
  end).
Qed.


From Coq Require Import PropExtensionality.
From Coq Require Import FunctionalExtensionality.


Definition prodif (A B : Type): Iso (A * B) (forall b : bool, if b then A else B)
:= {|
  to := fun p b => if b is true return (if b then A else B) then 
                      fst p 
                   else 
                      snd p;
  from := fun fb => pair (fb true) (fb false);
  to_from := fun fb => functional_extensionality_dep _ fb (*functional_extensionality can not applied to dependent functions and also functional_extensionality_dep can not applied to non-dependent functions. but Lean4 allow to apply dependent funext axiom to non-dependent function because it able to automatically treat non-dependent functions as dependent functions(seems like they use some form of subtypeing for function) *)
  (fun b : bool =>
      match b return (if b as b1 return (if b1 then A else B) 
                      then fb true 
                      else fb false) = fb b 
              with
      | true => erefl 
      | false => erefl 
      end) ;
  from_to := fun p => match p with
                      | (a,b) => erefl
                      end |}.



Definition unit_neq_bool_pred (t : Type) := forall e1 e2 : t , e1 = e2.

Search (true <> false).
Search tt.

(** * Exercise (optional): *)
Definition unit_neq_bool:
  unit <> bool
:= fun ubeq => 
        let pred_unit : unit_neq_bool_pred unit := fun e1 e2 =>
              match e1,e2 with 
              | tt,tt => erefl
              end
        in 
        (match Logic.eq_sym ubeq in _ = u return unit_neq_bool_pred u -> False with 
        | erefl => fun pred_bool : unit_neq_bool_pred bool =>
                          Bool.diff_true_false (pred_bool true false)
        end) pred_unit.

(*fails because rewrite can not lead type mismatch*)
Fail Definition unit_neq_bool':
unit <> bool
:= fun ubeq => 
      let pred_unit : (forall e1 e2 : unit , e1 = tt) := fun e1 e2 =>
            match e1,e2 with 
            | tt,tt => erefl
            end
      in 
      (match Logic.eq_sym ubeq in _ = u return (forall e1 e2 : u , e1 = tt) -> False with 
      | erefl => fun pred_bool : (forall e1 e2 : bool , e1 = tt) =>
                        Bool.diff_true_false (pred_bool true false)
      end) pred_unit.
