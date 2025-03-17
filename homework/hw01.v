From mathcomp Require Import ssreflect.

(*| We continue working with our own definitions of Booleans and natural numbers |*)

Module My.

Inductive bool : Type :=
| true
| false.

Definition negb :=
  fun (b : bool) =>
    match b with
    | true => false
    | false => true
    end.

(** * Exercise 1 : boolean functions *)

(*| 1a. Define `orb` function implementing boolean disjunction and test it
_thoroughly_ using the command `Compute`. |*)

Definition orb' (b c : bool) : bool := 
  match b,c with
  | true,_ => true
  | _,true => true
  | false,false => false
  end.

Definition orb (b c : bool) : bool := 
  match b with
  | true => true
  | false => c
  end.

Compute orb false false.
Compute orb true false.
Compute orb true true.

(*| 1b. Define `addb` function implementing _exclusive_ boolean disjunction.
Try to come up with more than one definition (try to make it interesting
and don't just swap the variables) and explore its reduction behavior
in the presence of symbolic variables. |*)

Definition addb (b c : bool) : bool := 
  match b,c with
  | true,true => true
  | _,_ => false
  end.

(*| 1c. Define `eqb` function implementing equality on booleans, i.e. `eqb b c`
must return `true` if and only iff `b` is equal to `c`. Add unit tests. |*)

Definition eqb (b c : bool) : bool := 
  match b,c with
  | false,false => true
  | true,true => true
  | _,_ => false
  end.

Compute eqb false false.
Compute eqb false true.


(** * Exercise 2 : arithmetic *)

Inductive nat : Type :=
| O
| S of nat.


(*| 2a. Define `dec2` function of type `nat -> nat` which takes a natural
number and decrements it by 2, e.g. for the number `5` it must return `3`. Write
some unit tests for `dec2`. What should it return for `1` and `0`? |*)

Definition dec2 (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S(S n') => n'
  end.


Compute dec2 (S O).
Compute dec2 (S (S O)).
Compute dec2 (S (S (S O))).


(*| 2b. Define `subn` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of subtracting `n` from `m`.
E.g. `subn 5 3` returns `2`. Write some unit tests. |*)

Fixpoint subn (m n : nat) : nat := 
  match m,n with
  | O ,O => O
  | O, S _ => O
  | S m', O => m
  | S m', S n' => subn m' n'
  end.

Compute subn O (S O).
Compute subn (S O) O.
Compute subn (S O) (S O).


(*| 2c. Define an `muln` function of type `nat -> nat -> nat` which takes two
natural numbers `m` and `n` and returns the result of their multiplication.
Write some unit tests. |*)

Fixpoint addn (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (addn n' m)
  end.

Fixpoint muln (m n : nat) : nat := 
  match m with 
  | O => O
  | S m' => addn n (muln m' n)
  end.

Compute muln O (S O).
Compute muln (S O) (S O).
Compute muln (S (S O)) (S (S O)).

(** 2d. Implement equality comparison function `eqn` on natural numbers of
type `nat -> nat -> bool`. It returns true if and only if the input numbers are
equal. *)

Fixpoint eqn (m n : nat) : bool := 
  match m,n with
  | O, O => true
  | S m',S n' => eqn m' n'
  | _,_ => false
  end.

Compute eqn O (S O).
Compute eqn (S O) (S O).
Compute eqn (S (S O)) (S (S O)).

(** 2e. Implement less-or-equal comparison function `leq` on natural numbers of
type `nat -> nat -> bool`. `leq m n` returns `true` if and only if `m` is less
than or equal to `n`. Your solution must not use recursion but you may reuse any
of the functions you defined in this module so far. *)

Definition leq (m n : nat) : bool := 
  if subn m n is O then true else false. 

Compute leq O (S O).
Compute leq (S O) (S O).
Compute leq (S (S O)) (S (S O)).
Compute leq (S O) O.
Compute leq (S (S O)) (S O).

(*| ---------------------------------------------------------------------------- |*)


(*| EXTRA problems: feel free to skip these. If you need to get credit for this
class: extra exercises do not influence your grade negatively if you skip them.
|*)

(*| Ea: implement division (`divn`) on natural numbers and write some unit tests
for it. |*)

Fixpoint modn (m n : nat) : nat := 
  match m,n with
  | O, _ => O
  | _, O => O
  | S m', S n' => let md := modn m' (S n') in if eqn md n' is true then O else S md
  end.


Fixpoint divn (m n : nat) : nat := 
  match m,n with
  | O, _ => O
  | _, O => O
  | S m', S n' => if modn (S m') (S n') is O then S (divn m' (S n')) else divn m' (S n')
  end.
(*we can write helper function to calculate mod and div at same time and return nat*nat *)

Compute divn O (S O).
Compute divn (S O) (S O).
Compute divn (S (S O)) (S (S O)).
Compute divn (S O) O.
Compute divn (S (S O)) (S O).
Compute divn (S (S (S O))) (S (S O)).
Compute divn (S (S (S (S O)))) (S (S O)).

End My.
