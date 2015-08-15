Require Import Program.Tactics.

Inductive Even : nat -> Prop :=
| zero_even : Even 0
| SS_even : forall n, Even n -> Even (S (S n)).

Theorem not_even : forall n, ~ Even n -> ~ Even (S (S n)).
Proof.
  intros; intro.
  inversion H0.
  now elim H.
Qed.

Program Fixpoint isEven (n : nat) : {Even n} + {~ Even n} :=
match n with
| 0        => left   zero_even
| S 0      => right  _
| S (S n)  =>
  match isEven n with
  | left E   => left   _
  | right E  => right  _
  end
end.
(** second case: prove that 1 is not even *)
Next Obligation.
  intros E.
  inversion E.
Defined.
(** recursive call returned that n is even *)
Next Obligation.
  intros.
  now constructor.
Defined.
(** recursive call returned that n is not even *)
Next Obligation.
  intros.
  now apply not_even.
Defined.
