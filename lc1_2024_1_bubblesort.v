(** Lógica Computacional 1 - 2024/1 *)
(** Projeto: formalização da correção do algoritmo bubblesort utilizando a estrutura de listas.

Nome e matrícula dos participantes:
1.
2.
3.
*)

Require Import Arith List Lia.
Require Import Recdef.

Function bubble l {measure length l} := match l with
            | nil => nil
            | h::nil => h::nil
            | h1::h2::l' => if h1 <=? h2 then (h1::(bubble (h2::l'))) else (h2::(bubble (h1::l')))
                                                                           end.
Proof.
  - intros. simpl. lia.
  - intros. simpl. lia.
Qed.

Lemma ex1: bubble (3::2::1::nil) = 2::1::3::nil.
Proof.
  rewrite bubble_equation. simpl. rewrite bubble_equation. simpl. rewrite bubble_equation. reflexivity.
Qed.

Fixpoint  bubblesort l := match l with
                  | nil => nil
                          | h::l' => bubble (h::(bubblesort l'))
                          end.

Lemma ex2: (bubblesort (3::2::1::nil)) = 1::2::3::nil.
Proof.
  simpl. replace (bubble (1::nil)) with (1::nil).
  - replace (bubble (2::1::nil)) with (1::2::nil).
    + rewrite bubble_equation. simpl. rewrite bubble_equation. simpl. rewrite bubble_equation. reflexivity.
    + rewrite bubble_equation. simpl. rewrite bubble_equation. simpl. reflexivity.
  - rewrite bubble_equation. reflexivity.
Qed.

Require Import Permutation.

Print Permutation.

Inductive sorted: list nat -> Prop :=
  sorted_nil: sorted nil
| sorted_one: forall x, sorted (x::nil)
| sorted_all: forall x y l, x <= y -> sorted (y::l) -> sorted (x::y::l).

Lemma sorted_bubble: forall l' x, sorted l' -> sorted (bubble (x::l')).
Proof.
  Admitted.

Lemma bubblesort_ordena: forall l, sorted (bubblesort l).
Proof.
  induction l.
  - simpl. apply sorted_nil.
  - simpl. apply sorted_bubble. apply IHl.
Qed.

Lemma perm_bubble: forall l a, Permutation (a :: l) (bubble (a :: l)).
Proof.
Admitted.

Lemma bubblesort_perm: forall l, Permutation l (bubblesort l).
Proof.
  induction l.
  - admit.
  - simpl. 
  Admitted.

Theorem bubblesort_correto: forall l, sorted (bubblesort l) /\ Permutation l (bubblesort l).
Proof.
  Admitted.
