
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic

set_option autoImplicit false

-- Aula 06: Predicados indutivos.

-- * Predicado de números pares

inductive even : ℕ → Prop where
| zero : even 0
| succ : ∀ n, even n → even (n + 2)

example : even 8 := by
  apply even.succ
  apply even.succ
  apply even.succ
  apply even.succ
  apply even.zero

/-
evenn = ∃ m, n = m * 2 -- não indutiva, recursiva

-------------------(zero)
even 0

even n
-------------------(succ)
even (n + 2)
-/

def evenb (n : ℕ) : Bool :=
  match n with
  | 0 => true
  | 1 => false
  | n' + 2 => evenb n'

-- ∀ n, P(n) ≃ P(0) ∧ (∀ n, P(n) → P(n + 1)) : Principio
-- de indução.
-- definição de princípios de indução.

def nat_ind  (P : ℕ → Prop)
             (base : P 0)
             (step : ∀ n, P n → P (n + 1)) :
             ∀ (n : ℕ), P n := λ n =>
    match n with
    | 0 => base
    | n' + 1 => step n' (nat_ind P base step n') -- P(n' + 1)

-- construindo provas com um princípio de indução
-- customizado

lemma plus_0_left (n : ℕ) : 0 + n = n := by
   induction n using nat_ind with
   | base =>
      simp
   | step n' _IH =>
      simp


def nat_ind2
  (P : ℕ → Prop)
  (zero : P 0)
  (one : P 1)
  (step : ∀ n, P n → P (n + 2)) : ∀ n, P n :=
  λ n =>
    match n with
    | 0 => zero
    | 1 => one
    | n' + 2 => step n' (nat_ind2 P zero one step n')

lemma evenb_sound : ∀ n, evenb n = true → even n := by
  intros n
  induction n using nat_ind2 with
  | zero =>
    simp [evenb]
    constructor
  | one =>
    simp [evenb]
  | step n' IH =>
    simp [evenb]
    intros H
    constructor
    apply IH
    assumption

lemma evenb_complete : ∀ n, even n → evenb n = true := by
  intros n H
  induction H with
  | zero =>
    simp [evenb]
  | succ n' H IHn' =>
    simp [evenb]
    assumption

lemma even_twice (n : ℕ) : even (2 * n) := by
  induction n with
  | zero =>
    simp [Nat.mul_zero]
    exact even.zero
  | succ n' IH =>
    simp [Nat.mul_succ, Nat.succ_eq_add_one]
    exact even.succ _ IH

lemma even_add (n m : ℕ) : even n → even m → even (n + m) := by
  intro hn hm
  induction hn with
  | zero =>
    simp [Nat.zero_add]
    exact hm
  | succ n' hn_even ih_n' =>
    rw [Nat.add_assoc]
    rw [Nat.add_comm 2 m]
    exact even.succ (n' + m) ih_n'

lemma even_inv (n : ℕ) :
  even n ↔ n = 0 ∨ (∃ m, n = m + 2 ∧ even m) := by
  constructor
  · intro h
    cases h with
    | zero => exact Or.inl rfl
    | succ m hm =>
      exact Or.inr ⟨m, rfl, hm⟩
  · intro h
    cases h with
    | inl h0 =>
      rw [h0]
      exact even.zero
    | inr hex =>
      cases hex with
      | intro m hex2 =>
        cases hex2 with
        | intro heq hm =>
          rw [heq]
          exact even.succ _ hm


section EVEN_MUTUAL
  mutual
    inductive Even1 : ℕ → Prop where
    | zero : Even1 0
    | succ : ∀ n, Odd1 n  → Even1 (n + 1)

    inductive Odd1 : ℕ → Prop where
    | succ : ∀ n, Even1 n → Odd1 (n + 1)
  end

  mutual
    def even' : ℕ → Bool
    | 0 => true
    | n + 1 => odd' n

    def odd' : ℕ → Bool
    | 0 => false
    | n + 1 => even' n
  end


  mutual
    lemma even'_sound (n : ℕ)
      : even' n = true → Even1 n  := by
      cases n with
      | zero =>
        intros _H
        apply Even1.zero
      | succ n' =>
        intros H
        simp [even'] at H
        apply Even1.succ
        apply odd'_sound ; assumption

    lemma odd'_sound (n : ℕ)
      : odd' n = true → Odd1 n := by
      cases n with
      | zero =>
        simp [odd'] at *
      | succ n' =>
        intros H
        simp [odd'] at H
        apply Odd1.succ
        apply even'_sound ; assumption
  end
end EVEN_MUTUAL

section EVEN_PROP
  def even_alt (n : ℕ) : Prop :=
    ∃ m, n = 2 * m

  theorem even_even_alt (n : ℕ)
    : even n → even_alt n := by
    intros H
    induction H with
    | zero =>
      exists 0
    | succ n' _Hn' IHn' =>
      rcases IHn' with ⟨ m , Heq ⟩
      rw [Heq]
      exists (m + 1)

  theorem even_alt_even (n : ℕ)
    : even_alt n → even n := by
    intros H
    rcases H with ⟨ m , Heq ⟩
    rw [Heq]
    apply even_twice
end EVEN_PROP

-- * predicado de pertencer a uma lista

section IN
  variable {A : Type}
/-
-------------- (Here)
x ∈ (x :: xs)

x ∈ ys
---------------(There)
x ∈ (y :: ys)
-/


  inductive In (x : A) : List A → Prop where
  | Here : ∀ xs, In x (x :: xs)
  | There : ∀ y ys, In x ys → In x (y :: ys)

  def member (x : ℕ)(xs : List ℕ) : Bool :=
    match xs with
    | [] => false
    | (y :: ys) =>
      match Nat.decEq x y with
      | isFalse _ => member x ys
      | isTrue _ => true

  lemma member_sound (x : ℕ)(xs : List ℕ)
    : member x xs = true → In x xs := by
    induction xs with
    | nil =>
      intros H
      simp [member] at H
    | cons x' xs' IH =>
      intros H
      simp [member] at H
      split at H
      ·
        apply In.There
        apply IH
        exact H
      ·
        have H1 : x = x' := by assumption
        rw [H1]
        apply In.Here

  lemma member_complete (x : ℕ) xs
    : In x xs → member x xs = true := by
  intros h
  induction h with
  | Here xs =>
    simp [member]
    split
    · contradiction
    · rfl
  | There y ys _ih =>
    simp [member]
    split
    · assumption
    · rfl


  lemma In_app_right (x : ℕ) xs ys
    : In x xs → In x (xs ++ ys) := by
  intros h
  induction h with
  | Here xs' =>
    apply In.Here
  | There y ys' ih =>
    apply In.There
    assumption

  lemma In_app_left (y : ℕ) ys xs
    : In y ys → In y (xs ++ ys) := by
  intros h
  induction xs with
  | nil =>
    simp [List.nil_append]
    exact h
  | cons x xs' ih =>
    apply In.There
    exact ih


  lemma In_app_inv (x : ℕ) xs ys
    : In x (xs ++ ys) → In x xs ∨ In x ys := by
  intros h
  induction xs with
  | nil =>
    simp at h
    exact Or.inr h
  | cons x' xs' ih =>
    cases h with
    | Here _ =>
      apply Or.inl
      apply In.Here
    | There y ys' h' =>
      specialize ih h'
      cases ih with
      | inl l => exact Or.inl (In.There _ _ l)
      | inr r => exact Or.inr r
end IN
