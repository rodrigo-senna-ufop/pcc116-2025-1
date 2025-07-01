import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith


def insert1 (x : ℕ)(ys : List ℕ) : List ℕ :=
  match ys with
  | [] => [x]
  | y' :: ys' =>
    match Nat.decLe x y' with
    | isTrue _ => x :: y' :: ys'
    | isFalse _ => y' :: insert1 x ys'

def isort (xs : List ℕ) : List ℕ :=
  match xs with
  | [] => []
  | x :: xs => insert1 x (isort xs)

-- ordenada ∧ permutacao

section PERM
  variable {A : Type}

  inductive Permutation : List A → List A → Prop where
  | perm_nil : Permutation [] []
  | perm_skip : ∀ x l l',
      Permutation l l' → Permutation (x::l) (x::l')
  | perm_swap : ∀ x y l,
      Permutation (y::x::l) (x::y::l)
  | perm_trans : ∀ l l' l'',
      Permutation l l' →
      Permutation l' l'' →
      Permutation l l''

  infix:60 " ~ " => Permutation

  -- Exercício: prove o lema de inversão para permutações
  lemma Perm_inv (xs ys : List A)
  : xs ~ ys →
    (xs = [] ∧ ys = []) ∨
    (∃ x xs' ys', xs = x :: xs' ∧ ys = x :: ys' ∧ xs' ~ ys') ∨
    (∃ x y zs, xs = x :: y :: zs ∧ ys = y :: x :: zs) ∨
    (∃ zs, xs ~ zs ∧ zs ~ ys) := by
    intro h_perm
    induction h_perm with
    | perm_nil =>
      left; exact ⟨rfl, rfl⟩
    | perm_skip x l l' h_perm_l_l' ih =>
      right
      left
      use x, l, l'
    | perm_swap x y l =>
      right
      right
      left
      use y, x, l
    | perm_trans l l' l'' h_perm_l_l' h_perm_l'_l'' ih_l_l' ih_l'_l'' =>
      right
      right
      right
      use l'

  -- P(nil) -> (∀ x xs, P x → P (x :: xs)) -> ∀ xs, P xs

  lemma perm_refl (xs : List A) : xs ~ xs := by
    induction xs with
    | nil =>
      constructor
    | cons y ys IHys =>
      constructor
      exact IHys

  lemma perm_length_eq (xs ys : List A)(p : xs ~ ys)
    : List.length xs = List.length ys := by
    induction p
    ·
      rfl
    ·
      rename_i x l1 l2 H1 H2
      simp [H2]
    ·
      rename_i x y zs
      simp
    ·
      rename_i l1 l2 l3 H1 H2 IH1 IH2
      simp [IH1, IH2]


  lemma length_eq_zero_nil (xs : List A)
    : List.length xs = 0 ↔ xs = [] := by
    induction xs <;> simp


  lemma perm_nil (xs : List A) :
    [] ~ xs → xs = [] := by
    intros H
    apply perm_length_eq at H
    simp [List.length] at H
    have H1 : xs.length = 0 := by aesop
    rcases (length_eq_zero_nil xs) with ⟨ H3 , H4 ⟩
    aesop



  lemma perm_symm (xs ys : List A)(p : xs ~ ys)
    : ys ~ xs := by
    induction p
    ·
      constructor
    ·
      rename_i x l1 l2 H1 H2
      constructor
      exact H2
    ·
      rename_i x y l
      constructor
    ·
      rename_i l1 l2 l3 H0 H1 H2 H3
      apply Permutation.perm_trans
      exact H3
      exact H2

end PERM

inductive Sorted : List ℕ → Prop where
| SortedNil : Sorted []
| SortedSingle : ∀ x, Sorted (x :: [])
| SortedCons : ∀ x y ys, x ≤ y →
              Sorted (y :: ys) →
              Sorted (x :: y :: ys)

lemma insertSorted (xs : List ℕ)(x : ℕ)
  : Sorted xs → Sorted (insert1 x xs) := by
    induction xs with
    | nil =>
      simp [insert1]
      intros _H
      constructor
    | cons y ys IHys =>
      intros H
      simp [insert1]
      rcases (Nat.decLe x y) with H1 | H1 <;> simp
      ·
        cases H
        case SortedSingle =>
          simp [insert1] at *
          constructor
          ·
            omega
          .
            constructor
        case SortedCons z zs H3 H2 =>
          specialize IHys H3
          revert IHys
          simp [insert1] at *
          rcases Nat.decLe x z with H4 | H4 <;> simp at *
          ·
            intros H5
            constructor <;> assumption
          ·
            intros H5
            constructor <;> (try assumption)
            omega
      ·
        constructor <;> assumption

lemma insert1Perm (xs : List ℕ)(x : ℕ)
  : (x :: xs) ~ (insert1 x xs) := by
    induction xs with
    | nil =>
      simp [insert1]
      apply perm_refl
    | cons y ys IHys =>
      simp [insert1]
      rcases Nat.decLe x y with H1 | H1 <;> simp
      ·
        have H2 : (x :: y :: ys) ~ (y :: x :: ys) := by
          constructor
        have H3 : (y :: x :: ys) ~ (y :: insert1 x ys) := by
          constructor ; exact IHys
        apply Permutation.perm_trans
        exact H2
        exact H3
      ·
        apply perm_refl


lemma isortSorted (xs : List ℕ) : Sorted (isort xs) := by
  induction xs with
  | nil => simp [isort] ; constructor
  | cons y ys IHys =>
    simp [isort ]
    apply insertSorted ; exact IHys

lemma isortPerm (xs : List ℕ) : xs ~ (isort xs) := by
  induction xs with
  | nil => simp [isort] ; constructor
  | cons y ys IHys =>
    simp [isort]
    have H2 : (y :: ys) ~ (y :: isort ys) := by
      constructor ; exact IHys
    have H3 : (y :: isort ys) ~ (insert1 y (isort ys)) := by
      apply insert1Perm
    apply Permutation.perm_trans
    exact H2
    exact H3

theorem isortCorrect (xs : List ℕ)
  : Sorted (isort xs) ∧ xs ~ (isort xs) := by
    apply And.intro
    ·
      apply isortSorted
    ·
      apply isortPerm
