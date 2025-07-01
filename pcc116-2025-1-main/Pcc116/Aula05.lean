-- 2. Listas encadeadas (tipo List na biblioteca)

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.Linarith

-- List

inductive list (A : Type) where
| nil : list A
| cons : A → list A → list A
deriving Repr
-- cons 1 (cons 2 (cons 3 nil))

open list --

-- length
-- implicito {A : Type}
def size {A : Type}(xs : list A) : ℕ :=
  match xs with
  | nil => 0
  | cons _ xs => Nat.succ (size xs)

-- repeat
def listRepeat {A : Type}(n : ℕ)(x : A) : list A :=
  match n with
  | Nat.zero => nil
  | Nat.succ n' => cons x (listRepeat n' x)

-- append
def cat {A : Type}(xs ys : list A) : list A :=
  match xs with
  | nil => ys
  | cons x xs' => cons x (cat xs' ys)

infixl:60 " .++. " => cat

def reverse {A : Type}(xs : list A) : list A :=
  match xs with
  | nil => nil
  | cons x' xs' => reverse xs' .++. (cons x' nil)

def rev {A : Type}(xs ac : list A) : list A :=
  match xs with
  | nil => ac
  | cons x' xs' => rev xs' (cons x' ac)

#check Nat.succ_add

lemma cat_size {A}(xs ys : list A) :
  size (xs .++. ys) = size xs + size ys := by
  induction xs with
  | nil =>

simp [cat, size]
  | cons x xs' ih =>

    simp [cat, size]
    rw [ih]
    rw [Nat.succ_add]


lemma listRepeat_size {A}(x : A)(n : ℕ) :
  size (listRepeat n x) = n := by
  induction n with
  | zero =>

    simp [listRepeat, size]
  | succ n' ih =>

    simp [listRepeat, size]
    rw [ih]


lemma reverse_size {A}(xs : list A) :
  size (reverse xs) = size xs := by
  induction xs with
  | nil =>

    simp [reverse, size]
  | cons x xs' ih =>

    simp [reverse, size, cat]
    rw [cat_size, ih]
    simp [size]


lemma cat_assoc {A}(xs ys zs : list A)
  : xs .++. ys .++. zs = xs .++. (ys .++. zs) := by
  induction xs with
  | nil =>

    simp [cat]
  | cons x xs' ih =>

    simp [cat]
    rw [ih]


lemma cat_nil_r {A}(xs : list A)
  : xs .++. nil = xs := by
  induction xs with
  | nil =>

    simp [cat]
  | cons x xs' ih =>

    simp [cat]
    rw [ih]


lemma reverse_cat {A}(xs ys : list A) :
  reverse (xs .++. ys) = reverse ys .++. reverse xs := by
  induction xs with
  | nil =>
    simp [reverse, cat]
    simp [reverse, cat_nil_r]
  | cons x xs' ih =>
    simp [reverse, cat]
    rw [ih]
    rw [cat_assoc]


lemma reverse_reverse {A}(xs : list A) :
  reverse (reverse xs) = xs := by
  induction xs with
  | nil =>
    simp [reverse]
  | cons x xs' ih =>
    simp [reverse, cat]
    rw [reverse_cat]
    simp [reverse, cat]
    rw [ih]


lemma reverse_rev {A}(xs : list A) :
  reverse xs = rev xs nil := by
  induction xs with
  | nil =>
    simp [reverse, rev]
  | cons x xs' ih =>
    simp [reverse, rev]
    rw [ih]


section MAP
  variable {A B C : Type}

  -- high-order function

  def map (f : A → B)(xs : list A) : list B :=
    match xs with
    | nil => nil
    | cons y ys => cons (f y) (map f ys)


  lemma map_id (xs : list A)
    : map (λ x => x) xs = xs := by
    induction xs with
    | nil =>
      simp [map]
    | cons y ys ih =>
      simp [map]
      rw [ih]


  lemma map_app (xs ys : list A)(f : A → B)
    : map f (xs .++. ys) = (map f xs) .++. (map f ys) := by
    induction xs with
    | nil =>
      simp [map, cat]
    | cons x xs' ih =>
      simp [map, cat]
      rw [ih]


  lemma map_compose (f : A → B)(g : B → C)(xs : list A)
    : map (λ x => g (f x)) xs = (map g (map f xs)) := by
    induction xs with
    | nil =>
    simp [map]
    | cons x xs' ih =>
      simp [map]
      rw [ih]


end MAP

section FILTER
  variable {A : Type}

  def filter (p : A → Bool)
             (xs : list A) : list A :=
    match xs with
    | nil => nil
    | cons y ys =>
      if p y then cons y (filter p ys)
      else filter p ys

  lemma filter_cat (p : A → Bool)
                   (xs ys : list A) :
    filter p xs .++. filter p ys =
    filter p (xs .++. ys) := by
    induction xs with
    | nil =>
      simp [filter, cat]
    | cons x xs' ih =>
      simp [filter, cat]
      split_ifs with h
      · simp [cat]
        rw [ih]
      · exact ih


  lemma filter_reverse (p : A → Bool)
                       (xs : list A) :
    reverse (filter p xs) =
    filter p (reverse xs) := by
    induction xs with
    | nil =>
      simp [filter, reverse]
    | cons x xs' ih =>
      simp [filter, reverse, cat]
      split_ifs with h
      · simp [reverse, cat]
        rw [ih]
        rw [filter.eq_def, cat.eq_def]
        simp [h]
      · simp [reverse, cat]
        rw [ih]
        simp [filter, h]


  lemma filter_size (p : A → Bool)(xs : list A) :
    size (filter p xs) ≤ size xs := by
    induction xs with
    | nil =>
    simp [filter, size]
    | cons x xs' ih =>
    simp [filter, size]
    split_ifs with h
    · simp [size]

      exact ih
    · exact Nat.le_succ_of_le ih


  lemma filter_and (p q : A → Bool)
                   (xs : list A) :
    filter p (filter q xs) =
    filter (λ x => p x && q x) xs := by
    induction xs with
    | nil =>
      simp [filter]
    | cons x xs' ih =>
      simp [filter]
      split_ifs with hq hp hpq
      · simp [hp] at *
        exact congrArg (cons x) ih
      · simp [hp] at *
        exact ih
      · simp [hpq] at *
        exact ih
      · simp [hpq] at *

end FILTER


section MEMBERSHIP
  variable {A : Type}

  def member [DecidableEq A](x : A)
                            (xs : list A) : Bool :=
    match xs with
    | nil => false
    | cons y ys => match decEq x y with
                   | isFalse _ => member x ys
                   | isTrue _ => true

  lemma member_cat_true_left [DecidableEq A]
                             (x : A)
                             (xs ys : list A) :
    member x xs = true →
    member x (xs .++. ys) = true := by
  induction xs with
  | nil =>
    simp [member]
  | cons y ys' ih =>
    simp [member, cat]
    cases decEq x y with
    | isTrue heq => simp [heq]
    | isFalse hne =>
      intro h
      apply ih h

  lemma member_cat_true_right [DecidableEq A](x : A)(xs ys : list A) :
    member x ys = true → member x (xs .++. ys) = true := by
  induction xs with
  | nil =>
    simp [member, cat]
  | cons y ys' ih =>
    simp [member, cat]
    cases decEq x y with
    | isTrue heq => simp [heq]
    | isFalse hne =>
      intro h
      apply ih h

  lemma member_reverse [DecidableEq A](x : A)(xs : list A) :
    member x xs = member x (reverse xs) := by
  induction xs with
  | nil =>
    simp [member, reverse]
  | cons y ys ih =>
    simp [member, reverse, cat]
    cases decEq x y with
    | isTrue heq =>
      simp [heq]
      apply member_cat_true_right
      simp [member, heq]
    | isFalse hne =>
      simp [hne]
      rw [ih]

      apply propext
      apply Iff.intro
      · intro h
        exact member_cat_true_left x (reverse ys) [y] h
      · intro h
        simp [member] at h
        cases decEq x y with
        | isTrue hxy => contradiction
        | isFalse _ => exact h

end MEMBERSHIP
