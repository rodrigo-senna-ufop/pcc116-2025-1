import Mathlib.Tactic.Basic

-- predicate logic

section PREDICATE_LOGIC
  variable {U : Type}
           {u : U}
           {P Q R : U → Prop}

  /-
  \     Γ ⊢ P x   x ∉ fv(Γ)
  \    ---------------------    intros
  \      Γ ⊢ ∀ x, P x
  \
  \
  \           H
  \     Γ ⊢ ∀ x, P x
  \     -------------
  \       Γ ⊢ P a
  \
  \     have Hx : P a := by
  \       apply H
  \
  \ -/


  lemma forall_and1
    : (∀ x, P x ∧ Q x) →
      ((∀ x, P x) ∧ (∀ x, Q x)) := by
    intros H
    constructor
    ·
      intros a
      have H1 : P a ∧ Q a := by
        apply H
      rcases H1 with ⟨ H2 , H3 ⟩
      exact H2
    ·
      intros a
      have H1 : P a ∧ Q a := by
        apply H
      rcases H1 with ⟨ H2 , H3 ⟩
      exact H3

  /-
  \      Γ ⊢ P a, para algum a
  \   -------------------------      exists a
  \      Γ ⊢ ∃ x, P x
  \
  \        H                 Ha
  \   Γ ⊢ ∃ x, P x     Γ ∪ {P a} ⊢ Q  a ∉ Γ
  \   ------------------------------------
  \            Γ ⊢ Q
  \
  \   rcases H with ⟨ a , Ha ⟩
  \
  \ -/

  lemma exists_or1
    : (∃ x, P x ∨ Q x) →
      (∃ x, P x) ∨ (∃ y, Q y) := by
    intros H
    rcases H with ⟨ a, H1 | H2 ⟩
    ·
      left
      exists a
    ·
      right
      exists a


--  ** Exercício 1.

  lemma forall_implies
    : (∀ x, P x → Q x) →
      (∀ y, Q y → R y) →
      (∀ z, P z → R z) := by

    intros H1 H2 a H3
    apply H2 a
    apply H1 a
    exact H3


-- ** Exercício 2.

  lemma exists_and1
    : (∃ x, P x ∧ Q x) →
      (∃ x, P x) ∧ (∃ y, Q y) := by
    intro H
    rcases H with ⟨a, ⟨H1, H2⟩⟩
    constructor
    · exists a
    · exists a


end PREDICATE_LOGIC
