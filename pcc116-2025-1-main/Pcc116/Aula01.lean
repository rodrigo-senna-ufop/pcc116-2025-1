import Mathlib.Tactic.Basic

section PropLogic

  variable (A B C : Prop)

  /-
  \   G U {A} |- B
  \  --------------{->I}     intros
  \   G |- A -> B
  \
  \      H1              H2
  \  G |- A -> B      G |- A
  \  -----------------------  apply H1 ; exact H2
  \      G |- B
  \
  \   A <- G
  \   -------{id}            exact nomeHipotese / assumption
  \   G |- A
  \ -/

  theorem first_theorem
    : (A → B) → A → B := by
    intros H
    exact H




-- *** Exercício 1.

  lemma ex1 : A → B → A := by
    intros H1 H2
    exact H1

  /-
  \
     B -> C          B
     ------------------
            C

  \ -/


  lemma ex2 : (A → B) → (B → C) → A → C := by
    intros H1 H2 H3
    apply H2
    apply H1
    assumption

-- ** Conjunção
-- par

/-
\
\   A              B
\  -----------------{∧ I}       apply And.intro / constructor
\      A ∧ B
\
\
\   A ∧ B
\   ------ {∧ E}               obtain / rcases
\     A
\ -/

  theorem and_comm1 : (A ∧ B) → (B ∧ A) := by
    intros H
    constructor
    ·
      obtain ⟨ H1 , H2 ⟩ := H
      exact H2
    ·
      rcases H with ⟨ H1 , H2 ⟩
      assumption

  theorem and_assoc1
    : A ∧ (B ∧ C) → (A ∧ B) ∧ C := by
      intros H
      obtain ⟨ H1, H2 , H3 ⟩ := H
      constructor
      ·
        constructor
        ·
          assumption
        ·
          assumption
      ·
        assumption

-- *** Exercício 3

  theorem ex3 : (A ∧ B) ∧ C -> A ∧ (B ∧ C) := by
    intros H
    obtain ⟨ H1 ⟩ := H
    obtain ⟨ H2 , H3 ⟩ := H1
    constructor
    exact H2
    .
      constructor
      .
        assumption
      .
        assumption

-- *** Exercício 4

  theorem ex4 : ((A ∧ B) → C) → (A → B → C) := by
    intros H1 H2 H3
    apply H1
    constructor
    .
      assumption
    .
      assumption


-- *** Exercício 5

  theorem ex5 : (A → B → C) → ((A ∧ B) → C) := by
    intros H1 H2
    apply H1
    obtain ⟨ H3 , H4 ⟩ := H2
    exact H3
    obtain ⟨ H3 , H4 ⟩ := H2
    exact H4


-- *** Exercício 6

  theorem ex6 : ((A → B) ∧ (A → C)) → A → (B ∧ C) := sorry



  -- A ↔ B = (A → B) ∧ (B → A)

  lemma iff_demo : (A ∧ B) ↔ (B ∧ A) := by
    constructor
    ·
      intros H
      obtain ⟨ H1, H2 ⟩ := H
      constructor
      ·
        assumption
      ·
        assumption
    ·
      intros X
      obtain ⟨ H1, H2 ⟩ := X
      constructor
      · assumption
      · assumption

-- Negação
-- ¬ A ≃ A → False

  lemma modus1 : ((A → B) ∧ ¬ B) → ¬ A := by
    intros H
    rcases H with ⟨ H1 , H2 ⟩
    intros H3
    apply H2
    apply H1
    exact H3

  lemma contraEx : A → ¬ A → B := by
    intros Ha Hna
    contradiction

/-
\       A
\   ---------               left
\     A ∨ B
\
\       B
\   ---------               right
\     A ∨ B
\
\       H             H1             H2
\   Γ ⊢ A ∨ B    Γ ∪ {A} ⊢ C    Γ ∪ {B} ⊢ C
\   ----------------------------------------  rcases H with H1 | H2
\            Γ ⊢ C
\ -/

  lemma or_comm1 : (A ∨ B) → (B ∨ A) := by
    intros H
    rcases H with H1 | H2
    ·
      right
      exact H1
    ·
      left
      exact H2

  lemma orex2 : ((A ∨ B) ∧ ¬ A) → B := by
    intros H
    rcases H with ⟨ H1 | H2 , H3 ⟩
    · contradiction
    · assumption

-- Exercício 8

  lemma ex8 : (A ∨ (B ∧ C)) → (A ∨ B) ∧ (A ∨ C) := sorry

-- Lógica clássica

  open Classical

  -- excluded middle

  #check (em A)

  lemma doubleNeg : ¬ (¬ A) ↔ A := by
    constructor
    ·
      intros H
      rcases (em A) with H1 | H2
      ·
        assumption
      ·
        contradiction
    ·
      intros H H1
      contradiction

-- Exercício 9

  lemma ex9 : (¬ B → ¬ A) → (A → B) := sorry

-- Exercício 10

  lemma ex10 : ((A → B) → A) → A := sorry

end PropLogic
