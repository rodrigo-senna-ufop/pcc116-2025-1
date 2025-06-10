import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic

-- # Interagindo com o Lean

-- Avaliando expressões

#eval 2 * 4

-- Obtendo tipo de expressões

#check String.append
#check not

-- # Funções e definições

def sayHello s :=
  String.append "Hello " (String.append s "!")

#check sayHello

def helloLean := sayHello "Lean"

#eval helloLean

def maximum (n m : ℕ) : ℕ :=
  if n > m then n else m

#eval maximum (2 + 4) (2 * 8)

-- # Tipos
-- level polymorphism
-- estratificação de tipos
-- Bool : Type_0 : Type_1 : Type_2 ...
--
-- Paradoxo Russell
--
-- {{1}, ∅}
--
-- Conjuntos pode ser elemento de si próprio
--
-- A = {X | X ∉ X}
--
-- A ∈ A ∨ A ∉ A
-- 1. A ∈ A ⇒ A ∉ A  --
-- 2. A ∉ A ⇒ A ∈ A
-- Paradoxo.

#check Bool
#check Type
#check Type 1

def Bla : Type := ℕ -- Bla e Nat são tipos diferentes

-- isso leva a um erro

-- def theAnswer : Bla := 42

-- forma correta

abbrev Natural := Nat

def Answer : Natural := 42

-- Registros

structure Point where
  x : Nat
  y : Nat


def origin : Point := {x := 0 , y := 0}
def origin1 : Point := Point.mk 0 0


-- NomeRegistro.mk arg1 ... argn

/- #eval origin -/
-- Se a : Point, a.x a.y

def addPoints (a b : Point) : Point :=
  {x := a.x + b.x, y := a.y + b.y}

def addPoint (a b : Point) : Point :=
  match a, b with
  | Point.mk x1 y1, Point.mk x2 y2 =>
    Point.mk (x1 + x2) (y1 + y2)

-- #Tipos de dados algébricos

-- 0. Enumerações

inductive WeekDay where
| Sunday : WeekDay
| Monday : WeekDay
| Tuesday : WeekDay
| Wednesday : WeekDay
| Thursday : WeekDay
| Friday : WeekDay
| Saturday : WeekDay
deriving Repr

-- Funções totais / funções parciais.
-- Verificação de totalidade
--  1. Casamento de padrão exaustivo
--  2. Funções recursivas devem sempre terminar.
--  2.1. Chamadas recursivas devem ser feitas somente sobre
--       argumentos sintaticamente "menores".

-- NomeTipo.Construtor
-- open NomeTipo in

def nextDay (d : WeekDay) : WeekDay :=
  open WeekDay in
  match d with
  | Sunday => Monday
  | Monday => Tuesday
  | Tuesday => Wednesday
  | Wednesday => Thursday
  | Thursday => Friday
  | Friday => Saturday
  | Saturday => Sunday

#eval nextDay WeekDay.Thursday

def prevDay (d : WeekDay) : WeekDay :=
  match d with
  | WeekDay.Sunday => WeekDay.Saturday
  | WeekDay.Monday => WeekDay.Sunday
  | WeekDay.Tuesday => WeekDay.Monday
  | WeekDay.Wednesday => WeekDay.Tuesday
  | WeekDay.Thursday => WeekDay.Wednesday
  | WeekDay.Friday => WeekDay.Thursday
  | WeekDay.Saturday => WeekDay.Friday

-- análise de casos.

-- igualdade
--- Proposicional: forall x, x = x
---- 1 + 1 = 2
---- 2 = 2

lemma nextPrevId (d : WeekDay)
  : prevDay (nextDay d) = d := by
  cases d <;> simp [nextDay, prevDay]


lemma prevNextId (d : WeekDay)
  : nextDay (prevDay d) = d := by
  cases d <;> simp [nextDay, prevDay]

-- definição de boolean (presente na biblioteca)

/-
inductive Bool where
| true : Bool
| false : Bool
-/

def negb (x : Bool) : Bool :=
  match x with
  | true => false
  | _    => true

def andb (x y : Bool) : Bool :=
  match x with
  | true => y
  | false => false

def orb (x y : Bool) : Bool :=
  match x with
  | false => y
  | true => true

-- a .&. b .&. c = (a .&. b) .&. c
infixl:65 " .&. " => andb
infixl:80 " .|. " => orb

#eval true .&. true

lemma negb_inv (b : Bool) : negb (negb b) = b := by
  cases b <;> simp [negb]


lemma andb_comm b1 b2 : b1 .&. b2 = b2 .&. b1 := by
  cases b2 <;> cases b1 <;> simp [andb]

-- Exercício 1.

lemma orb_comm b1 b2 : b1 .|. b2 = b2 .|. b1 := by
  cases b1 <;> cases b2 <;> simp [orb]

lemma andb_assoc b1 b2 b3 :
  b1 .&. b2 .&. b3 = b1 .&. (b2 .&. b3) := by
  cases b1 <;> cases b2 <;> cases b3 <;> simp [andb]

lemma andb_orb b1 b2 : b1 .&. b2 = b1 .|. b2 → b1 = b2 := by
  intro h
  cases b1 <;> cases b2 <;> simp [andb, orb] at h
  all_goals (try (exact rfl))

lemma deMorgan1 b1 b2 :
  negb (b1 .&. b2) = (negb b1) .|. (negb b2) := by
  cases b1 <;> cases b2 <;> simp [negb, andb, orb]

lemma deMorgan2 b1 b2 :
  negb (b1 .|. b2) = (negb b1) .&. (negb b2) := by
  cases b1 <;> cases b2 <;> simp [negb, andb, orb]

/-
# Exercício: Modelando penalidade por atraso em entregas

O objetivo desta sequência de exercícios é a modelagem
de um sistema de penalidade por atraso em entregas e
a demonstração de alguns fatos simples sobre esse sistema.

Vamos considerar um sistema de notas em que teremos
conceitos e um modificador. O seguinte tipo modela as
diferentes possibilidades de conceitos para a nota.
-/

inductive letter :=
| A | B | C | D | E | F
deriving Repr


-- Modificadores são utilizados para representar
-- diferentes escalas de notas: A + , A ou A -

inductive modifier :=
| Plus | Plain | Minus
deriving Repr

-- Definição de uma nota

inductive grade :=
| Grade : letter → modifier → grade
deriving Repr

/-
Uma parte importante é a comparação entre notas.
Para representar os possíveis resultados de
comparação, vamos criar o tipo cmp
-/

inductive cmp1 :=
| Lt | EQ | Gt
deriving Repr

open letter
open modifier
open grade
open cmp1

-- Exercício 1. Comparando letras
-- Desenvolva a função

def letter_cmp (l1 l2 : letter) : cmp1 :=
  match l1, l2 with
  | A, A => EQ | A, _ => Gt
  | B, A => Lt | B, B => EQ | B, _ => Gt
  | C, A => Lt | C, B => Lt | C, C => EQ | C, _ => Gt
  | D, F => Gt | D, E => Gt | D, D => EQ | D, _ => Lt
  | E, F => Gt | E, E => EQ | E, _ => Lt
  | F, F => EQ | F, _ => Lt


/-
que deve comparar notas considerando que a maior é A
e a menor é F.
-/

-- Exercício 2. Prove o seguinte resultado

theorem letter_cmp_refl l : letter_cmp l l = EQ := by
 cases l <;> rfl


-- Exercício 3. Desenvolva a função

/-def modifier_cmp (m1 m2 : modifier) : cmp1 :=
  match m1, m2 with
  | Plus, Plus => EQ | Plus, Minus => Gt
  | Plus, Plain => Gt | Plain, Plus => Lt
  | Plain, Minus => Gt | Minus, Plain => Lt
  | Minus, Minus => EQ | Minus, Plus => Lt
-/
def modifier_cmp : modifier → modifier → cmp1
| Plus, Plus => EQ | Plus, _ => Gt
| Plain, Plus => Lt | Plain, Plain => EQ | Plain, Minus => Gt
| Minus, Minus => EQ | Minus, _ => Lt


/-
que deve comparar modificadores considerando que
Plus > Plain > Minus.
-/

-- Exercício 4. Desenvolva a função

def grade_cmp (g1 g2 : grade) : cmp1 :=
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 =>
    match letter_cmp l1 l2 with
    | EQ => modifier_cmp m1 m2
    | other => other
/-
def grade_cmp : grade → grade → cmp1
  Grade l1 m1, Grade l2 m2 =>
    match letter_cmp l1 l2 with
    EQ => modifier_cmp m1 m2
    other => other
-/

/-
A comparação de notas deve proceder da seguinte forma:
Se o conceito (letter) não for igual, você deverá
retornar o resultado da compração de conceitos. Para
conceitos iguais, compara-se o modificador da nota,
retornando-o como resultado.
-/

-- Exercício 5. Desenvolva a função

def lower_letter (l : letter) : letter :=
  match l with
  | A => B | B => C | C => D | D => E | E => F | F => F



/-
Que retorna o conceito imediatamente abaixo do
fornecido como argumento. Note que não há conceito
abaixo de F, logo lower_letter F = F. Em seguida,
prove o seguinte lema:
-/

lemma lower_letter_F : lower_letter F = F := by
  rfl


-- Exercício 6. Prove o seguinte teorema

theorem lower_letter_lowers l :
  letter_cmp F l = Lt →
  letter_cmp (lower_letter l) l = Lt := by
  intro h
  cases l <;> simp [lower_letter, letter_cmp] at * <;> assumption

theorem lower_letter_lowers1 l :
  letter_cmp F l = Lt →
  letter_cmp (lower_letter l) l = Lt := by
  intro h
  cases l
  case A =>
    simp [letter_cmp, lower_letter] at *
  case B =>
    simp [letter_cmp, lower_letter] at *
  case C =>
    simp [letter_cmp, lower_letter] at *
  case D =>
    simp [letter_cmp, lower_letter] at *
  case E =>
    simp [letter_cmp, lower_letter] at *
  case F =>
    simp [letter_cmp] at h

/-
que formaliza a propriedade que
se a letra passada como argumento é maior
que F então o resultado de lower_letter será
menor que a letra atual.
-/

-- Exercício 7. Desenvolva a função

def lower_grade (g : grade) : grade :=
  match g with
  | Grade l Plus => Grade (lower_letter l) Plain
  | Grade l Plain => Grade (lower_letter l) Minus
  | Grade l Minus =>
    match lower_letter l with
    | l' => Grade l' Plus
/-
def lower_grade : grade → grade
| Grade l Plus => Grade l Plain
| Grade l Plain => Grade l Minus
| Grade l Minus =>
  match lower_letter l with
  | l' => Grade l' Plus
-/

/-
que a partir de uma nota g fornecida como argumento
produz a nota imediatamente inferior a ela.
Em seguida, prove o seguinte fato sobre sua definição:
-/

--lemma F_Minus_lowest_grade :
--  lower_grade (Grade F Minus) = Grade F Minus := sorry

--lemma F_Minus_lowest_grade : lower_grade (Grade F Minus) = Grade F Minus := by rfl

-- Exercício 8. Prove o seguinte teorema que formaliza
-- que se uma nota passada para lower_grade é maior que
-- F-, então o resultado de lower_grade será uma nota
-- menor que a fornecida como argumento.
theorem lower_grade_lowers (g : grade) :
  grade_cmp (Grade F Minus) g = Lt →
  grade_cmp (lower_grade g) g = Lt := by
  intro h
  cases g with
  | Grade l m =>
    cases l with
    | A =>
      cases m with
      | Plus =>
        -- Goal: grade_cmp (Grade B Plain) (Grade A Plus) = Lt
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        -- After dsimp, goal should be `Lt = Lt`
        rfl
      | Plain =>
        -- Goal: grade_cmp (Grade B Minus) (Grade A Plain) = Lt
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
      | Minus =>
        -- Goal: grade_cmp (Grade B Plus) (Grade A Minus) = Lt
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
    | B =>
      cases m with
      | Plus =>
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
      | Plain =>
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
      | Minus =>
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
    | C =>
      cases m with
      | Plus =>
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
      | Plain =>
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
      | Minus =>
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
    | D =>
      cases m with
      | Plus =>
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
      | Plain =>
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
      | Minus =>
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
    | E =>
      cases m with
      | Plus =>
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
      | Plain =>
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
      | Minus =>
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        rfl
    | F =>
      cases m with
      | Plus =>
        -- g = Grade F Plus. lower_grade g = Grade F Plain
        -- Goal: grade_cmp (Grade F Plain) (Grade F Plus) = Lt
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        -- Expected: `Lt = Lt` (since modifier_cmp Plain Plus = Lt)
        rfl
      | Plain =>
        -- g = Grade F Plain. lower_grade g = Grade F Minus
        -- Goal: grade_cmp (Grade F Minus) (Grade F Plain) = Lt
        dsimp [lower_grade, grade_cmp, letter_cmp, modifier_cmp]
        -- Expected: `Lt = Lt` (since modifier_cmp Minus Plain = Lt)
        rfl
      | Minus =>
        -- g = Grade F Minus.
        -- Hipótese h: grade_cmp (Grade F Minus) (Grade F Minus) = Lt
        -- Simplifica para `EQ = Lt`.
        simp only [grade_cmp, letter_cmp, modifier_cmp] at h
        -- Objetivo: grade_cmp (lower_grade (Grade F Minus)) (Grade F Minus) = Lt
        -- Simplifica para `grade_cmp (Grade F Plus) (Grade F Minus) = Lt`
        -- Simplifica para `Gt = Lt`.
        -- A hipótese `h` é falsa (`EQ = Lt`), então a implicação inteira é verdadeira.
        -- Provamos `False` usando `h`.
        exact cmp1.noConfusion h

-- Exercício 9
/-
Agora, você deverá implementar uma função que
irá aplicar sobre uma nota a penalidade por atraso
de acordo com a tabela seguinte

# Dias de atraso     Penalidade
0 - 8                 sem penalidade
9 - 16                Diminuir a nota por um passo.
17 - 20               Diminuir a nota por dois passos.
          >= 21       Diminuir a nota por três passos.
-/
-- Exemplo de comparação. Use em sua definição.
#eval 1 < 2


def penalize (days_late : Nat) (g : grade) : grade :=
  let steps :=
    if days_late ≤ 8 then 0
    else if days_late ≤ 16 then 1
    else if days_late ≤ 20 then 2
    else 3
  let rec apply_penalty (n : Nat) (g : grade) : grade :=
    match n with
    | 0 => g
    | Nat.succ n' => apply_penalty n' (lower_grade g)
   apply_penalty steps g
