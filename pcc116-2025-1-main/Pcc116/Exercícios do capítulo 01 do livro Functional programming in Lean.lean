#eval 1 + 2

#eval 1 + 2 * 5

--#eval String.append ("Hello, ", "Lean!")

#eval String.append "Hello, " "Lean!"

#eval String.append "great " (String.append "oak " "tree")

#eval String.append "it is " (if 1 > 2 then "yes" else "no")
/-
#eval String.append "it is " (if false then "yes" else "no")
===>
String.append "it is " "no"
===>
"it is no"
-/
--#eval String.append "it is "


-------------------------------------------------------------------------------------------------
-- Exercício 1.1
-- 42 + 19
#eval 42 + 19
--String.append "A" (String.append "B" "C")
#eval String.append "A" (String.append "B" "C")
--String.append (String.append "A" "B") "C"
#eval String.append (String.append "A" "B") "C"
-- if 3 == 3 then 5 else 7
#eval if 3 == 3 then 5 else 7
-- if 3 == 4 then "equal" else "not equal"
#eval if 3 == 4 then "equal" else "not equal"
-------------------------------------------------------------------------------------------------


#eval (1 + 2 : Nat)

#eval 1 - 2

#eval (1 - 2 : Int)

#check (1 - 2 : Int)

--#check String.append ["hello", " "] "world"

def hello := "Hello"

def lean : String := "Lean"

#eval String.append hello (String.append " " lean)

def add1 (n : Nat) : Nat := n + 1

#eval add1 7

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n

def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)

#eval maximum (5 + 8) (2 * 7)
/-
===>
maximum 13 14
===>
if 13 < 14 then 14 else 13
===>
14
-/

-------------------------------------------------------------------------------------------------
-- Exercício 1.3
/-
Define the function joinStringsWith with type String -> String -> String -> String that
  creates a new string by placing its first argument between its second and third arguments.
  joinStringsWith ", " "one" "and another" should evaluate to "one, and another".
-/

def joinStringsWith (middle : String) (before : String) (after : String) : String :=
  String.append before (String.append middle after)

#eval joinStringsWith ", " "one" "and another"

/-
What is the type of joinStringsWith ": "? Check your answer with Lean.
-/

#check joinStringsWith ": "

/-
Define a function volume with type Nat → Nat → Nat → Nat that computes the volume of a
rectangular prism with the given height, width, and depth.
-/

def volume (height : Nat) (width : Nat) (depth : Nat) : Nat :=
  height * width * depth

#eval volume 2 3 4
-------------------------------------------------------------------------------------------------


def Str : Type := String

def aStr : Str := "This is a string."

def NaturalNumber : Type := Nat

--def thirtyEight : NaturalNumber := 38

def thirtyEight : NaturalNumber := (38 : Nat)

abbrev N : Type := Nat

def thirtyNine : N := 39


#check 1.2

#check -454.2123215

#check 0.0

#check 0

#check (0 : Float)

-- structure Point where
--   x : Float
--   y : Float
-- deriving Repr

structure Point where
  point ::
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin

#eval origin.x

#eval origin.y

-- def addPoints (p1 : Point) (p2 : Point) : Point :=
--   { x := p1.x + p2.x, y := p1.y + p2.y }

-- #eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }

-- def distance (p1 : Point) (p2 : Point) : Float :=
--   Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

-- #eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }

structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr

-- --#check { x := 0.0, y := 0.0 }

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

-- #check ({ x := 0.0, y := 0.0 } : Point)

-- --def zeroX (p : Point) : Point :=
-- --  { x := 0, y := p.y }

def zeroX (p : Point) : Point :=
  { x := 0, y := p.y }

def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }

-- #eval fourAndThree

-- #eval zeroX fourAndThree

-- #eval fourAndThree

-- #check Point.mk 1.5 2.8

-- #check (Point.mk)



#check (Point.x)

#check (Point.y)

#eval origin.x

#eval Point.x origin

#eval "one string".append " and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

#eval fourAndThree.modifyBoth Float.floor


-------------------------------------------------------------------------------------------------
-- Exercício 1.4
/-
Exercises
Define a structure named RectangularPrism that contains the height, width,
  and depth of a rectangular prism, each as a Float.
-/
structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

/-
Define a function named volume : RectangularPrism → Float that computes
  the volume of a rectangular prism.
-/
def volume1 (r : RectangularPrism) : Float :=
  r.height * r.width * r.depth

/-
Define a structure named Segment that represents a line segment by its
  endpoints, and define a function length : Segment → Float that computes
  the length of a line segment. Segment should have at most two fields.
-/
structure Segment where
  p1 : Point
  p2 : Point

def length (s : Segment) : Float :=
  Float.sqrt ((s.p2.x - s.p1.x)^2 + (s.p2.y - s.p1.y)^2)

/-
Which names are introduced by the declaration of RectangularPrism?
  RectangularPrism — o nome do tipo.
  RectangularPrism.mk — o construtor.
  RectangularPrism.height — função acessora para o campo height.
  RectangularPrism.width — função acessora para o campo width.
  RectangularPrism.depth — função acessora para o campo depth.
-/

/-
Which names are introduced by the following declarations of Hamster
  and Book? What are their types?
  For Hamster:
    Hamster — tipo.
    Hamster.mk — construtor.
    Hamster.name — acessor.
    Hamster.fluffy — acessor.
  For Book:
    Book — tipo.
    Book.mk — construtor.
    Book.title — acessor.
    Book.author — acessor.
    Book.price — acessor.
-/
structure Hamster where
  name : String
  fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

-------------------------------------------------------------------------------------------------
inductive Bool1 where
  | false : Bool1
  | true : Bool1

inductive Nat1 where
  | zero : Nat1
  | succ (n : Nat1) : Nat1

set_option linter.unusedVariables false
def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false

def pred : Nat → Nat
| 0     => 0
| n + 1 => n

#eval pred 5

#eval isZero Nat.zero
#eval isZero (Nat.succ 5)

inductive Sum1 (α : Type) (β : Type) : Type where
  | inl : α → Sum1 α β
  | inr : β → Sum1 α β

def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs animals




-------------------------------------------------------------------------------------------------
/-Exercises 1.6
Write a function to find the last entry in a list. It should return an Option.
-/
def List.last? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [x] => some x
  | _ :: xs' => List.last? xs'

#eval List.last? [1, 2, 3]

/-
Write a function that finds the first entry in a list that satisfies a given predicate.
  Start the definition with def List.findFirst?
  {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
-/

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
match xs with
| [] => none
| x :: xs => if predicate x then some x else findFirst? xs predicate

#eval List.findFirst? [1, 3, 5, 6, 7] (fun x => x % 2 == 0)
#eval List.findFirst? [1, 3, 5, 7] (fun x => x % 2 == 0)

/-
Write a function Prod.switch that switches the two fields in a pair for each other.
  Start the definition with def Prod.switch {α β : Type} (pair : α × β) : β × α :=
-/
def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  match pair with
  | (a, b) => (b, a)

#eval Prod.switch (1, 2)

/-
Rewrite the PetName example to use a custom datatype and compare it to the version that uses Sum.
-/
inductive PetName2
| dog : String → PetName2
| cat : String → PetName2

open PetName2

def animals1 : List PetName2 :=
  [dog "Spot", cat "Tiger", dog "Fifi", dog "Rex", cat "Floof"]

def howManyDogs1 (pets1 : List PetName2) : Nat :=
  match pets1 with
  | [] => 0
  | dog _ :: morePets1 => howManyDogs1 morePets1 + 1
  | cat _ :: morePets1 => howManyDogs1 morePets1

#eval howManyDogs1 animals1

/-
Write a function zip that combines two lists into a list of pairs.
  The resulting list should be as long as the shortest input list.
  Start the definition with def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=.
-/
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs', y :: ys' => (x, y) :: zip xs' ys'

#eval zip [1, 2, 3, 4] ["a", "b"]
#eval zip ["a", "b"] [1, 2, 3, 4]
#eval zip [true, false] [1, 2]


/-
Write a function that takes a list of pairs and returns a list of the first elements of each pair.
  Start the definition with def List.firsts {α β : Type} (xs : List (α × β)) : List α :=.
-/
def List.firsts {α β : Type} (xs : List (α × β)) : List α :=
  match xs with
  | [] => []
  | (x, _) :: xs' => x :: List.firsts xs'

#eval List.firsts [(1, "a"), (2, "b"), (3, "c")]


/-
Write a polymorphic function take that returns the first n
  entries in a list, where n is a Nat.
  If the list contains fewer than n entries,
  then the resulting list should be the entire input list.
  #eval take 3 ["bolete", "oyster"] should yield ["bolete", "oyster"],
  and #eval take 1 ["bolete", "oyster"] should yield ["bolete"].
-/
def take {α : Type} (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | 0, _ => []
  | _, [] => []
  | n + 1, x :: xs' => x :: take n xs'

#eval take 3 ["bolete", "oyster"]
#eval take 1 ["bolete", "oyster"]


/-
Using the analogy between types and arithmetic, write a function that distributes
  products over sums. In other words, it should have type α × (β ⊕ γ) → (α × β) ⊕ (α × γ).
-/
def distribute {α β γ : Type} (pair : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match pair with
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)


#eval distribute (42, (Sum.inl "hello" : Sum String Bool))
#eval distribute (42, (Sum.inr true : Sum String Bool))


/-
Using the analogy between types and arithmetic, write a function that turns
  multiplication by two into a sum. In other words, it should have type Bool × α → α ⊕ α.
-/
def double {α : Type} (pair : Bool × α) : α ⊕ α :=
  match pair with
  | (true, a) => Sum.inl a
  | (false, a) => Sum.inr a


#eval double (true, 5)
#eval double (false, 7)
#eval double (true, "Olá")
#eval double (false, "Mundo")
-------------------------------------------------------------------------------------------------
