
inductive BobStudiesAtUVa
| attendsClasses
| paidTuition

inductive MaryStudiesAtUVa
| attendsClasses
| paidTuition --these are proofs (?)

inductive MarkoStudiesAtUVa
--the fact that there are no proofs means that it is not
--true that Marko studies at UVa

def neg (α : Type) := α → Empty

example : neg MarkoStudiesAtUVa :=
  λ m : MarkoStudiesAtUVa => nomatch m
--0 values of this type so there are no cases to consider at all
--this is what nomatch means

inductive BobStudiesAtUVaAndMaryStudiesAtUVa
| and (b : BobStudiesAtUVa) (m : maryStudiesAtUVA)

def b : BobStudiesAtUVa := BobStudiesAtUVa.paidTuition
def m: MaryStudiesAtUVa := MaryStudiesAtUVa.paidTuition

example : BobStudiesAtUVaAndMaryStudiesAtUVa :=
    BobStudiesAtUVaAndMaryStudiesAtUVa.and b m

inductive BobStudiesAtUVaOrMaryStudiesAtUVa
| left (b : BobStudiesAtUVa)
| right (m : MaryStudiesAtUVa)

--                proposition
example : BobStudiesAtUVaOrMaryStudiesAtUVa :=
              --proof
  BobStudiesAtUVaOrMaryStudiesAtUVa.left b

/-!
Let's generalize a bit
-/

inductive MyAnd (α β : Type) : Type
| mk (a: α) (b : β)

inductive MyOr (α β : Type) : Type
| inl (a : α)
| inr (b : β)

example : MyAnd BobStudiesAtUVa MaryStudiesAtUVa :=
  MyAnd.mk b m

example: MyOr BobStudiesAtUVa MaryStudiesAtUVa :=
  MyOr.inl b

example: MyOr BobStudiesAtUVa MaryStudiesAtUVa :=
  MyOr.inr m

def MyNot (α : Type) := α → Empty

example : MyNot BobStudiesAtUVa := λ b => _ --can't complete this proof - it's not true
example : MyNot MarkoStudiesAtUVa := λ MarkoStudiesAtUVa => nomatch MarkoStudiesAtUVa --0 cases to consider

#check (@Prod) --use for and
#check (1, "Hello")

example : Prod BobStudiesAtUVa MaryStudiesAtUVa := Prod.mk b m
example : BobStudiesAtUVa × MaryStudiesAtUVa := ⟨ b, m ⟩ --same notation as above

example : BobStudiesAtUVa × MaryStudiesAtUVa → BobStudiesAtUVa := λ p => p.fst
example : BobStudiesAtUVa × MaryStudiesAtUVa → MaryStudiesAtUVa := λ p => p.snd

#check (@Sum) --use for or

--only one of them has to be inhabited
example : Sum BobStudiesAtUVa MarkoStudiesAtUVa := Sum.inl b -b is a proof of the left
example : BobStudiesAtUVa ⊕ MarkoStudiesAtUVa := Sum.inr --no proof, inr is MarkoStudiesAtUVA

--basically sayinf if either Bob or Marko studies at UVA then Bob studies at UVA
example : BobStudiesAtUVa ⊕ MarkoStudiesAtUVa → BobStudiesAtUVa
| (Sum.inl l) => l
| (Sum.inr r) => nomatch r --you're making an assumption that Marko studies at UVA here

--example : neg MarkoStudiesAtUVa :=
--thus there must exist a function from MarkoStudiesAtUVA → Empty
--no possible proof that Marko studies at UVA
--MarkoStudiesAtUVA → contradiction

example : neg (MaryStudiesAtUVa × MarkoStudiesAtUVa) := --this is an assumed proof, we need to show it's not true
λ p => nomatch p.2 --this is the proof of this proposition
--the proposition says that the statement that Mary and Marko study at UVA is false

/-!  Proof Irrelevance

-/



inductive B : Prop
| paid
| classes

inductive M : Prop
| paid
| classes

inductive K : Prop

--these three examples ay the same thing
example : And B M := And.intro B.paid M.classes
def b_and_m_true : B ∧ M := And.intro B.paid M.classes
theorem b_and_m_true' : B ∧ M := And.intro B.paid M.classes
example : B ∧ M := ⟨ B.paid, M.classes ⟩

example : B ∧ M → M := λ bm => bm.right
example : B ∧ M → B := λ bm => bm.1

--we're assuming there is a proof of K and so we're saying not K as in K → False (or nomatch k where k is of type K?)
theorem foo : B ∧ ¬K := ⟨ B.paid, λ k => nomatch k ⟩
example : B ∧ Not K := foo

example : B ∨ K := Or.inl B.paid

example : B ∨ K → B := λ b => b.inl

λ bork => match bork with
| Or.inl b => b --put b if you have a proof of b
| Or.inr k => nomatch k --ignore because this case can't happen (99% DQ K.S)

example:
  ∀ (Raining Sprinkling Wet : Prop),
  (Raining ∨ Sprinkling) →
  (Raining → Wet) →
  (Sprinkling → Wet) →
  Wet :=

λ R S W rors rw sp => --you can replace R S W with underscores
match rors with
| Or.inl r => rw r --says that it's raining (r), so given that it's raining, the grass is wet (rw r)
| Or.inr s => sp s

def NotK : ¬K := λ k => nomatch k

example (P : Prop): ¬P → P → False := --law of no contradiction
λ np p => np p

example (P : Prop) : ¬¬P → P --can't derive a proof of P here
  | nnp => _ --stuck

example (P : Prop) : (P ∨ ¬ P) → (¬¬P → P) --can't derive a proof of P here
  | pornp => match pornp with
    | Or.inl p => λ nnp => p
    | Or.inr np => λ nnp => nomatch (nnp np) --(nnp np) returns False

example (P Q : Prop): P ∧ Q → Q ∧ P :=
--want a functiuon that converts a proof of p and q into a proof of q and p
λ (h : P ∧ Q) => ⟨h.right, h.left⟩ --the angle brackets stand for And.intro (the constructor)

--this is different notation for the example above
example (P Q : Prop): P ∧ Q → Q ∧ P
| And.intro p q => And.intro q p

--this is also different notation for the example above
example (P Q : Prop): P ∧ Q → Q ∧ P
| ⟨p, q⟩ => ⟨q, p⟩

example (P Q : Prop) : P ∧ Q → P ∨ Q
| ⟨p, q⟩ => Or.inl p

example (P Q : Prop) : P ∨ Q → Q ∨ P
| Or.inl p => Or.inr p
| Or.inr q => Or.inl q


--- ∀ (P : Prop) , P ∨ ¬P


example : ∀ (P : Prop), ¬¬P → P :=
λ P nnp => _

--takes in a proposition, outputs a proof of p or not p
#check Classical.em --this is an example of a namespace

def one_not_eq_zero (n : Nat): n = 1 → n ≠ 0 :=
λ (neq1 : n = 1) => λ neq0 => by
  rw [neq1] at neq0
  cases neq0

/-!
Equality
-/

#check 1 = 0
#check Eq 1 0

#check Eq.refl 1

example : 1 = 2 := Eq.refl 1 --proof that the input is equal to itself

/-!
inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a
-/

def isEven (n : Nat): Prop := n % 2 == 0 --this is an equality proposition
--if it's equal we have a prof from the proof constructor of equality
--the presence of this proof is a proof of that proposition
--try not to think in truth values

--"predicates are just functions that yield parameterized propositions" K.S

#check isEven 0
#check isEven 1

#check isEven 2
#check isEven 3
#check isEven 4
#check isEven 5

/-!
### For all (∀)
∀ (p : P), Q
∀ (p : P), Q p --> here Q is a predicate applied to p
-/

example : ∀ (n : Nat), isEven n := _ --not true


def zornz : ∀ (n : Nat), n = 0 ∨ n ≠ 0 := --this is an Or statement you could take Or.inl and Or.inr from
λ n => match n with
  | 0 => (Or.inl (Eq.refl 0)) --you could also say rfl
  | (n' + 1) => (Or.inr (λ h => nomatch h)) --need proof of negation

#reduce zornz 3

#reduce isEven 0 --there is a proof here
#reduce isEven 1 --different output type than the one above (there is no proof here)

variable
  (P : Type)
  (Q : P → Prop) --this is a predicate
  (R : Prop)
  (t : P)

#check P
#check Q

#check Q t
#check ∀ (p : P), Q p

#check ∀ (x : P), R --just an ordinary function
--the above is a function of P to R but doesn't depend on P
--like increment, just adds 1
--example: input a value and return a list of 0's with length of that value (so like if input is 3 return a list of 3 0's)


/-!
### Exists (∃)
-/

--general form
example : ∃ (p : P) , Q p := _ --"there exists some p that has propoerty Q"

def exists_even_nat : ∃ (n : Nat), isEven n := ⟨ 2 , rfl ⟩  -- 2 is called a "witness"
--I think rfl is saying that isEven n reduced to 0 = 0, since rfl is for equality
--⟨ 2 , rfl ⟩ is called a dependent pair (?)

--example : ∃ ( n : Nat), n ≠

def foo' : (∃ (n : Nat), isEven n) → True
| ⟨ n' , pf ⟩ => _

example : ∃ (n : Nat), n ≠ 0 := ⟨ 5 , _ ⟩


/-!
### Equality — Revisited
-/

/-!
inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a
-/

--Lean reduced expressions
example : 1 + 1 = 2 := rfl

inductive IsEven : Nat → Prop
| zero_is_even : IsEven 0
| even_plus_2_even : ∀ (n : Nat), IsEven n → IsEven (n + 2)

open IsEven
example : IsEven 0 := zero_is_even
example : IsEven 4 := even_plus_2_even 2 _ --finish this blank off




--"building proofs as recursive data structures" 99% DQ K.S
