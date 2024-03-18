
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

--- ∀ (P : Prop) , P ∨ ¬P
