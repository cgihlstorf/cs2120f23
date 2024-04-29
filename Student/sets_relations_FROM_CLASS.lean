import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic

def a_set : Set Nat := { 1, 2, 3 } --this is a predicate
def b_set : Set Nat := { 3, 4, 5 }

--this is the same notation as the definition of a_set above
--and as such it's a predicate! so you can apply it to an argument
def a_set' : Set Nat := { n : Nat | n = 1 ∨ n = 2 ∨ n = 3}

example: 1 ∈ a_set := by
  show a_set 1 --this is also another way of writing the goal(?)
  unfold a_set
  show 1=1 ∨ 1=2 ∨ 1=3 --this is a rewrite
  exact Or.inl rfl --need a proof that 1=1, use rfl

example : 3 ∈ a_set ∩ b_set := by
  --intersection is defined using And
  --it doesn't compute the intersection
  show 3 ∈ a_set ∧ 3 ∈ b_set
  exact ⟨ Or.inr (Or.inr rfl) , Or.inl rfl⟩ --this represents And.intro

example : 2 ∈ a_set ∪ b_set := by
  show 2 ∈ a_set ∨ 2 ∈ b_set
  exact Or.inl (Or.inr (Or.inl rfl))

--HW problems
example : 2 ∈ a_set \ b_set := by
  show 2 ∈ a_set ∧ ¬ (2 ∈ b_set)

--example : 3 ∉ a_set \ b_set := by
  --show 3 something



/-!
binary relation on a type, α
- reflexive
- symmetric
- transitive
- equivalence (Core.lean)
- asymmetric
- antisymmetric
- closures
- inverse

- empty relation
- complete relation
- subrelation

binary relation from α → β, etc
- compose
- join

inverse image
-/

inductive Person : Type
| lu
| mary
| jane

open Person

def Likes : Person → Person → Prop :=
  λ p1 p2 =>
    (p1 = lu ∧ p2 = mary) ∨
    (p1 = mary ∧ p2 = lu)

#reduce Likes lu mary

#reduce Likes lu jane


example : Likes lu mary := Or.inl ⟨ rfl, rfl⟩

#reduce Likes lu jane

example : ¬ Likes lu jane :=
λ h : Likes lu jane => by
  unfold Likes at h
  cases h with
  | inl l => nomatch l.2
  | inr r => nomatch r.1

  /-
    cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq
  -/

/-
order relations
- partial order: reflexive, antisymmetric, transitive
- poset: a set α along with a partial order on α
- total order: partial order ∧ ∀ a b, a ≤ b ∨ b ≤ a
-/

/-
functions
- a single-valued relation is a function

- domain of definition
- codomain
- domain
- range
- partial
- total

- identity function -- See Mathlib.Logic.Function.Basic

- one-to-one (vs many-to-one, injective)
- onto (surjective)
- bijective

- composition
- inverse
- etc
-/


--Properties of Relations
#check (@Reflexive)
#check (@Symmetric)
#check (@Equivalence)

lemma eq_nat_is_trans : Transitive (@Eq Nat) := by
unfold Transitive
intros x y z
intros hxy hyz --assume as a premise that x=y and y=z
rw[hxy]
rw[hyz] --this is all you need to do to prove x=z

theorem eq_nat_is_equiv : Equivalence (@Eq Nat) :=
  Equivalence.mk @eq_nat_is_refl @eq_nat_is_symm @eq_nat_is_trans

def cong_mod_n : Nat → Nat → Nat → Prop := λ n a b => a%n = b%n

lemma cong_mod_n_rfl : ∀ (n: Nat), Reflexive (cong_mod_n n) := by

theorem cong_mod_n_equiv' : ∀ n, Equivalence (cong_mod_n n) :=
  by
    intro n
    exact Equivalence.mk _ _ _

lemma cong_mod_n_symm : ∀ (n : Nat), Symmetric (cong_mod_n n) := by
  intro n
  unfold Symmetric
  intros x y --I'm assuing all these are nats?
  intro hxy
  unfold cong_mod_n
  unfold cong_mod_n at hxy --"in the assumption int the context called hxy" -K.S
  rw[hxy] --to substitute for the equality

  theorem cong_mod_n_equiv: ∀ (n : Nat), Equivalence (cong_mod_n n) :=
    by
      intro n
      unfold cong_mod_n
