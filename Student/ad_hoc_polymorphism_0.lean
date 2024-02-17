
structure my_monoid' (α : Type) where
(op : α → α → α )
(id : α)

def foldr' {α : Type} : my_monoid' α → List α → α
| m, List.nil => m.id
| m, (List.cons h t) => (m.op h (foldr' m t))

#eval foldr' (my_monoid'.mk Nat.add 0) [1,2,3,4,5]
#eval foldr' (my_monoid'.mk Nat.mul 1) [1,2,3,4,5]
#eval foldr' (my_monoid'.mk String.append "") ["Water", "melon"]


structure my_monoid (α : Type) where
(op : α → α → α )
(id : α)
(left_id: ∀ a, op id a = a)
(right_id : ∀ a, op a id = a)
(op_assoc: ∀ a b c, op a (op b c) = op (op a b) c)


def foldr {α : Type} : my_monoid α → List α → α
| m, List.nil => m.id
| m, (List.cons h t) => (m.op h (foldr m t))

def nat_add_monoid : my_monoid Nat :=
  my_monoid.mk Nat.add 0 sorry sorry sorry

#eval foldr nat_add_monoid [1,2,3,4,5]

def nat_add_monoid' : my_monoid Nat :=
  ( Nat.add,
    0,
    λ a => by simp [Nat.add], --you could leave off [Nat.add] and it would still work
    λ a => by simp [Nat.add],
    _
  )

def nat_mul_monoid'' : my_monoid Nat :=
  (
    Nat.mul,
    1,
    λ a => by simp,
    λ a => by simp
    sorry
  )

def nary_mul' : List Nat → Nat := foldr (my_monoid.mk Nat.mul 1 sorry sorry sorry)

#eval nary_mul' [1,2,3,4,5]


/-!
Another mathematical structure: functor. -/

#check (@Option)

def pred : Nat → Option Nat
  | Nat.zero => Option.none
  | (Nat.succ n') => n'

#reduce pred 3
#reduce pred 0

def option_map {α β : Type} : (α → β) → Option α → Option β
  | f, Option.none => Option.none --these are writtne the same way but are different types
  | f, (Option.some a), some (f a) --apply the function f to get something of type β
