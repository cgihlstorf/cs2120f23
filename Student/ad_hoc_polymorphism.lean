
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
  | f, (Option.some a) => some (f a) --apply the function f to get something of type β


inductive Tree (α : Type) : Type
  | empty : Tree α
  | node: α → Tree α → Tree α → Tree α
  --you can also write: node (a : α) (l r : Tree α) : Tree α

def tree_map {α β : Type} : (α → β) → Tree α → Tree β
  | f, Tree.empty => Tree.empty
  | f, (Tree.node a l r) => (Tree.node (f a) (tree_map f l) (tree_map f r))

#reduce tree_map Nat.succ Tree.empty

--def a_tree := (Tree.node 1 (Tree.node 2 Tree.empty Tree.empty) (Tree.node 3 Tree.empty Tree.empty))

def a_tree :=
  Tree.node
    1
    (Tree.node
      2
      Tree.empty
      Tree.empty)
    (Tree.node
      3
      Tree.empty
      Tree.empty)


#reduce a_tree
#reduce tree_map Nat.succ a_tree




structure functor {α β : Type} (c : Type → Type) : Type where
map (f : α → β) (ic : c α) : c β

def list_functor {α β : Type}: @functor α β List := functor.mk list_map
#check (@list_functor)
def option_functor {α β : Type}: @functor α β Option := functor.mk option_map

def convert {α β : Type} (c: Type → Type) (m : @functor α β c): (f: α → β)  → c α → c β
  | f, c => m.map f c


#reduce convert List list_functor Nat.succ [1,2,3,4,5]
#reduce convert Option option_functor Nat.succ (Option.some 4)

inductive Box (α : Type)
| contents (a : α)

#reduce convert Box
