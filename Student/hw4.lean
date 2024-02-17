--HW for 02/07/2024--
--Reduce a list of strings to a Boolean --> true if all strings
--in the list have even length--
--(this version was completed before class)

def combine : String → Bool → Bool
 | str, lst_bool => ((String.length str) % 2 == 0) ∧ lst_bool

def foldr' {α β : Type} : (α → β → β) → β → List α → β
  | _, id, List.nil => id --id is true in the String -> Bool -> Bool example
  | op, id, (h::t) => (op h (foldr' op id t))


def even_str_list : List String := ["list", "of", "even", "things"]
def non_even_str_list: List String := ["not", "all", "words", "are", "even"]
def all_odd_list : List String  := ["all", "words", "are", "odd"]
def empty_str_list : List String := [""]
def empty_list : List String := []

#eval foldr' combine true even_str_list     -- expect true
#eval foldr' combine true non_even_str_list -- expect false
#eval foldr' combine true all_odd_list      -- expect false
#eval foldr' combine true empty_str_list    -- expect true
#eval foldr' combine true empty_list        -- expect true

--Corrections from class--

--you can also define a separate isEvenLen function:
def isEvenLen : String → Bool := λ s => s.length % 2 == 0

def combine_from_class : String → Bool → Bool
 | s, b => and (isEvenLen s) b

#eval foldr' combine_from_class true []
#eval foldr' combine true ["Hello,", "Lean"]
#eval foldr' combine true ["Hello,", "Lean!"]

--this function only works wiht objects of the same type
def foldr_ {α : Type} : (α → α → α) → α → List α → α
  | _, id, List.nil => id
  | op, id, (h::t) => (op h (foldr_ op id t))

#eval foldr_ (Nat.add) 0 [1,2,3]
#eval foldr_ (Nat.add) 1 [1,2,3]

-- inductive my_monoid' (α : Type) where
-- | mk : (op : α → α → α) → (id : α) → (left_id : ∀ (a : α), op id a = a) →
-- (right_id : ∀ (a : α), op a id = a) →

structure my_monoid (α : Type) where --similar to inductive, gives you 1 implicit constructor mk
(op : α → α → α)
(id : α)
(left_id : ∀ (a : α), op id a = a) --left_id is of type "proposition"
(right_id : ∀ (a : α), op a id = a)

def a_monoid : my_monoid Nat := my_monoid.mk Nat.add 0 sorry sorry

#check a_monoid.op
