/-!
#1

Define a function, dec' : Nat → Nat, that takes any Nat, n, and that
returns 0 if n is 0 and that otherwise returns one less than n. Hint:
case analysis on n. When you've succeeded the following test cases
should run and return the expected values.
-/

def dec': Nat → Nat
  | Nat.zero => 0
  | (Nat.succ n') => n'


#eval dec' 2    -- expect 1
#eval dec' 1    -- expect 0
#eval dec' 0    -- expect 0

/-
#2

Define a function, l2l, polymorphic in two type parameters, α and β, that
also takes a function, f, from α to β and a list of α values and that returns
a  list of corresponding β values. As an example, (l2l Nat.succ [0, 1, 2]) is
expected to return [1, 2, 3]. Write a few test cases where α is String, β is
Nat, and f is String.length. Hint: Use case analysis on the incoming list: it
will be either List.nil or (List.cons h t), the latter of which can also be
written as (h::t).
-/

def l2l {α : Type} {β : Type}: (α → β) → (List α ) → (List β)
  | f, List.nil => List.nil
  | f, (List.cons h t) => (List.cons (f h) (l2l f t))

def strlist1 : List String := ["These", "are", "all", "strings!"]
def emptylist : List String := []
def strlist2 : List String := ["", " ", "a", "ab", "abc"]

#eval l2l String.length strlist1    -- expect [5, 3, 3, 8]
#eval l2l String.length strlist2    -- expect [0, 1, 1, 2, 3]
#eval l2l String.length emptylist   -- expect []


/-!
#3

Define a data type, called PRFV (short for "partial function return value"),
polymorphic in one type, α, where a value of this type is either "undefined"
or "defined α". If α is Nat, for example, then you would have (undefined) and
(defined 3) as values of this type. In the case of undefined,, you will have
to disable implicit arguments, as there's no value provided to this constructor
from which Lean can infer α.
-/


inductive PRFV {α : Type} where
  | undefined : PRFV
  | defined (a : α) : PRFV

#check @PRFV.undefined Nat    -- expect PRFV
#check PRFV.defined 3         -- Expect PRFV

/-!
#4

Define a variant of dec', called dec, that takes a natural number, n, as an
argument and that returns a (PRFV Nat). This value must be "PFRV.undefined"
if n = 0, reflecting the idea that dec is a partial function, one that is not
defined for the argument value, 0; and that returns one less than n otherwise.
You will thus represent a partial function from Nat to Nat as a total function
from Nat to PRFV Nat.
-/

def dec : Nat → PRFV Nat
  | Nat.zero => (PRFV)
  | (Nat.succ n') => PRFV n'



/-!
#5

Define a function, isZero from Nat to Bool that returns true if its argument
is zero and false otherwise. Write a few test cases to show that it works.
-/

def isZero : Nat → Bool
  | Nat.zero => true
  | (Nat.succ n') => false

#eval isZero 0    --expect true
#eval isZero 1    --expect false
#eval isZero 5    --expect false
#eval isZero 000  --expect true (?)
#eval isZero 05   --expect false (?)

/-!
#6

Define a function, isDef, from PFRV α to Bool, that returns false if the given
PFRV α is "undefined" and true otherwise. The following test cases should then
return the expected values.
-/

def isDef {α : Type} : PRFV α → Bool
  | PRFV.undefined => false
  | PFRV.defined => true

#eval isDef (dec 0)   -- expect false
#eval isDef (dec 1)   -- expect true
