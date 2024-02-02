/-!
(1) Write a function called add that takes two natural
numbers, a and b, and returns their sum, a + b. Don't
just look up the answer. Figure it out on your own.
Hint: do case analysis on the second argument
(a Nat can be either Nat.zero or (Nat.succ n')
and use the fact that n + (1 + m) = 1 + (n + m).
-/

def add : (a : Nat) → (b : Nat) → Nat
  | Nat.zero, b => b --can also write 0 for Nat.0
  | (Nat.succ n'), b => n' + 1 + b --can also write nm (m' + 1)

#reduce (add 0 2)
#reduce (add 1 2)

def correct_add : Nat → Nat → Nat
  | n, 0 => n
  | n, (m' + 1) => Nat.succ (add n m')
  -- you are incrementing argument 1 argument 2 times

def mul : Nat → Nat → Nat
  | n, 0 => 0
  | n, (m' + 1) => (add n (mul n m'))

#eval (mul 5 4)

def exp : Nat → Nat → Nat
  | n, 0 => 1
  | n, (m' + 1) => (mul n (exp n m'))

#eval exp 2 5
#eval exp 2 0


#eval add 4 5

/-!
(2) Write a function called append, polymorphic in a type, T,
that takes two lists values, n and m of type List T and that
returns the result of appending the two lists. For example,
append [1,2,3] [4,5,6], should return [1,2,3,4,5,6]. Hint:
It's very much list Nat addition.
-/

def append {α : Type} : (n : List α) → (m : List α) → List α
  | List.nil, m => m
  | n, List.nil => n
  | (List.cons h t), m => (append t (List.cons h m))

def l1 : List Nat := 1::2::3::List.nil
#reduce l1
def l2 : List Nat := 4::5::6::List.nil
#reduce l2
def l3 : List Nat := List.nil

#reduce (append l1 l2)
#reduce (append l1 l3)
#reduce (append l3 l1)

#check Bool

/-! The boolean value `false`, not to be confused with the proposition `False`.
The boolean value `true`, not to be confused with the proposition `True`. -/

#check Unit

/-!
inductive Empty: Type
-/

/-!inductive PUnit : Sort u where
  `PUnit.unit : PUnit`-/

def e2e : Empty → Empty
 | e => e --you can impment this function but you can never call it

#eval e2e --doesn't work

def n2e : Nat → Empty
  | n -> _ -- you can't implement this function because you can't return
  --something of type empty can't be used because there are no terms of type Empty
