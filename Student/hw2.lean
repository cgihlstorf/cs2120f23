/-!
(1) Write a function called add that takes two natural
numbers, a and b, and returns their sum, a + b. Don't
just look up the answer. Figure it out on your own.
Hint: do case analysis on the second argument
(a Nat can be either Nat.zero or (Nat.succ n')
and use the fact that n + (1 + m) = 1 + (n + m).
-/

def add : (a : Nat) → (b : Nat) → Nat
  | Nat.zero, b => b
  | (Nat.succ n'), b => n' + 1 + b

#reduce (add 0 2)
#reduce (add 1 2)

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
