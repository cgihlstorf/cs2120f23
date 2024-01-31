


/-!
Below is the correct version:
-/

def appl4correct {α : Type} : (α → α) → (α → α)
  | f => fun a => (f ∘ f ∘ f ∘ f) a

/-!
Below is the my version:
-/

def apply4 (α : Type) : (α → α) → (α → α)
  | f => fun a => (f ∘ (f ∘ (f ∘ (f)))) a



def compn {α : Type} : Nat → (α → α) → (α → α)
  | Nat.zero, f => λ a => a
  | (Nat.succ n'), f => λ a => f (compn n' f a)

#eval (compn 5 Nat.succ) 0

def sq (n: Nat) := n * n

#eval (compn 5 sq) 2

#check (@List)

/-!
inductive List (α : Type u) where
  | nil : List α
  | cons (head : α) (tail : List α) : List α
-/
def e : List Nat := List.nil
def e' : List Nat := [] --List NOTATION

def l1 : List Nat := List.cons 1 e
def l1' : List Nat := 1::e -- notation for cons
def l'' : List Nat := [1]

def l2 : List Nat := List.cons 0 l1
#reduce l2

def list_len {α : Type} : List α → Nat
  | List.nil => 0
  | (List.cons h t) => 1 + list_len  t --you could also use an underscore for h since it isn't being used

  #eval list_len l2
