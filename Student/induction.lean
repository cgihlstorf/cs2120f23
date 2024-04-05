#check False.rec

#check Bool.rec

/-!
Bool.rec.{u}
  {motive : Bool → Sort u} --function of sort 1 or higher, predicate if sort 0 (Prop)
  (false : motive false)
  (true : motive true)
  (t : Bool) :
  motive t
-/

example : ∀ (b : Bool), !!b = b:=
by
  intros b --assume you have some arbitrary bool
  induction b --induction principle for Bools, here it's the same as case analysis
  repeat {rfl}

#check Nat.rec

/-!
Nat.rec.{u}
  {motive : Nat → Sort u}
  (zero : motive Nat.zero)
  (succ : (n : Nat) → motive n → motive (Nat.succ n))
  (t : Nat) :
  motive t
-/

--factorial
def fact_0 := 1
def fact_succ : (n : Nat) → (fact_n : Nat) → Nat
| n, fact_n => fact_n * (n + 1)

#check (Nat.rec fact_0 fact_succ : Nat → Nat)

#reduce (Nat.rec fact_0 fact_succ : Nat → Nat) 5



#check List.rec

/-!
List.rec.{u_1, u}
  {α : Type u}
  {motive : List α → Sort u_1}
  (nil : motive [])
  (cons : (head : α) → (tail : List α) → motive tail → motive (head :: tail))
  (t : List α) : motive t
-/

def list_step {α : Type} : α → List α → Nat → Nat := _
--fill in this step function as HW!
--and finishe the #reduce expression (also as HW)
--also use the recursor to compute the number of nodes in the tree
--cut and paste

#reduce (List.rec 0 list_step)

def list_empty_len := 0


#check List Nat


inductive Tree (α : Type) where
| empty : Tree α
| node (a : α) (l r : Tree α)

#check Tree.rec
