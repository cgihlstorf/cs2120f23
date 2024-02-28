--Corrections from class:

inductive Box (α : Type)
| contents (a : α)

inductive Tree (α : Type): Type
| empty
| node (a : α) (l r : Tree α) : Tree α

def list_map {α β : Type} : (α → β) → List α → List β
| _, [] => []
| f, h::t => f h :: list_map f t

def option_map {α β : Type} : (α → β) → Option α → Option β
| _, Option.none => Option.none
| f, (Option.some a) => some (f a)




-- @[class] --deontes this is a type class
-- structure functor (c : Type → Type) where
-- map {α β : Type} (f : α → β) (ic : c a) : c β

class functor (c : Type → Type) where
map {α β : Type} (f : α → β) (ic : c a) : c β

def list_functor : functor List  := functor.mk list_map
def option_functor : functor Option  := functor.mk option_map

--Problem 6 corrections:
def do_map {α β : Type} {c : Type → Type} [m : functor c] :
  (f : α → β) → c α → c β
| f, c => m.map f c

instance : functor List := (list_map)
instance : functor Box := (box_map)
instance : functor Option := (option_map)

#reduce do_map Nat.succ [1,2,3]
#reduce do_map Nat.succ (Box.contents 1)


infix:50 "<$>" => do_map
#reduce Nat.succ <$> (Box.contents 1)

#reduce Nat.succ [1,2,3]
#reduce do_map Nat.succ [1,2,3]

#check Functor





/-!
  class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  /-- If `f : α → β` and `x : F α` then `f <$> x : F β`. -/
  map : {α β : Type u} → (α → β) → f α → f β
  /-- The special case `const a <$> x`, which can sometimes be implemented more
  efficiently. -/
  mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _)
-/

universe u v
inductive Box' (α : Type)
  |contents (a : α)

def box_map {α β : Type} : (α → β) → Box' α → Box' β
  |f, (Box'.contents a) => Box'.contents (f a)

instance : Functor Box' := (box_map, _)

#reduce Nat.succ <$> Box'.contents 2
