--Caroline Gihlstorf

/-!
We've seen that we can generalize the notion of
mapping objects of one container-like type to
objects of a correspond value of the same type
by replacing each *element* in one container
corresponding objects computed by applying an
element-wise conversion function to each object
in the input container. Here we give two examples
that we saw in class: functions for mapping over
Lists, and functions for mapping over Options.
-/

def list_map {α β : Type} : (α → β) → List α → List β
| _, [] => []
| f, h::t => f h :: list_map f t

def option_map {α β : Type} : (α → β) → Option α → Option β
| _, Option.none => Option.none
| f, (Option.some a) => some (f a)

/-!
We now present two more "container-like" types that
we saw in class. The Box type is a container type for
exactly one object some type, α, and Tree is such a
type for representing binary trees of such objects.
-/
inductive Box (α : Type)
| contents (a : α)

inductive Tree (α : Type): Type
| empty
| node (a : α) (l r : Tree α) : Tree α

/-! Problem #1
Define box_map and tree_map functions and
use #eval to give examples of applying these
functions to a few arguments.
-/

def box_map {α β : Type} : (α → β) → Box α → Box β
  | f, (Box.contents a) => Box.contents (f a)

def tree_map {α β} : (α → β) → Tree α → Tree β
  | f, Tree.empty => Tree.empty
  | f, Tree.node a l r => Tree.node (f a) (tree_map f l) (tree_map f r)

def nat_box : Box Nat := Box.contents 3
def str_box : Box String := Box.contents "Hello"

def nat_tree : Tree Nat := Tree.node 2 (Tree.node 4 Tree.empty Tree.empty) (Tree.node 6 Tree.empty Tree.empty)
def str_tree : Tree String := Tree.node "Apples" (Tree.node "Oranges" Tree.empty Tree.empty) (Tree.node "Pears" Tree.empty Tree.empty)

--I used #reduce here because #eval was giving me an error
#reduce box_map Nat.succ nat_box
#reduce box_map String.length str_box

#reduce tree_map Nat.succ nat_tree
#reduce tree_map String.length str_tree



/-!
The functor type, below, generalizes the idea
that we can map over *any* polymorphic container
type. The functor type takes a polymorphic type
(builder), such as List or Option, and augments
it with a map function for objects of that type.
Here we don't try to specify rules for functors.
We'll see them shortly. For now the definition
follows has everything we need.
-/

structure functor (c : Type → Type) where
map {α β : Type} (f : α → β) (ic : c α) : c β

/-!
Here are functor *instances* for the polymorphic
container-like List and Option types.
-/

def list_functor : functor List  := functor.mk list_map
def option_functor : functor Option  := functor.mk option_map

/-! Problem #2

Complete the definition of a polymorphic do_map
function. Note that this function, map, is not
the same as the functor field value, functor.map.
Hint: See the "convert" function from class.
-/

def do_map {α β : Type} {c : Type → Type} (m : functor c) :
  (f : α → β) → c α → c β
| f, c => m.map f c

-- These test cases should succeed when do_map is right
#eval do_map list_functor Nat.succ [1,2,3]  -- [2, 3, 4]
#eval do_map option_functor (λ s => s ++ "!") (some "Hi")



/-! Problem #3

Briefly explain why you can't apply map to a value of type
(Tree Nat) at this point.

Here: We don't yet have a Tree functor, which is necessary
to apply the do_map function to a Tree object.
-/



/-! Problem #4

Define functor instances for Box and Tree.
-/

def box_functor : functor Box := functor.mk box_map
def tree_functor : functor Tree := functor.mk tree_map


/-! Problem #5

Give working examples, using #eval, of applying do_map
to a Box Nat and Tree String values.
-/

--I used #reduce here because #eval was giving me an error
#reduce do_map box_functor Nat.succ nat_box --(nat_box = (Box.contents 3))
#reduce do_map tree_functor String.length str_tree --(str_tree is defined in problem #1)

/-!
Here's an infix notation for do_map and a few examples
of its use.
-/

infix:50 "<$>"  => do_map
#eval Nat.succ <$> [1,2,3]
#eval (λ s => s ++ "!") <$> ["Hi", "Yo"]

/-! Problem #6

Rewrite your/our examples of mapping over List,
Option, Box, and Tree values using <$> notation.
-/

infix:50 "lm" => do_map list_functor --list mapping
#eval Nat.succ lm [1,2,3]                      --expect [2, 3, 4]
#eval String.length lm ["One", "Two", "Three"] --expect [3, 3, 5]

infix:50 "om" => do_map option_functor --Option mapping
#eval Nat.succ om Option.some 3                --expect some 4
#eval String.length om Option.some "String"    --expect some 6

infix:50 "bm" => do_map box_functor --Box mapping
--I used #reduce here because #eval was giving me an error
#reduce Nat.succ bm Box.contents 3            --expect Box.contents 4
#reduce String.length bm Box.contents "Hello" --expect Box.contents 5

infix:50 "tm" => do_map tree_functor --Tree mapping
--I used #reduce here because #eval was giving me an error
#reduce Nat.succ tm nat_tree --nat_tree is defined in problem #1
#reduce String.length tm str_tree --str_tree is defined in problem #1
