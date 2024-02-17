#check Empty

def  e2e : Empty → Empty
| e => e

def n2e : Nat → Empty --think of this as an implication
| n => _ --can't return a value of type Empty
