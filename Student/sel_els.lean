
example:
∀ (Person : Type)
  (Loves : Person → Person → Prop)
  (p q : Person),
  (∃ (q : Person), ∀ (p : Person), Loves p q) → --sel
  (∀ (p : Person), ∃ (q : Person), Loves p q) :=
λ Person Loves p q sel k => match sel with
| ⟨ joe , everyone_loves_joe ⟩ => ⟨joe, everyone_loves_joe k ⟩

--your attempt: (forgot to match sel with the line below)
-- λ Person Loves p q sel k =>
-- | ⟨joe , everyone_loves_joe⟩ => ⟨joe, everyone_loves_joe k⟩

variable
  (Ball : Type)
  (Heavy : Ball → Prop)
  (Red : Ball → Prop)

example : (∃ (b : Ball), (Red b ∧ Heavy b)) → (∃ (b: Ball), Red b) :=
λ h => match h with
| ⟨brh, bisredandheavy⟩ => ⟨brh, bisredandheavy.left⟩

-- λ h => match h with
-- | ⟨ rhb, bisredandheavy ⟩ => ⟨rhb , bisredandheavy.left⟩

example : (∃ (b : Ball), (Red b ∧ Heavy b)) → (∃ (b: Ball), Red b ∨ Heavy b) :=
λ h => match h with
| ⟨rhb, bisredandheavy⟩ => ⟨rhb, Or.inr bisredandheavy.right⟩

example : (¬ (∀ (b : Ball), Red b)) → (b : Ball) → (∃ (b : Ball), ¬(Red b)) :=
λ nabr aball => ⟨ aball , λ rb => _ ⟩

example : (∃ (b : Ball), ¬(Red b)) → (¬ (∀ (b : Ball), Red b)) :=
λ nonred =>
  match nonred with
  | ⟨ nrb, pfnr ⟩ => λ h =>
    let rb := ⟨h nrb⟩
    --by contradiction
    False.elim ⟨pfnr rb⟩
