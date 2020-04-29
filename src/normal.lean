/- Normal extensions. -/

import field_theory.minimal_polynomial field_theory.splitting_field

universes u v w

variables (α : Type u) (β : Type v) {γ : Type w}

noncomputable theory
open_locale classical
variables [field α] [field β] [algebra α β] [field γ]

@[class] def normal : Prop :=
∀ x : β, ∃ H : is_integral α x, polynomial.splits (algebra_map α β) (minimal_polynomial H)

