import field_theory.splitting_field ring_theory.polynomial
import data.polynomial

universes u

variables {α : Type u} [field α]

def adjoin_all_roots (f : polynomial α) : Type u :=
sorry

variables (β : Type u) (f : polynomial α)

variables [field β] 

variables [algebra α β]

def is_splitting_field (f : polynomial α) : Prop :=
polynomial.splits (algebra_map α β) f ∧ β = adjoin_all_roots f

theorem splitting_theorem :
(is_splitting_field β f) → 
∀ (p : polynomial α), (irreducible p → (∃ (x : β), polynomial.aeval α β x p = 0) → 
polynomial.splits (algebra_map α β) p) := 
sorry



