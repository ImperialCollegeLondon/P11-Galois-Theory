import algebra.big_operators

universes u v

namespace finset

variables {α : Type u} {β : Type v} {s : finset α} {f : α → β} [integral_domain β]

theorem prod_ne_zero : s.prod f ≠ 0 ↔ ∀ a ∈ s, f a ≠ 0 :=
by { rw [ne, prod_eq_zero_iff], push_neg }

end finset
