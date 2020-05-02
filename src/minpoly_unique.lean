import field_theory.minimal_polynomial

universes u v

local attribute [instance] classical.dec

theorem eq_of_dvd_of_irreducible_of_monic {α : Type u} [comm_ring α] (p q : polynomial α)
  (hpm : p.monic) (hqm : q.monic) (hpi : irreducible p) (hqi : irreducible q) (H : p ∣ q) : p = q :=
sorry
