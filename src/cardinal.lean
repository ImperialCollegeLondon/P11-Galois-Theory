import set_theory.cardinal

universe u

theorem card_le_of {α : Type u} {n : ℕ} (H : ∀ s : finset α, s.card ≤ n) :
  cardinal.mk α ≤ n :=
begin
  refine le_of_not_lt (λ hn, _),
  have := cardinal.succ_le.2 hn,
  rw [← cardinal.nat_succ, ← cardinal.lift_mk_fin n.succ] at this,
  cases this,
  refine not_lt_of_le (H $ finset.univ.map this) _,
  rw [finset.card_map, ← fintype.card, fintype.card_ulift, fintype.card_fin],
  exact n.lt_succ_self
end
