import ring_theory.polynomial

universe u

namespace polynomial

theorem eq_of_monic_of_associated {R : Type u} [integral_domain R] {p q : polynomial R}
  (hp : p.monic) (hq : q.monic) (hpq : associated p q) : p = q :=
begin
  obtain ⟨u, hu⟩ := hpq,
  unfold monic at hp hq,
  rw eq_C_of_degree_le_zero (le_of_eq $ degree_coe_units _) at hu,
  rw [← hu, leading_coeff_mul, hp, one_mul, leading_coeff_C] at hq,
  rwa [hq, C_1, mul_one] at hu
end

theorem map_to_subring {R : Type u} [comm_ring R] (p : polynomial R) (T : set R) [is_subring T]
  (hp : ↑p.frange ⊆ T) : (p.to_subring T hp).map (algebra_map T R) = p :=
ext $ λ n, coeff_map _ _

end polynomial
