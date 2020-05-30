import ring_theory.polynomial algebra.group_ring_action

universes u v

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
  (hp : ↑p.frange ⊆ T) : (p.to_subring T hp).map (is_subring.subtype T) = p :=
ext $ λ n, coeff_map _ _

theorem irreducible_of_monic {F : Type u} [field F] {p : polynomial F} (hp1 : p.monic)
  (hp2 : p ≠ 1) (hp3 : ∀ f g : polynomial F, f.monic → g.monic → f * g = p → f = 1 ∨ g = 1) :
  irreducible p :=
⟨mt (eq_one_of_is_unit_of_monic hp1) hp2, λ f g hp,
have hf : f ≠ 0, from λ hf, by { rw [hp, hf, zero_mul] at hp1, exact not_monic_zero hp1 },
have hg : g ≠ 0, from λ hg, by { rw [hp, hg, mul_zero] at hp1, exact not_monic_zero hp1 },
or.imp (λ hf, is_unit_of_mul_eq_one _ _ hf) (λ hg, is_unit_of_mul_eq_one _ _ hg) $
hp3 (f * C f.leading_coeff⁻¹) (g * C g.leading_coeff⁻¹)
  (monic_mul_leading_coeff_inv hf) (monic_mul_leading_coeff_inv hg) $
by rw [mul_assoc, mul_left_comm _ g, ← mul_assoc, ← C_mul, ← mul_inv'', ← leading_coeff_mul,
    ← hp, monic.def.1 hp1, one_inv_eq, C_1, mul_one]⟩

theorem map_dvd_map {R : Type u} [comm_ring R] {S : Type v} [comm_ring S]
  (f : R →+* S) (hf : function.injective f) {x y : polynomial R} (hx : x.monic) :
  x.map f ∣ y.map f ↔ x ∣ y :=
by { rw [← dvd_iff_mod_by_monic_eq_zero hx, ← dvd_iff_mod_by_monic_eq_zero (monic_map f hx),
    ← map_mod_by_monic f hx], exact ⟨λ H, map_injective hf $ by rw [H, map_zero],
  λ H, by rw [H, map_zero]⟩ }

local attribute [instance] classical.dec_eq
theorem map_dvd_map' {F : Type u} [field F] {K : Type v} [field K]
  (f : F →+* K) {x y : polynomial F} : x.map f ∣ y.map f ↔ x ∣ y :=
if H : x = 0 then by rw [H, map_zero, zero_dvd_iff, zero_dvd_iff, map_eq_zero]
else by rw [← normalize_dvd_iff, ← @normalize_dvd_iff (polynomial F), normalize, normalize,
    coe_norm_unit H, coe_norm_unit (mt (map_eq_zero _).1 H),
    leading_coeff_map, ← f.map_inv, ← map_C, ← map_mul,
    map_dvd_map _ f.injective (monic_mul_leading_coeff_inv H)]

theorem smul_eval_smul {M : Type u} [monoid M] {R : Type v} [comm_semiring R]
  [mul_semiring_action M R] (m : M) (f : polynomial R) (x : R) :
  (m • f).eval (m • x) = m • f.eval x :=
polynomial.induction_on f
  (λ r, by rw [smul_C, eval_C, eval_C])
  (λ f g ihf ihg, by rw [smul_add, eval_add, ihf, ihg, eval_add, smul_add])
  (λ n r ih, by rw [smul_mul', smul_pow, smul_C, smul_X, eval_mul, eval_C, eval_pow, eval_X,
      eval_mul, eval_C, eval_pow, eval_X, smul_mul', smul_pow])

theorem eval_smul {G : Type u} [group G] {R : Type v} [comm_semiring R]
  [mul_semiring_action G R] (g : G) (f : polynomial R) (x : R) :
  f.eval (g • x) = g • (g⁻¹ • f).eval x :=
by rw [← smul_eval_smul, mul_action.smul_inv_smul]

theorem smul_eval {G : Type u} [group G] {R : Type v} [comm_semiring R]
  [mul_semiring_action G R] (g : G) (f : polynomial R) (x : R) :
  (g • f).eval x = g • f.eval (g⁻¹ • x) :=
by rw [← smul_eval_smul, mul_action.smul_inv_smul]

end polynomial
