-- minimal polynomial

import .integral_closure
import ring_theory.principal_ideal_domain
import ring_theory.ideal_operations

universes u v

variables {F : Type u} {K : Type v}
variables [discrete_field F] [discrete_field K] [algebra F K]

theorem algebra.eq_zero_iff {x : F} : algebra_map K x = 0 ↔ x = 0 :=
⟨λ h, is_field_hom.injective (algebra_map K) $ h.symm ▸ (is_ring_hom.map_zero _).symm,
λ h, h.symm ▸ is_ring_hom.map_zero _⟩

open polynomial

variables (F)
def is_algebraic (x : K) : Prop :=
∃ p : polynomial F, p ≠ 0 ∧ aeval F K x p = 0

theorem is_integral_of_algebraic {x : K} (p : polynomial F)
  (hp1 : p ≠ 0) (hp2 : aeval F K x p = 0) : is_integral F x :=
⟨p * C (leading_coeff p)⁻¹, monic_mul_leading_coeff_inv hp1,
by rw [alg_hom.map_mul, hp2, zero_mul]⟩

noncomputable def irr_aux (x : K) : polynomial F :=
@@ideal.is_principal.generator _
  (ideal.comap (aeval F K x) ⊥)
  (principal_ideal_domain.principal _)

/-- minimal polynomial -/
noncomputable def irr (x : K) : polynomial F :=
irr_aux F x * C (leading_coeff (irr_aux F x))⁻¹

theorem aeval_irr (x : K) : aeval F K x (irr F x) = 0 :=
have _ := or.resolve_right (ideal.is_principal.generator_mem (ideal.comap (aeval F K x) ⊥)) (set.not_mem_empty _),
by rw [aeval_def, irr, irr_aux, eval₂_mul, ← aeval_def, this, zero_mul]

variables {F}

theorem irr_aux_ne_zero_of_algebraic {x : K} (hx : is_algebraic F x) : irr_aux F x ≠ 0 :=
λ hi, let ⟨p, hp1, hp2⟩ := hx in
by letI : module (polynomial F) (polynomial F) := ring.to_module; exact
hp1 ((submodule.mem_bot F).1 $ lattice.eq_bot_iff.1 ((ideal.is_principal.eq_bot_iff_generator_eq_zero _).2 hi) (or.inl hp2))

theorem monic_irr_of_algebraic {x : K} (hx : is_algebraic F x) : monic (irr F x) :=
monic_mul_leading_coeff_inv $ irr_aux_ne_zero_of_algebraic hx

theorem irr_ne_zero_of_algebraic {x : K} (hx : is_algebraic F x) : irr F x ≠ 0 :=
ne_zero_of_monic $ monic_irr_of_algebraic hx

theorem irr_eq_zero_of_not_algebraic {x : K} (hx : ¬is_algebraic F x) : irr F x = 0 :=
by rw [irr, irr_aux, (ideal.is_principal.eq_bot_iff_generator_eq_zero _).1, zero_mul];
letI : module (polynomial F) (polynomial F) := ring.to_module;
exact lattice.eq_bot_iff.2 (λ p hp, (submodule.mem_bot F).2 $ by_contradiction $ λ hnp,
hx ⟨p, hnp, or.resolve_right hp (set.not_mem_empty _)⟩)

theorem irr_dvd_iff (x : K) (p : polynomial F) :
  irr F x ∣ p ↔ aeval F K x p = 0 :=
begin
  cases classical.em (is_algebraic F x) with hx hx,
  { have : is_unit (C (leading_coeff (irr_aux F x))⁻¹),
    { rw is_unit_iff_degree_eq_zero,
      exact degree_C (inv_ne_zero $ mt leading_coeff_eq_zero.1 $ irr_aux_ne_zero_of_algebraic hx) },
    rw [irr, mul_dvd_of_is_unit_right this, irr_aux, ← ideal.is_principal.mem_iff_generator_dvd,
        ideal.mem_comap, submodule.mem_bot] },
  rw [irr_eq_zero_of_not_algebraic hx, zero_dvd_iff],
  split,
  { rintro rfl, rw [aeval_def, eval₂_zero] },
  intro hp, by_contra hnp, exact hx ⟨p, hnp, hp⟩
end

theorem irreducible_irr {x : K} (hx : is_algebraic F x) : irreducible (irr F x) :=
begin
  split,
  { rw [is_unit_iff_degree_eq_zero], intro hdi,
    have hirr := eq_C_of_degree_le_zero (le_of_eq hdi),
    have := aeval_irr F x,
    rw [hirr, aeval_def, eval₂_C, algebra.eq_zero_iff] at this,
    rw [this, C_0] at hirr,
    exact irr_ne_zero_of_algebraic hx hirr },
  intros p q hipq,
  have := aeval_irr F x,
  rw [aeval_def, hipq, eval₂_mul, mul_eq_zero] at this,
  -- TODO : wlog
  cases this,
  { rw [← aeval_def, ← irr_dvd_iff] at this,
    cases this with r hr,
    rw [hr, mul_assoc, ← sub_eq_zero, ← mul_one (irr F x), mul_assoc, ← mul_sub,
        one_mul, mul_eq_zero, or_iff_not_imp_left, sub_eq_zero, mul_comm] at hipq,
    exact or.inr (is_unit_of_mul_one _ _ $ eq.symm $ hipq $ irr_ne_zero_of_algebraic hx) },
  { rw [← aeval_def, ← irr_dvd_iff] at this,
    cases this with r hr,
    rw [mul_comm, hr, mul_assoc, ← sub_eq_zero, ← mul_one (irr F x), mul_assoc, ← mul_sub,
        one_mul, mul_eq_zero, or_iff_not_imp_left, sub_eq_zero, mul_comm] at hipq,
    exact or.inl (is_unit_of_mul_one _ _ $ eq.symm $ hipq $ irr_ne_zero_of_algebraic hx) }
end

@[extensionality]
theorem irr_ext (x : K) (p : polynomial F) (hmp : monic p)
  (hpx : aeval F K x p = 0) (hip : irreducible p) : p = irr F x :=
begin
  cases (irr_dvd_iff x p).2 hpx with q hpq,
  have := eq_C_of_degree_le_zero (le_of_eq $ is_unit_iff_degree_eq_zero.1 $
      (hip.2 _ _ hpq).resolve_left (irreducible_irr ⟨p, ne_zero_of_monic hmp, hpx⟩).1),
  rw this at hpq, rw hpq, replace hpq := congr_arg leading_coeff hpq,
  rw [leading_coeff_mul, leading_coeff_C, show _ = _, from hmp,
      show _ = _, from monic_irr_of_algebraic ⟨p, ne_zero_of_monic hmp, hpx⟩, one_mul] at hpq,
  rw [← hpq, C_1, mul_one]
end