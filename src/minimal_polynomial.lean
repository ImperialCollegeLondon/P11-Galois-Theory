-- minimal polynomial

import .balgebra ring_theory.principal_ideal_domain ring_theory.ideal_operations

universes u v

variables (F : Type u) {K : Type v}
variables [discrete_field F] [field K]

theorem is_ring_hom.inj (φ : F → K) [is_ring_hom φ] : function.injective φ :=
λ x y hφ, eq_of_sub_eq_zero $ by_contradiction $ λ hxy,
have _ := congr_arg φ (mul_inv_cancel hxy),
by rw [is_ring_hom.map_mul φ, is_ring_hom.map_sub φ, hφ, sub_self, zero_mul, is_ring_hom.map_one φ] at this;
exact zero_ne_one this

variables {F} (i : algebra F K)

theorem algebra.eq_zero_iff {x : F} : i x = 0 ↔ x = 0 :=
⟨λ h, is_ring_hom.inj F i $ h.symm ▸ (is_ring_hom.map_zero _).symm,
λ h, h.symm ▸ is_ring_hom.map_zero _⟩

open polynomial

def is_algebraic (x : K) : Prop :=
∃ p : polynomial F, p ≠ 0 ∧ aeval F i x p = 0

noncomputable def irr_aux (x : K) : polynomial F :=
@@ideal.is_principal.generator _
  (ideal.comap (aeval F i x) ⊥)
  (principal_ideal_domain.principal _)

/-- minimal polynomial -/
noncomputable def irr (x : K) : polynomial F :=
irr_aux i x * C (leading_coeff (irr_aux i x))⁻¹

theorem aeval_irr (x : K) : aeval F i x (irr i x) = 0 :=
have _ := or.resolve_right (ideal.is_principal.generator_mem (ideal.comap (aeval F i x) ⊥)) (set.not_mem_empty _),
by rw [aeval_def, irr, irr_aux, eval₂_mul, ← aeval_def, this, zero_mul]

variables {F i}

theorem irr_aux_ne_zero_of_algebraic {x : K} (hx : is_algebraic i x) : irr_aux i x ≠ 0 :=
λ hi, let ⟨p, hp1, hp2⟩ := hx in
by letI : module (polynomial F) (polynomial F) := ring.to_module; exact
hp1 (submodule.mem_bot.1 $ lattice.eq_bot_iff.1 ((ideal.is_principal.eq_bot_iff_generator_eq_zero _).2 hi) (or.inl hp2))

theorem monic_irr_of_algebraic {x : K} (hx : is_algebraic i x) : monic (irr i x) :=
monic_mul_leading_coeff_inv $ irr_aux_ne_zero_of_algebraic hx

theorem irr_ne_zero_of_algebraic {x : K} (hx : is_algebraic i x) : irr i x ≠ 0 :=
ne_zero_of_monic $ monic_irr_of_algebraic hx

theorem irr_eq_zero_of_not_algebraic {x : K} (hx : ¬is_algebraic i x) : irr i x = 0 :=
by rw [irr, irr_aux, (ideal.is_principal.eq_bot_iff_generator_eq_zero _).1, zero_mul];
letI : module (polynomial F) (polynomial F) := ring.to_module;
exact lattice.eq_bot_iff.2 (λ p hp, submodule.mem_bot.2 $ by_contradiction $ λ hnp,
hx ⟨p, hnp, or.resolve_right hp (set.not_mem_empty _)⟩)

-- TODO : https://github.com/leanprover/mathlib/pull/514
lemma is_unit_iff_degree_eq_zero {p : polynomial F} : is_unit p ↔ degree p = 0 := sorry

theorem irr_dvd_iff (x : K) (p : polynomial F) :
  irr i x ∣ p ↔ aeval F i x p = 0 :=
begin
  cases classical.em (is_algebraic i x) with hx hx,
  { have : is_unit (C (leading_coeff (irr_aux i x))⁻¹),
    { rw is_unit_iff_degree_eq_zero,
      exact degree_C (inv_ne_zero $ mt leading_coeff_eq_zero.1 $ irr_aux_ne_zero_of_algebraic hx) },
    rw [irr, mul_dvd_of_is_unit_right this, irr_aux, ← ideal.is_principal.mem_iff_generator_dvd,
        ideal.mem_comap, submodule.mem_bot] },
  rw [irr_eq_zero_of_not_algebraic hx, zero_dvd_iff],
  split,
  { rintro rfl, rw [aeval_def, eval₂_zero] },
  intro hp, by_contra hnp, exact hx ⟨p, hnp, hp⟩
end

theorem irreducible_irr {x : K} (hx : is_algebraic i x) : irreducible (irr i x) :=
begin
  split,
  { rw [is_unit_iff_degree_eq_zero], intro hdi,
    have hirr := eq_C_of_degree_le_zero (le_of_eq hdi),
    have := aeval_irr i x,
    rw [hirr, aeval_def, eval₂_C, algebra.eq_zero_iff] at this,
    rw [this, C_0] at hirr,
    exact irr_ne_zero_of_algebraic hx hirr },
  intros p q hipq,
  have := aeval_irr i x,
  rw [aeval_def, hipq, eval₂_mul, mul_eq_zero] at this,
  -- TODO : wlog
  cases this,
  { rw [← aeval_def, ← irr_dvd_iff] at this,
    cases this with r hr,
    rw [hr, mul_assoc, ← sub_eq_zero, ← mul_one (irr i x), mul_assoc, ← mul_sub,
        one_mul, mul_eq_zero, or_iff_not_imp_left, sub_eq_zero, mul_comm] at hipq,
    exact or.inr (is_unit_of_mul_one _ _ $ eq.symm $ hipq $ irr_ne_zero_of_algebraic hx) },
  { rw [← aeval_def, ← irr_dvd_iff] at this,
    cases this with r hr,
    rw [mul_comm, hr, mul_assoc, ← sub_eq_zero, ← mul_one (irr i x), mul_assoc, ← mul_sub,
        one_mul, mul_eq_zero, or_iff_not_imp_left, sub_eq_zero, mul_comm] at hipq,
    exact or.inl (is_unit_of_mul_one _ _ $ eq.symm $ hipq $ irr_ne_zero_of_algebraic hx) }
end

@[extensionality]
theorem irr_ext (x : K) (p : polynomial F) (hmp : monic p)
  (hpx : aeval F i x p = 0) (hip : irreducible p) : p = irr i x :=
begin
  cases (irr_dvd_iff x p).2 hpx with q hpq,
  have := eq_C_of_degree_le_zero (le_of_eq $ is_unit_iff_degree_eq_zero.1 $
      (hip.2 _ _ hpq).resolve_left (irreducible_irr ⟨p, ne_zero_of_monic hmp, hpx⟩).1),
  rw this at hpq, rw hpq, replace hpq := congr_arg leading_coeff hpq,
  rw [leading_coeff_mul, leading_coeff_C, show _ = _, from hmp,
      show _ = _, from monic_irr_of_algebraic ⟨p, ne_zero_of_monic hmp, hpx⟩, one_mul] at hpq,
  rw [← hpq, C_1, mul_one]
end