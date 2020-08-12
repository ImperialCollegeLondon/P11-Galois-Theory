import linear_algebra.dimension
import field_theory.fixed
import field_theory.tower
import .faithful_mul_semiring_action .dimension .linear_independent .group_ring_action .finsupp

universes u v

open_locale classical big_operators
open mul_action finset

variables (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F]

theorem linear_independent_smul_of_linear_independent {s : finset F} :
  linear_independent (fixed_points G F) (λ i : (↑s : set F), (i : F)) →
  linear_independent F (λ i : (↑s : set F), mul_action.to_fun G F i) :=
begin
  refine finset.induction_on s (λ _, linear_independent_empty_type $ λ ⟨x⟩, x.2) (λ a s has ih hs, _),
  rw coe_insert at hs ⊢,
  rw linear_independent_insert (mt mem_coe.1 has) at hs,
  rw linear_independent_insert' (mt mem_coe.1 has), refine ⟨ih hs.1, λ ha, _⟩,
  rw finsupp.mem_span_iff_total at ha, rcases ha with ⟨l, hl, hla⟩,
  rw [finsupp.total_apply_of_mem_supported hl] at hla,
  suffices : ∀ i ∈ s, l i ∈ fixed_points G F,
  { replace hla := (sum_apply _ _ (λ i, l i • to_fun G F i)).symm.trans (congr_fun hla 1),
    simp_rw [pi.smul_apply, to_fun_apply, one_smul] at hla,
    refine hs.2 (hla ▸ submodule.sum_mem _ (λ c hcs, _)),
    change (⟨l c, this c hcs⟩ : fixed_points G F) • c ∈ _,
    exact submodule.smul_mem _ _ (submodule.subset_span $ mem_coe.2 hcs) },
  intros i his g,
  refine eq_of_sub_eq_zero (linear_independent_iff'.1 (ih hs.1) s.attach (λ i, g • l i - l i) _
    ⟨i, his⟩ (mem_attach _ _) : _),
  refine (@sum_attach _ _ s _ (λ i, (g • l i - l i) • (to_fun G F) i)).trans _, ext g', dsimp only,
  conv_lhs { rw sum_apply, congr, skip, funext, rw [pi.smul_apply, sub_smul, smul_eq_mul] },
  rw [sum_sub_distrib, pi.zero_apply, sub_eq_zero],
  conv_lhs { congr, skip, funext,
    rw [to_fun_apply, ← mul_inv_cancel_left g g', mul_smul, ← smul_mul', ← to_fun_apply _ x] },
  show ∑ x in s, g • (λ y, l y • to_fun G F y) x (g⁻¹ * g') =
    ∑ x in s, (λ y, l y • to_fun G F y) x g',
  rw [← smul_sum, ← sum_apply _ _ (λ y, l y • to_fun G F y),
      ← sum_apply _ _ (λ y, l y • to_fun G F y)], dsimp only,
  rw [hla, to_fun_apply, to_fun_apply, smul_smul, mul_inv_cancel_left]
end

variables [fintype G]

theorem fixed.dim_le_card : vector_space.dim (fixed_points G F) F ≤ fintype.card G :=
begin
  refine dim_le (λ s hs, cardinal.nat_cast_le.1 _),
  rw [← @dim_fun' F G, ← cardinal.lift_nat_cast.{v (max u v)},
    cardinal.finset_card, ← cardinal.lift_id (vector_space.dim F (G → F))],
  refine le_dim.{_ _ _ (max u v)} (λ i : (↑s : set F), mul_action.to_fun G F i.1) _,
  exact linear_independent_smul_of_linear_independent G F hs
end

#check linear_independent_monoid_hom
/-
G → (F →ₐ[fixed_points G F] F)
g ↦ (x ↦ g • x)

lindep F (coe : (F →ₐ[fixed_points G F] F) → (F →ₗ[fixed_points G F] F))

Hom(V, W) <-- V* ⊗ W
dim L (V ⊗[K] L) = dim K V

When in doubt, pick a basis

    dim F (F →ₗ[fixed_points G F] F)
"=" dim F ((F →ₗ[fixed_points G F] (fixed_points G F)) ⊗[fixed_points G F] F)
"=" dim (fixed_points G F) (F →ₗ[fixed_points G F] (fixed_points G F))
"=" dim (fixed_points G F) F
-/

open finite_dimensional
#check findim_mul_findim (fixed_points G F) F (F →ₗ[fixed_points G F] F) -- F ⊆ K ⊆ A
