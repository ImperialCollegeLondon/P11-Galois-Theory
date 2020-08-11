import linear_algebra.dimension
import field_theory.fixed
import .faithful_mul_semiring_action .dimension .linear_independent .group_ring_action .finsupp

universes u v

open_locale classical
open mul_action

variables (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] (g : G)

-- set_option pp.all true
theorem mem_fixed {s : finset F} {a : F} (has : a ∉ s)
  (h1 : linear_independent F (λ i : (↑(s.map $ mul_action.to_fun G F) : set (G → F)), (i : G → F)))
  {L : F →₀ F} (h2 : L ∈ finsupp.supported F F (↑s : set F))
  (h3 : mul_action.to_fun G F a = s.sum (λ i, L i • mul_action.to_fun G F i)) {i : F} :
  L i ∈ fixed_points G F :=
begin
  intro g,
  by_cases hi : i ∈ s,
  { rw linear_independent_iff at h1,
    specialize h1 (s.attach.sum $ λ i, finsupp.single ⟨_, finset.mem_map_of_mem _ i.2⟩ (g • L i.1 - L i.1)) _,
    { rw finsupp.ext_iff at h1, specialize h1 ⟨_, finset.mem_map_of_mem _ hi⟩,
      rwa [finset.sum_apply', finset.sum_eq_single (⟨i, hi⟩ : {x // x ∈ s}), finsupp.single_eq_same,
          finsupp.zero_apply, sub_eq_zero] at h1,
      { exact λ b _ hb, finsupp.single_eq_of_ne (λ H, hb $ subtype.eq $ (mul_action.to_fun G F).2 $
          by convert congr_arg subtype.val H) },
      { exact λ h, absurd (finset.mem_attach _ _) h } },
    { ext g',
      rw [finsupp.total_apply],
      erw finsupp.sum_apply'.{(max u v) v u v}
          (s.attach.sum $ λ i, finsupp.single (⟨_, finset.mem_map_of_mem _ i.2⟩ : (↑(finset.map (mul_action.to_fun G F) s) : set (G → F))) (g • L i.1 - L i.1))
          (λ i (a : F), (a • ↑i : G → F))
          g',
      simp_rw pi.smul_apply,
      rw finsupp.sum_sum_index', iterate 3 { sorry } } },
  sorry
  -- intro g,
/-   have h3 := congr_fun h2 1,
  have h4 := congr_fun h2 g,
  simp_rw [finset.sum_apply, pi.smul_apply, mul_action.to_fun_apply, smul_eq_mul] at h3 h4,
  simp_rw one_smul at h3,
  rw [h3, finset.smul_sum, ← sub_eq_zero, ← finset.sum_sub_distrib] at h4,
 -/end

#check linear_independent_iff


-- #exit
theorem linear_independent_smul_of_linear_independent {s : finset F} :
  linear_independent (fixed_points G F) (λ i : (↑s : set F), (i : F)) →
  linear_independent F (λ i : (↑s : set F), mul_action.to_fun G F i) :=
begin
  refine finset.induction_on s (λ _, linear_independent_empty_type $ λ ⟨x⟩, x.2) (λ a s has ih hs, _),
  rw finset.coe_insert at hs ⊢,
  rw linear_independent_insert (mt finset.mem_coe.1 has) at hs,
  rw linear_independent_insert' (mt finset.mem_coe.1 has),
  sorry
  -- refine (ih hs.1).insert _,
  -- rw [finset.map_insert, finset.coe_insert],
  -- rw [finset.coe_insert, linear_independent_insert (mt finset.mem_coe.1 has)] at hs,
  -- refine (ih hs.1).insert (λ ha, hs.2 _),
  -- rw [finset.coe_map, finsupp.mem_span_iff_total] at ha,
  -- rcases ha with ⟨L, hL, ha⟩,
  -- rw [← set.image_id ↑s, finsupp.mem_span_iff_total],
  -- rw [finsupp.total_apply_of_mem_supported hL] at ha,
end

#check nonempty

variables [fintype G]

theorem fixed.dim_le_card : vector_space.dim (fixed_points G F) F ≤ fintype.card G :=
begin
  refine dim_le (λ s hs, cardinal.nat_cast_le.1 _),
  rw [← @dim_fun' F G, ← cardinal.lift_nat_cast.{v (max u v)},
    cardinal.finset_card, ← cardinal.lift_id (vector_space.dim F (G → F))],
  refine le_dim.{_ _ _ (max u v)} (λ i : (↑s : set F), mul_action.to_fun G F i.1) _,
  exact linear_independent_smul_of_linear_independent G F hs
/-   refine finset.induction_on s (λ _, linear_independent_empty) (λ a s has ih hs, _),
  rw [finset.map_insert, finset.coe_insert],
  rw [finset.coe_insert, linear_independent_insert (mt finset.mem_coe.1 has)] at hs,
  refine (ih hs.1).insert (λ ha, hs.2 _),
  rw [finset.coe_map, function.embedding.coe_fn_mk, finsupp.mem_span_iff_total] at ha,
  rcases ha with ⟨L, hL, ha⟩,
  rw [← set.image_id ↑s, finsupp.mem_span_iff_total],
  rw [finsupp.total_apply_of_mem_supported hL] at ha,
  suffices : ∀ x, ∀ g : G, g • L x = L x,
  { refine ⟨s.sum $ λ i, finsupp.single i ⟨L i, λ g, this i g⟩,
      submodule.sum_mem _ (λ i his, finsupp.single_mem_supported _ _ his), _⟩,
      }, -/
end

#check finsupp.sum_single
#check finsupp.total_apply
#check cardinal.lift_le
