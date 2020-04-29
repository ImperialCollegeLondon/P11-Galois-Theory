/-import .algebra ring_theory.noetherian linear_algebra.dimension

universes u v

open lattice

section

parameters {F : Type u} [discrete_field F]
parameters {V : Type v} [add_comm_group V] [vector_space F V]
parameters (hv : (⊤ : submodule F V).fg)

include hv

theorem surjective_of_injective
  (φ : V →ₗ V) (hφ : function.injective φ) : function.surjective φ :=
begin
  have hb : is_basis (∅ : set φ.ker),
  { split, { exact linear_independent_empty },
    rw eq_top_iff, rintros x hx', clear hx',
    suffices : x = 0,
    { rw this, exact (submodule.mem_coe _).2 (submodule.zero_mem _) },
    suffices : x.1 ∈ (⊥ : submodule F V),
    { exact subtype.eq (submodule.mem_bot.1 this) },
    rw ← linear_map.ker_eq_bot.2 hφ, exact x.2 },
  have H := dim_range_add_dim_ker φ,
  have : cardinal.mk (∅ : set φ.ker) = 0,
  { by_contra h, cases cardinal.ne_zero_iff_nonempty.1 h with x, exact x.2 },
  rw [← hb.mk_eq_dim, this, add_zero] at H,
  sorry
end

end

section

parameters {F : Type u} [discrete_field F]
parameters {A : Type v} [integral_domain A]
parameters [algebra F A] (hi : (⊤ : submodule F A).fg)

private theorem exists_mul (x : A) (h : x ≠ 0) : function.surjective ((*) x) :=
sorry

noncomputable def field_of_fg_of_integral_domain
  {F : Type u} [discrete_field F]
  {A : Type v} [integral_domain A]
  (i : algebra F A) (hi : (⊤ : submodule F i.mod).fg) : field A :=
{ inv := λ x, classical.some ((sorry : ∀ z, ∃ y, x * y = z) (1:A)),
  mul_inv_cancel := sorry,
  inv_mul_cancel := sorry,
  .. (infer_instance : integral_domain A) }

end-/