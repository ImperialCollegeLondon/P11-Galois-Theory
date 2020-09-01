import linear_algebra.dimension
import field_theory.fixed
import field_theory.tower
import linear_algebra.matrix
import .faithful_mul_semiring_action .dimension .linear_independent .group_ring_action .finsupp

universes u v w

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

instance linear_map.semimodule' (R : Type u) [comm_semiring R]
  (M : Type v) [add_comm_monoid M] [semimodule R M]
  (S : Type w) [comm_semiring S] [algebra R S] : semimodule S (M →ₗ[R] S) :=
{ smul := λ s f, linear_map.llcomp _ _ _ _ (algebra.lmul R S s) f,
  one_smul := λ f, linear_map.ext $ λ x, one_mul _,
  mul_smul := λ s₁ s₂ f, linear_map.ext $ λ x, mul_assoc _ _ _,
  smul_add := λ s f g, linear_map.map_add _ _ _,
  smul_zero := λ s, linear_map.map_zero _,
  add_smul := λ s₁ s₂ f, linear_map.ext $ λ x, add_mul _ _ _,
  zero_smul := λ f, linear_map.ext $ λ x, zero_mul _ }

instance linear_map.semiring (R : Type u) [comm_semiring R]
  (S : Type v) [semiring S] [algebra R S] : semiring (S →ₗ[R] S) :=
{ mul := λ f g, linear_map.llcomp R S S S f g,
  one := linear_map.id,
  mul_assoc := λ _ _ _, rfl,
  mul_one := λ _, linear_map.ext $ λ _, rfl,
  one_mul := λ _, linear_map.ext $ λ _, rfl,
  zero_mul := λ _, rfl,
  mul_zero := λ f, linear_map.ext $ λ x, f.map_zero,
  left_distrib := λ _, linear_map.map_add _,
  right_distrib := λ _ _ _, linear_map.map_add₂ _ _ _ _,
  .. linear_map.add_comm_monoid }

instance linear_map.ring (R : Type u) [comm_semiring R]
  (S : Type v) [ring S] [algebra R S] : ring (S →ₗ[R] S) :=
{ .. linear_map.semiring R S, .. linear_map.add_comm_group }

-- NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE!
-- instance linear_map.algebra (R : Type u) [comm_semiring R]
--   (S : Type w) [comm_semiring S] [algebra R S] : algebra S (S →ₗ[R] S) :=
-- { to_fun := algebra.lmul R S,
--   map_one' := linear_map.ext one_mul,
--   map_mul' := λ s₁ s₂, linear_map.ext $ mul_assoc s₁ s₂,
--   map_zero' := linear_map.map_zero _,
--   map_add' := linear_map.map_add _,
--   commutes' := λ s f, linear_map.ext $ λ x, _, -- s * f(x) = f(s * x)
--   smul_def' := _,
--   .. linear_map.semimodule' R S S }
-- NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE! NOT TRUE!

instance is_scalar_tower.linear_map (R : Type u) (A : Type v) (V : Type w)
  [comm_semiring R] [comm_semiring A] [add_comm_monoid V]
  [semimodule R V] [algebra R A] : is_scalar_tower R A (V →ₗ[R] A) :=
⟨λ x y f, linear_map.ext $ λ v, algebra.smul_mul_assoc x y (f v)⟩

theorem finite_dimensional_of_right (F : Type u) (K : Type v) (V : Type w)
  [field F] [field K] [add_comm_group V] [algebra F K] [vector_space K V] [vector_space F V]
  [is_scalar_tower F K V] [hf : finite_dimensional F V] :
  finite_dimensional K V :=
let ⟨b, hb⟩ := finite_dimensional.iff_fg.1 hf in
finite_dimensional.iff_fg.2 ⟨b, @submodule.restrict_scalars'_injective F _ _ _ _ _ _ _ _ _ _ _ $
by { rw [submodule.restrict_scalars'_top, eq_top_iff, ← hb, submodule.span_le],
  exact submodule.subset_span }⟩

instance finite_dimensional_linear_map (F : Type u) (V : Type v) (W : Type w)
  [field F] [add_comm_group V] [vector_space F V] [add_comm_group W] [vector_space F W]
  [finite_dimensional F V] [finite_dimensional F W] :
  finite_dimensional F (V →ₗ[F] W) :=
let ⟨b, hb⟩ := finite_dimensional.exists_is_basis_finset F V in
let ⟨c, hc⟩ := finite_dimensional.exists_is_basis_finset F W in
linear_equiv.finite_dimensional (linear_equiv_matrix hb hc).symm

open finite_dimensional

theorem findim_linear_map (F : Type u) (V : Type v) (W : Type w)
  [field F] [add_comm_group V] [vector_space F V] [add_comm_group W] [vector_space F W]
  [finite_dimensional F V] [finite_dimensional F W] :
  findim F (V →ₗ[F] W) = findim F V * findim F W :=
let ⟨b, hb⟩ := finite_dimensional.exists_is_basis_finset F V in
let ⟨c, hc⟩ := finite_dimensional.exists_is_basis_finset F W in
by rw [linear_equiv.findim_eq (linear_equiv_matrix hb hc), matrix.findim_matrix,
      findim_eq_card_basis hb, findim_eq_card_basis hc, mul_comm]

-- TODO: generalize by removing [finite_dimensional F K]
instance finite_dimensional_linear_map' (F : Type u) (K : Type v) (V : Type w)
  [field F] [field K] [add_comm_group V] [vector_space F V] [finite_dimensional F V]
  [algebra F K] [finite_dimensional F K] :
  finite_dimensional K (V →ₗ[F] K) :=
finite_dimensional_of_right F _ _

-- V = ⊕F,
-- (V →ₗ[F] K) = ((⊕F) →ₗ[F] K) = (⊕ (F →ₗ[F] K)) = (⊕K) is finite over K

theorem findim_linear_map' (F : Type u) [field F] (K : Type v) [field K]
  [algebra F K] [finite_dimensional F K] :
  findim K (K →ₗ[F] K) = findim F K :=
(nat.mul_right_inj $ show 0 < findim F K, from findim_pos).1 $
calc  findim F K * findim K (K →ₗ[F] K)
    = findim F (K →ₗ[F] K) : findim_mul_findim _ _ _
... = findim F K * findim F K : findim_linear_map F K K

lemma linear_independent_of_comp {R : Type u} {M : Type v} {N : Type w} {ι : Type*}
  [comm_ring R] [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  (f : M →ₗ[R] N) (v : ι → M) (hfv : linear_independent R (f ∘ v)) :
  linear_independent R v :=
linear_independent_iff'.2 $ λ s g hg i his,
have ∑ (i : ι) in s, g i • f (v i) = 0,
  by simp_rw [← f.map_smul, ← f.map_sum, hg, f.map_zero],
linear_independent_iff'.1 hfv s g this i his

def linear_map.lto_fun (R : Type u) (M : Type v) (A : Type w)
  [comm_semiring R] [add_comm_monoid M] [semimodule R M] [comm_ring A] [algebra R A] :
  (M →ₗ[R] A) →ₗ[A] (M → A) :=
{ to_fun := linear_map.to_fun,
  map_add' := λ f g, rfl,
  map_smul' := λ c f, rfl }

lemma linear_independent_to_linear_map (R : Type u) (A : Type v)
  [comm_semiring R] [integral_domain A] [algebra R A] :
  linear_independent A (alg_hom.to_linear_map : (A →ₐ[R] A) → (A →ₗ[R] A)) :=
have linear_independent A (linear_map.lto_fun R A A ∘ alg_hom.to_linear_map),
from ((linear_independent_monoid_hom A A).comp
  (coe : (A →ₐ[R] A) → (A →* A))
  (λ f g hfg, alg_hom.ext $ monoid_hom.ext_iff.1 hfg) : _),
linear_independent_of_comp _ _ this

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

#G ≤ #(F →ₐ[fixed_points G F] F) ≤ dim F (F →ₗ[fixed_points G F] F) = dim (fixed_points G F) F
-/

#check fintype_card_le_findim_of_linear_independent
#check cardinal_mk_le_findim_of_linear_independent
