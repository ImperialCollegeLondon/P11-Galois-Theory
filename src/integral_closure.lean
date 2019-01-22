/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Integral closure of a subring.
-/

import .adjoin .hilbert_basis

universes u v

theorem ring.closure_union_eq_range {R : Type u} {A : Type v}
  [comm_ring R] [comm_ring A] [decidable_eq R] [decidable_eq A]
  (i : algebra R A) (σ : set A) :
  i.adjoin σ = (mv_polynomial.aeval R A i σ).range :=
begin
  ext r, change _ ↔ r ∈ set.range (mv_polynomial.eval₂ i (subtype.val : σ → A)),
  split; intro hr,
  { refine ring.in_closure.rec_on hr _ _ _ _,
    { exact ⟨1, mv_polynomial.eval₂_one _ _⟩ },
    { refine ⟨-1, _⟩, rw [mv_polynomial.eval₂_neg, mv_polynomial.eval₂_one] },
    { rintros s (⟨s, rfl⟩ | hs) r ⟨p, rfl⟩,
      { refine ⟨mv_polynomial.C s * p, _⟩,
        rw [mv_polynomial.eval₂_mul, mv_polynomial.eval₂_C] },
      { refine ⟨mv_polynomial.X ⟨s, hs⟩ * p, _⟩,
        rw [mv_polynomial.eval₂_mul, mv_polynomial.eval₂_X] } },
    { rintros x y ⟨p, rfl⟩ ⟨q, rfl⟩,
      exact ⟨p + q, mv_polynomial.eval₂_add _ _⟩ } },
  rcases hr with ⟨f, rfl⟩,
  refine mv_polynomial.induction_on f _ _ _,
  { intro s, rw mv_polynomial.eval₂_C,
    exact (i.adjoin σ).range_le ⟨s, rfl⟩ },
  { intros p q hp hq,
    rw mv_polynomial.eval₂_add,
    exact subalgebra.mem_coe.1 (is_add_submonoid.add_mem hp hq) },
  { intros p t hp,
    rw [mv_polynomial.eval₂_mul, mv_polynomial.eval₂_X],
    exact subalgebra.mem_coe.1 (is_submonoid.mul_mem hp (ring.subset_closure (or.inr t.2))) }
end

namespace polynomial
variables {R : Type u} {A : Type v}
variables [comm_ring R] [comm_ring A]
variables [decidable_eq R] [decidable_eq A]
variables (i : algebra R A)

theorem adjoin_singleton_eq_range (x : A) :
  i.adjoin {x} = (aeval R i x).range :=
begin
  rw ring.closure_union_eq_range, ext r,
  change r ∈ set.range (mv_polynomial.eval₂ i (subtype.val : ({x} : set A) → A)) ↔ r ∈ set.range (eval₂ i x),
  split; rintro ⟨p, rfl⟩,
  { refine ⟨mv_polynomial.eval₂ C (λ _, X) p, _⟩,
    refine mv_polynomial.induction_on p _ _ _,
    { intro s, rw [mv_polynomial.eval₂_C, mv_polynomial.eval₂_C, eval₂_C] },
    { intros p q hp hq,
      rw [mv_polynomial.eval₂_add, mv_polynomial.eval₂_add, eval₂_add, hp, hq] },
    { intros p x' hp,
      rw [mv_polynomial.eval₂_mul, mv_polynomial.eval₂_X, mv_polynomial.eval₂_mul, mv_polynomial.eval₂_X],
      rw [eval₂_mul, eval₂_X, hp],
      rcases x' with ⟨_, rfl | H⟩, {refl}, {cases H} } },
  refine ⟨eval₂ mv_polynomial.C (mv_polynomial.X ⟨x, or.inl rfl⟩) p, _⟩,
  refine polynomial.induction_on p _ _ _,
  { intro s, rw [eval₂_C, mv_polynomial.eval₂_C, eval₂_C] },
  { intros p q hp hq,
    rw [eval₂_add, mv_polynomial.eval₂_add, eval₂_add, hp, hq] },
  { intros n x' ih,
    haveI : is_ring_hom (mv_polynomial.C : R → mv_polynomial ({x} : set A) R) := mv_polynomial.C.is_ring_hom,
    haveI : is_semiring_hom (mv_polynomial.C : R → mv_polynomial ({x} : set A) R) := is_ring_hom.is_semiring_hom _,
    rw [pow_succ', ← mul_assoc, eval₂_mul mv_polynomial.C (mv_polynomial.X (⟨x, _⟩ : ({x} : set A))), mv_polynomial.eval₂_mul, ih],
    conv_rhs {rw eval₂_mul},
    rw [eval₂_X, mv_polynomial.eval₂_X, eval₂_X],
    exact _inst_5 }
end

def restriction (p : polynomial R) : polynomial (ring.closure (↑p.frange : set R)) :=
⟨p.support, λ i, ⟨p.to_fun i,
  if H : p.to_fun i = 0 then H.symm ▸ is_add_submonoid.zero_mem _
  else ring.subset_closure $ finsupp.mem_frange.2 ⟨H, i, rfl⟩⟩,
λ i, finsupp.mem_support_iff.trans (not_iff_not_of_iff ⟨λ H, subtype.eq H, subtype.mk.inj⟩)⟩

theorem coeff_restriction {p : polynomial R} {n : ℕ} : ↑(coeff (restriction p) n) = coeff p n := rfl

theorem coeff_restriction' {p : polynomial R} {n : ℕ} : (coeff (restriction p) n).1 = coeff p n := rfl

theorem degree_restriction {p : polynomial R} : (restriction p).degree = p.degree := rfl

theorem nat_degree_restriction {p : polynomial R} : (restriction p).nat_degree = p.nat_degree := rfl

theorem monic_restriction {p : polynomial R} : monic (restriction p) ↔ monic p :=
⟨λ H, congr_arg subtype.val H, λ H, subtype.eq H⟩

theorem restriction_zero : restriction (0 : polynomial R) = 0 := rfl

theorem restriction_one : restriction (1 : polynomial R) = 1 :=
ext.2 $ λ i, subtype.eq $ by rw [coeff_restriction', coeff_one, coeff_one]; split_ifs; refl

variables {S : Type v} [comm_ring S] {f : R → S} {x : S}

theorem eval₂_restriction {p : polynomial R} :
  eval₂ f x p = eval₂ (f ∘ subtype.val) x p.restriction :=
rfl

section base_change
variables (p : polynomial R) (T : set R) [is_subring T]

def base_change (hp : ↑p.frange ⊆ T) : polynomial T :=
⟨p.support, λ i, ⟨p.to_fun i,
  if H : p.to_fun i = 0 then H.symm ▸ is_add_submonoid.zero_mem _
  else hp $ finsupp.mem_frange.2 ⟨H, i, rfl⟩⟩,
λ i, finsupp.mem_support_iff.trans (not_iff_not_of_iff ⟨λ H, subtype.eq H, subtype.mk.inj⟩)⟩

variables (hp : ↑p.frange ⊆ T)
include hp

theorem coeff_base_change {n : ℕ} : ↑(coeff (base_change p T hp) n) = coeff p n := rfl

theorem coeff_base_change' {n : ℕ} : (coeff (base_change p T hp) n).1 = coeff p n := rfl

theorem degree_base_change : (base_change p T hp).degree = p.degree := rfl

theorem nat_degree_base_change : (base_change p T hp).nat_degree = p.nat_degree := rfl

theorem monic_base_change : monic (base_change p T hp) ↔ monic p :=
⟨λ H, congr_arg subtype.val H, λ H, subtype.eq H⟩

omit hp

theorem base_change_zero : base_change (0 : polynomial R) T (set.empty_subset _) = 0 := rfl

theorem base_change_one : base_change (1 : polynomial R) T
  (set.subset.trans (finset.coe_subset.2 finsupp.frange_single)
    (set.singleton_subset_iff.2 (is_submonoid.one_mem _))) = 1 :=
ext.2 $ λ i, subtype.eq $ by rw [coeff_base_change', coeff_one, coeff_one]; split_ifs; refl
end base_change

variables (T : set R) [is_subring T]

def of_subtype (p : polynomial T) : polynomial R :=
⟨p.support, subtype.val ∘ p.to_fun,
λ n, finsupp.mem_support_iff.trans (not_iff_not_of_iff
  ⟨λ h, congr_arg subtype.val h, λ h, subtype.eq h⟩)⟩

theorem frange_of_subtype {p : polynomial T} :
  ↑(p.of_subtype T).frange ⊆ T :=
λ y H, let ⟨hy, x, hx⟩ := finsupp.mem_frange.1 H in hx ▸ (p.to_fun x).2

end polynomial

open polynomial submodule

variables {R : Type u} {A : Type v}
variables [comm_ring R] [comm_ring A]
variables [decidable_eq R] [decidable_eq A]
variables (i : algebra R A)

def is_integral (x : A) : Prop :=
∃ p : polynomial R, monic p ∧ aeval R i x p = 0

theorem is_integral_i (x) : is_integral i (i x) :=
⟨X - C x, monic_X_sub_C _,
by rw [alg_hom.map_sub, aeval_def, aeval_def, eval₂_X, eval₂_C, sub_self]⟩

theorem is_integral_of_subring {x} (T : set R) [is_subring T]
  (hx : is_integral ((algebra.of_subring T).comap i) x) : is_integral i x :=
let ⟨p, hpm, hpx⟩ := hx in
⟨⟨p.support, λ n, (p.to_fun n).1,
  λ n, finsupp.mem_support_iff.trans (not_iff_not_of_iff
    ⟨λ H, have _ := congr_arg subtype.val H, this,
    λ H, subtype.eq H⟩)⟩,
have _ := congr_arg subtype.val hpm, this, hpx⟩

theorem is_integral_iff_is_integral_closure_finite {r : A} :
  is_integral i r ↔ ∃ s : set R, s.finite ∧ is_integral ((algebra.of_subring (ring.closure s)).comap i) r :=
begin
  split; intro hr,
  { rcases hr with ⟨p, hmp, hpr⟩,
    exact ⟨_, set.finite_mem_finset _, p.restriction, subtype.eq hmp, hpr⟩ },
  rcases hr with ⟨s, hs, hsr⟩,
  exact is_integral_of_subring _ _ hsr
end

theorem fg_madjoin_singleton_of_integral (x : A) (hx : is_integral i x) :
  (i.adjoin {x}).to_submodule.fg :=
begin
  rcases hx with ⟨f, hfm, hfx⟩,
  existsi finset.image ((^) x) (finset.range (nat_degree f + 1)),
  apply le_antisymm,
  { rw span_le, intros s hs, rw finset.mem_coe at hs,
    rcases finset.mem_image.1 hs with ⟨k, hk, rfl⟩, clear hk,
    exact is_submonoid.pow_mem (ring.subset_adjoin (set.mem_singleton _)) },
  intros r hr, change r ∈ i.adjoin _ at hr,
  rw adjoin_singleton_eq_range at hr, rcases hr with ⟨p, rfl⟩,
  rw ← mod_by_monic_add_div p hfm,
  rw [alg_hom.map_add, alg_hom.map_mul, hfx, zero_mul, add_zero],
  have : degree (p %ₘ f) ≤ degree f := degree_mod_by_monic_le p hfm,
  generalize_hyp : p %ₘ f = q at this ⊢,
  rw [← sum_C_mul_X_eq q, aeval_def, eval₂_sum, finsupp.sum, mem_coe],
  refine sum_mem _ (λ k hkq, _),
  rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← algebra.smul_def],
  refine smul_mem _ _ (subset_span _),
  rw finset.mem_coe, refine finset.mem_image.2 ⟨_, _, rfl⟩,
  rw [finset.mem_range, nat.lt_succ_iff], refine le_of_not_lt (λ hk, _),
  rw [degree_le_iff_coeff_zero] at this,
  rw [finsupp.mem_support_iff] at hkq, apply hkq, apply this,
  exact lt_of_le_of_lt degree_le_nat_degree (with_bot.coe_lt_coe.2 hk)
end

theorem fg_madjoin_of_finite {s : set A} (hfs : s.finite)
  (his : ∀ x ∈ s, is_integral i x) : (i.adjoin s).to_submodule.fg :=
set.finite.induction_on hfs (λ _, ⟨finset.singleton 1, le_antisymm
  (span_le.2 $ set.singleton_subset_iff.2 $ is_submonoid.one_mem _)
  (show ring.closure _ ⊆ _, by rw set.union_empty; exact
    set.subset.trans (ring.closure_subset (set.subset.refl _))
    (λ y ⟨x, hx⟩, hx ▸ mul_one (i x) ▸ i.smul_def x 1 ▸ (mem_coe _).2
      (submodule.smul_mem _ x $ subset_span $ or.inl rfl)))⟩)
(λ a s has hs ih his, by rw [← set.union_singleton, ring.madjoin_union]; exact
  ring.fg_mul (ih $ λ i hi, his i $ set.mem_insert_of_mem a hi)
    (fg_madjoin_singleton_of_integral _ _ $ his a $ set.mem_insert a s)) his

theorem is_integral_of_noetherian' (H : is_noetherian R i.mod) (x : A) :
  is_integral i x :=
begin
  let leval : polynomial R →ₗ i.mod := (aeval R i x).to_linear_map,
  let D : ℕ → submodule R i.mod := λ n, (degree_le R n).map leval,
  let M := well_founded.min (is_noetherian_iff_well_founded.1 H)
    (set.range D) (set.ne_empty_of_mem ⟨0, rfl⟩),
  have HM : M ∈ set.range D := well_founded.min_mem _ _ _,
  cases HM with N HN,
  have HM : ¬M < D (N+1) := well_founded.not_lt_min
    (is_noetherian_iff_well_founded.1 H) (set.range D) _ ⟨N+1, rfl⟩,
  rw ← HN at HM,
  have HN2 : D (N+1) ≤ D N := classical.by_contradiction (λ H, HM
    (lt_of_le_not_le (map_mono (degree_le_mono
      (with_bot.coe_le_coe.2 (nat.le_succ N)))) H)),
  have HN3 : leval (X^(N+1)) ∈ D N,
  { exact HN2 (mem_map_of_mem (mem_degree_le.2 (degree_X_pow_le _))) },
  rcases HN3 with ⟨p, hdp, hpe⟩,
  refine ⟨X^(N+1) - p, monic_X_pow_sub (mem_degree_le.1 hdp), _⟩,
  show leval (X ^ (N + 1) - p) = 0,
  rw [linear_map.map_sub, hpe, sub_self]
end

theorem is_integral_of_noetherian (M : subalgebra i)
  (H : is_noetherian R M.to_submodule) (x : A) (hx : x ∈ M.to_submodule) :
  is_integral i x :=
begin
  suffices : is_integral M.algebra ⟨x, hx⟩,
  { rcases this with ⟨p, hpm, hpx⟩,
    replace hpx := congr_arg subtype.val hpx,
    refine ⟨p, hpm, eq.trans _ hpx⟩,
    simp only [aeval_def, eval₂, finsupp.sum],
    rw ← finset.sum_hom subtype.val,
    { refine finset.sum_congr rfl (λ n hn, _),
      change _ = _ * _,
      rw is_semiring_hom.map_pow subtype.val, refl,
      split; intros; refl },
    constructor; intros; refl },
  refine is_integral_of_noetherian' _ H ⟨x, hx⟩
end

theorem is_integral_of_mem_of_fg (M : subalgebra i)
  (HM : M.to_submodule.fg) (x : A) (hx : x ∈ M) : is_integral i x :=
begin
  cases HM with m hm,
  have hxm : x ∈ M.to_submodule := hx,
  rw [← hm, mem_span_iff_lc] at hxm,
  rcases hxm with ⟨lx, hlx1, hlx2⟩,
  have : ∀ (jk : (↑(m.product m) : set (i.mod × i.mod))), jk.1.1 * jk.1.2 ∈ span (↑m : set i.mod),
  { intros jk,
    let j : ↥(↑m : set i.mod) := ⟨jk.1.1, (finset.mem_product.1 jk.2).1⟩,
    let k : ↥(↑m : set i.mod) := ⟨jk.1.2, (finset.mem_product.1 jk.2).2⟩,
    have hj : j.1 ∈ span (↑m : set i.mod) := subset_span j.2,
    have hk : k.1 ∈ span (↑m : set i.mod) := subset_span k.2,
    revert hj hk, rw hm, exact @is_submonoid.mul_mem i.mod _ M.to_submodule _ j.1 k.1 },
  simp only [mem_span_iff_lc] at this,
  choose lm hlm1 hlm2,
  let S₀' : finset R := lx.frange ∪ finset.bind finset.univ (finsupp.frange ∘ lm),
  let S₀ : set R := ring.closure ↑S₀',
  apply is_integral_of_subring i (ring.closure ↑S₀'),
  have : span (insert 1 (↑m:set i.mod) : set ((algebra.of_subring S₀).comap i).mod) = (((algebra.of_subring S₀).comap i).adjoin (↑m : set i.mod)).to_submodule,
  { apply le_antisymm,
    { exact span_le.2 (set.insert_subset.2 ⟨is_submonoid.one_mem _, ring.subset_adjoin⟩) },
    rw [ring.madjoin_eq_span, span_le], intros r hr, refine monoid.in_closure.rec_on hr _ _ _,
    { intros r hr, exact subset_span (set.mem_insert_of_mem _ hr) },
    { exact subset_span (set.mem_insert _ _) },
    intros r1 r2 hr1 hr2 ih1 ih2, simp only [mem_coe, mem_span_iff_lc] at ih1 ih2,
    have ih1' := ih1, have ih2' := ih2,
    rcases ih1' with ⟨l1, hl1, rfl⟩, rcases ih2' with ⟨l2, hl2, rfl⟩,
    simp only [lc.total_apply, finsupp.sum_mul, finsupp.mul_sum, mem_coe],
    rw [finsupp.sum], refine sum_mem _ _, intros r2 hr2,
    rw [finsupp.sum], refine sum_mem _ _, intros r1 hr1,
    rw [algebra.mul_smul, algebra.smul_mul], refine smul_mem _ _ (smul_mem _ _ _),
    rcases hl1 hr1 with rfl | hr1,
    { rw one_mul, exact subset_span (hl2 hr2) },
    rcases hl2 hr2 with rfl | hr2,
    { rw mul_one, exact subset_span (set.mem_insert_of_mem _ hr1) },
    let jk : ↥(↑(finset.product m m) : set (i.mod × i.mod)) := ⟨(r1, r2), finset.mem_product.2 ⟨hr1, hr2⟩⟩,
    specialize hlm2 jk, change _ = r1 * r2 at hlm2, rw [← hlm2, lc.total_apply],
    rw [finsupp.sum], refine sum_mem _ _, intros z hz,
    have : lm jk z ∈ S₀,
    { apply ring.subset_closure,
      apply finset.mem_union_right, apply finset.mem_bind.2,
      exact ⟨jk, finset.mem_univ _, finset.mem_image_of_mem _ hz⟩ },
    rw i.smul_def,
    change @has_scalar.smul S₀ ((algebra.of_subring S₀).comap i).mod _ ⟨lm jk z, this⟩ z ∈ _,
    exact smul_mem _ _ (subset_span (set.mem_insert_of_mem _ (hlm1 _ hz))) },
  apply is_integral_of_noetherian ((algebra.of_subring S₀).comap i)
    (((algebra.of_subring S₀).comap i).adjoin (↑m : set i.mod))
    (is_noetherian_of_fg_of_noetherian _ (by convert is_noetherian_ring_closure _ (finset.finite_to_set _); apply_instance)
      ⟨insert 1 m, by rw [finset.coe_insert, this]⟩),
  rw [← hlx2, lc.total_apply, finsupp.sum], refine sum_mem _ _, intros r hr,
  rw [← this, i.smul_def],
  have : lx r ∈ ring.closure ↑S₀' :=
    ring.subset_closure (finset.mem_union_left _ (finset.mem_image_of_mem _ hr)),
  change @has_scalar.smul S₀ ((algebra.of_subring S₀).comap i).mod _ ⟨lx r, this⟩ r ∈ _,
  exact smul_mem _ _ (subset_span (set.mem_insert_of_mem _ (hlx1 hr)))
end

theorem is_integral_of_mem_closure {x y z : A}
  (hx : is_integral i x) (hy : is_integral i y)
  (hz : z ∈ ring.closure ({x, y} : set A)) :
  is_integral i z :=
begin
  have := ring.fg_mul (fg_madjoin_singleton_of_integral i x hx) (fg_madjoin_singleton_of_integral i y hy),
  rw [← ring.madjoin_union, set.union_singleton, insert] at this,
  exact is_integral_of_mem_of_fg i (i.adjoin {x, y}) this z
    (ring.closure_mono (set.subset_union_right _ _) hz)
end

theorem is_integral_zero : is_integral i 0 :=
i.map_zero ▸ is_integral_i i 0

theorem is_integral_one : is_integral i 1 :=
i.map_one ▸ is_integral_i i 1

theorem is_integral_add {x y : A}
  (hx : is_integral i x) (hy : is_integral i y) :
  is_integral i (x + y) :=
is_integral_of_mem_closure i hx hy (is_add_submonoid.add_mem
  (ring.subset_closure (or.inr (or.inl rfl))) (ring.subset_closure (or.inl rfl)))

theorem is_integral_neg {x : A}
  (hx : is_integral i x) : is_integral i (-x) :=
is_integral_of_mem_closure i hx hx (is_add_subgroup.neg_mem
  (ring.subset_closure (or.inl rfl))) 

theorem is_integral_sub {x y : A}
  (hx : is_integral i x) (hy : is_integral i y) : is_integral i (x - y) :=
is_integral_add i hx (is_integral_neg i hy)

theorem is_integral_mul {x y : A}
  (hx : is_integral i x) (hy : is_integral i y) :
  is_integral i (x * y) :=
is_integral_of_mem_closure i hx hy (is_submonoid.mul_mem
  (ring.subset_closure (or.inr (or.inl rfl))) (ring.subset_closure (or.inl rfl)))

def integral_closure : subalgebra i :=
{ carrier := { r | is_integral i r },
  subring :=
  { zero_mem := is_integral_zero i,
    one_mem := is_integral_one i,
    add_mem := λ _ _, is_integral_add i,
    neg_mem := λ _, is_integral_neg i,
    mul_mem := λ _ _, is_integral_mul i },
  range_le := λ y ⟨x, hx⟩, hx ▸ is_integral_i i x }

theorem mem_integral_closure_iff_mem_fg {r : A} :
  r ∈ integral_closure i ↔ ∃ M : subalgebra i, M.to_submodule.fg ∧ r ∈ M :=
⟨λ hr, ⟨i.adjoin {r}, fg_madjoin_singleton_of_integral _ _ hr, ring.subset_adjoin (or.inl rfl)⟩,
λ ⟨M, Hf, hrM⟩, is_integral_of_mem_of_fg _ M Hf _ hrM⟩

theorem integral_closure_idem : integral_closure (algebra.of_subring (integral_closure i : set A)) = ⊥ :=
begin
  rw lattice.eq_bot_iff, intros r hr,
  rcases (is_integral_iff_is_integral_closure_finite _).1 hr with ⟨s, hfs, hr⟩,
  apply (algebra.mem_bot _).2, refine ⟨⟨_, _⟩, rfl⟩,
  refine (mem_integral_closure_iff_mem_fg _).2 ⟨i.adjoin (subtype.val '' s ∪ {r}),
    ring.fg_trans
      (fg_madjoin_of_finite _ (set.finite_image _ hfs)
        (λ y ⟨x, hx, hxy⟩, hxy ▸ x.2))
      (fg_madjoin_singleton_of_integral _ _ _),
    ring.subset_adjoin (or.inr (or.inl rfl))⟩,
  rcases hr with ⟨p, hmp, hpx⟩,
  refine ⟨base_change (of_subtype _ (of_subtype _ p)) _ _, _, hpx⟩,
  { intros x hx, rcases finsupp.mem_frange.1 hx with ⟨h1, n, rfl⟩,
    change (coeff p n).1.1 ∈ _,
    rcases ring.exists_list_of_mem_closure' (coeff p n).2 with ⟨L, HL1, HL2⟩, rw ← HL2,
    clear HL2 hfs h1 hx n hmp hpx hr r p,
    induction L with hd tl ih, { exact is_add_submonoid.zero_mem _ },
    rw list.forall_mem_cons at HL1,
    rw [list.map_cons, list.sum_cons],
    refine is_add_submonoid.add_mem _ (ih HL1.2),
    cases HL1 with HL HL', clear HL' ih tl,
    induction hd with hd tl ih, { exact is_submonoid.one_mem _ },
    rw list.forall_mem_cons at HL,
    rw list.prod_cons,
    refine is_submonoid.mul_mem _ (ih HL.2),
    rcases HL.1 with hs | rfl,
    { exact ring.subset_adjoin (set.mem_image_of_mem _ hs) },
    exact is_add_subgroup.neg_mem (is_submonoid.one_mem _) },
  replace hmp := congr_arg subtype.val hmp,
  replace hmp := congr_arg subtype.val hmp,
  exact subtype.eq hmp
end