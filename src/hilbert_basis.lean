import linear_algebra.multivariate_polynomial
import data.polynomial
import ring_theory.principal_ideal_domain
import ring_theory.subring

universes u v

-- data.finsupp START

namespace finsupp
section frange
variables {α : Type*} {β : Type*}
variables [decidable_eq α] [decidable_eq β] [has_zero β]

def frange (f : α →₀ β) : finset β :=
finset.image f f.support

theorem mem_frange {f : α →₀ β} {y : β} :
  y ∈ f.frange ↔ y ≠ 0 ∧ ∃ x, f x = y :=
finset.mem_image.trans
⟨λ ⟨x, hx1, hx2⟩, ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩,
λ ⟨hy, x, hx⟩, ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩

theorem zero_not_mem_frange {f : α →₀ β} : (0:β) ∉ f.frange :=
λ H, (mem_frange.1 H).1 rfl

theorem frange_single {x : α} {y : β} : frange (single x y) ⊆ {y} :=
λ r hr, let ⟨t, ht1, ht2⟩ := mem_frange.1 hr in ht2 ▸
(by rw single_apply at ht2 ⊢; split_ifs at ht2 ⊢; [exact finset.mem_singleton_self _, cc])

end frange
end finsupp

-- data.finsupp END


-- data.int.basic START

namespace int
variables {α : Type*}
instance cast.is_ring_hom [ring α] :
  is_ring_hom (int.cast : ℤ → α) :=
⟨cast_one, cast_mul, cast_add⟩
end int

-- data.int.basic END


-- data.polynomial START

namespace polynomial

section coeff
variables (α : Type*) [comm_semiring α] [decidable_eq α]
variable α
@[simp] lemma coeff_X (n : ℕ) :
  coeff (X : polynomial α) n = if n = 1 then 1 else 0 :=
by simpa only [pow_one] using @coeff_X_pow α _ _ 1 n
end coeff

section comm_semiring
variables {α : Type*} [comm_semiring α] [decidable_eq α]
variables {p : polynomial α}
theorem monic_of_degree_le {R : Type u} [comm_semiring R] [decidable_eq R]
  {p : polynomial R} (n : ℕ) (H1 : degree p ≤ n) (H2 : coeff p n = 1) : monic p :=
decidable.by_cases
  (assume H : degree p < n, @subsingleton.elim _ (subsingleton_of_zero_eq_one R $
    H2 ▸ (coeff_eq_zero_of_degree_lt H).symm) _ _)
  (assume H : ¬degree p < n, by rwa [monic, leading_coeff, nat_degree, (lt_or_eq_of_le H1).resolve_left H])

theorem degree_C_mul_X_pow_le (r : α) (n : ℕ) : degree (C r * X^n) ≤ n :=
by rw [← single_eq_C_mul_X]; exact finset.sup_le (λ b hb,
by rw list.eq_of_mem_singleton (finsupp.support_single_subset hb); exact le_refl _)

theorem degree_X_pow_le (n : ℕ) : degree (X^n : polynomial α) ≤ n :=
by simpa only [C_1, one_mul] using degree_C_mul_X_pow_le (1:α) n

theorem degree_X_le : degree (X : polynomial α) ≤ 1 :=
by simpa only [C_1, one_mul, pow_one] using degree_C_mul_X_pow_le (1:α) 1

theorem monic_X_pow_add {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) + p) :=
have H1 : degree p < n+1, from lt_of_le_of_lt H (with_bot.coe_lt_coe.2 (nat.lt_succ_self n)),
monic_of_degree_le (n+1)
  (le_trans (degree_add_le _ _) (max_le (degree_X_pow_le _) (le_of_lt H1)))
  (by rw [coeff_add, coeff_X_pow, if_pos rfl, coeff_eq_zero_of_degree_lt H1, add_zero])

theorem degree_le_iff_coeff_zero (f : polynomial α) (n : with_bot ℕ) :
  degree f ≤ n ↔ ∀ m : ℕ, n < m → coeff f m = 0 :=
⟨λ (H : finset.sup (f.support) some ≤ n) m (Hm : n < (m : with_bot ℕ)), decidable.of_not_not $ λ H4,
  have H1 : m ∉ f.support,
    from λ H2, not_lt_of_ge ((finset.sup_le_iff.1 H) m H2 : ((m : with_bot ℕ) ≤ n)) Hm,
  H1 $ (finsupp.mem_support_to_fun f m).2 H4,
λ H, finset.sup_le $ λ b Hb, decidable.of_not_not $ λ Hn,
  (finsupp.mem_support_to_fun f b).1 Hb $ H b $ lt_of_not_ge Hn⟩

theorem nat_degree_le_of_degree_le {p : polynomial α} {n : ℕ}
  (H : degree p ≤ n) : nat_degree p ≤ n :=
show option.get_or_else (degree p) 0 ≤ n, from match degree p, H with
| none,     H := zero_le _
| (some d), H := with_bot.coe_le_coe.1 H
end

theorem leading_coeff_mul_X_pow {p : polynomial α} {n : ℕ} :
  leading_coeff (p * X ^ n) = leading_coeff p :=
decidable.by_cases
  (assume H : leading_coeff p = 0, by rw [H, leading_coeff_eq_zero.1 H, zero_mul, leading_coeff_zero])
  (assume H : leading_coeff p ≠ 0,
    by rw [leading_coeff_mul', leading_coeff_X_pow, mul_one];
       rwa [leading_coeff_X_pow, mul_one])
end comm_semiring

section comm_ring
variables {α : Type*} [comm_ring α] [decidable_eq α]
variables {p : polynomial α}
theorem monic_X_sub_C' (x : α) : monic (X - C x) :=
begin
  by_cases h01 : (0:α) = 1,
  { exact @subsingleton.elim _ (subsingleton_of_zero_eq_one _ h01) _ _ },
  change ite _ _ _ - ite _ _ _ = _,
  suffices : degree (X - C x) = 1,
  { have : nat_degree (X - C x) = 1,
    { unfold nat_degree, rw this, refl },
    rw [this, if_pos rfl, if_neg nat.zero_ne_one, sub_zero] },
  have : coeff (X - C x) 1 = 1,
  { change coeff X 1 - coeff (C x) 1 = 1,
    rw [coeff_X_one, coeff_C, if_neg nat.one_ne_zero, sub_zero] },
  apply le_antisymm,
  { apply le_trans (degree_add_le _ _) (max_le degree_X_le _),
    rw degree_neg, exact le_trans degree_C_le dec_trivial },
  { refine le_of_not_lt (λ H, h01 _),
    rwa [coeff_eq_zero_of_degree_lt H] at this }
end

theorem monic_X_pow_sub {n : ℕ} (H : degree p ≤ n) : monic (X ^ (n+1) - p) :=
monic_X_pow_add ((degree_neg p).symm ▸ H)

theorem degree_mod_by_monic_le (p : polynomial α) {q : polynomial α}
  (hq : monic q) : degree (p %ₘ q) ≤ degree q :=
decidable.by_cases
  (assume H : q = 0, by rw [monic, H, leading_coeff_zero] at hq;
    have : (0:polynomial α) = 1 := (by rw [← C_0, ← C_1, hq]);
    rw [eq_zero_of_zero_eq_one _ this (p %ₘ q), eq_zero_of_zero_eq_one _ this q]; exact le_refl _)
  (assume H : q ≠ 0, le_of_lt $ degree_mod_by_monic_lt _ hq H)

end comm_ring

end polynomial

-- data.polynomial END


-- ring_theory.subring START

namespace is_ring_hom

instance set.range.is_subring {R : Type u} {S : Type v} [ring R] [ring S]
  (f : R → S) [is_ring_hom f] : is_subring (set.range f) :=
{ zero_mem := ⟨0, is_ring_hom.map_zero f⟩,
  one_mem := ⟨1, is_ring_hom.map_one f⟩,
  neg_mem := λ x ⟨p, hp⟩, ⟨-p, hp ▸ is_ring_hom.map_neg f⟩,
  add_mem := λ x y ⟨p, hp⟩ ⟨q, hq⟩, ⟨p + q, hp ▸ hq ▸ is_ring_hom.map_add f⟩,
  mul_mem := λ x y ⟨p, hp⟩ ⟨q, hq⟩, ⟨p * q, hp ▸ hq ▸ is_ring_hom.map_mul f⟩, }

end is_ring_hom

-- ring_theory.subring END


-- ring_theory.noetherian START

namespace submodule

open set lattice

variables {α : Type*} {β : Type*} [ring α] [add_comm_group β] [module α β]

theorem fg_bot : (⊥ : submodule α β).fg :=
⟨∅, by rw [finset.coe_empty, span_empty]⟩

theorem fg_sup {s₁ s₂ : submodule α β}
  (hs₁ : s₁.fg) (hs₂ : s₂.fg) : (s₁ ⊔ s₂).fg :=
let ⟨t₁, ht₁⟩ := fg_def.1 hs₁, ⟨t₂, ht₂⟩ := fg_def.1 hs₂ in
fg_def.2 ⟨t₁ ∪ t₂, finite_union ht₁.1 ht₂.1, by rw [span_union, ht₁.2, ht₂.2]⟩

variables {γ : Type*} [add_comm_group γ] [module α γ]
variables {f : β →ₗ γ}

theorem fg_map {s : submodule α β} (hs : s.fg) : (s.map f).fg :=
let ⟨t, ht⟩ := fg_def.1 hs in fg_def.2 ⟨f '' t, finite_image _ ht.1, by rw [span_image, ht.2]⟩

theorem fg_prod {sb : submodule α β} {sc : submodule α γ}
  (hsb : sb.fg) (hsc : sc.fg) : (sb.prod sc).fg :=
let ⟨tb, htb⟩ := fg_def.1 hsb, ⟨tc, htc⟩ := fg_def.1 hsc in
fg_def.2 ⟨prod.inl '' tb ∪ prod.inr '' tc,
  finite_union (finite_image _ htb.1) (finite_image _ htc.1),
  by rw [linear_map.span_inl_union_inr, htb.2, htc.2]⟩

variable (f)
theorem fg_exact {s : submodule α β}
  (hs1 : (s.map f).fg) (hs2 : (s ⊓ f.ker).fg) : s.fg :=
begin
  haveI := classical.dec_eq β, haveI := classical.dec_eq γ,
  cases hs1 with t1 ht1, cases hs2 with t2 ht2,
  have : ∀ y ∈ t1, ∃ x ∈ s, f x = y,
  { intros y hy,
    have : y ∈ map f s, { rw ← ht1, exact subset_span hy },
    rcases mem_map.1 this with ⟨x, hx1, hx2⟩,
    exact ⟨x, hx1, hx2⟩ },
  have : ∃ g : γ → β, ∀ y ∈ t1, g y ∈ s ∧ f (g y) = y,
  { choose g hg1 hg2,
    existsi λ y, if H : y ∈ t1 then g y H else 0,
    intros y H, split,
    { simp only [dif_pos H], apply hg1 },
    { simp only [dif_pos H], apply hg2 } },
  cases this with g hg, clear this,
  existsi t1.image g ∪ t2,
  rw [finset.coe_union, span_union, finset.coe_image],
  apply le_antisymm,
  { refine sup_le (span_le.2 $ image_subset_iff.2 _) (span_le.2 _),
    { intros y hy, exact (hg y hy).1 },
    { intros x hx, have := subset_span hx,
      rw ht2 at this,
      exact this.1 } },
  intros x hx,
  have : f x ∈ map f s, { rw mem_map, exact ⟨x, hx, rfl⟩ },
  rw [← ht1, mem_span_iff_lc] at this,
  rcases this with ⟨l, hl1, hl2⟩,
  refine mem_sup.2 ⟨lc.total β ((lc.map g : lc α γ → lc α β) l), _,
    x - lc.total β ((lc.map g : lc α γ → lc α β) l), _, add_sub_cancel'_right _ _⟩,
  { rw mem_span_iff_lc, refine ⟨_, _, rfl⟩,
    rw [← lc.map_supported g, mem_map],
    exact ⟨_, hl1, rfl⟩ },
  rw [ht2, mem_inf], split,
  { apply s.sub_mem hx,
    rw [lc.total_apply, lc.map_apply, finsupp.sum_map_domain_index],
    refine s.sum_mem _,
    { intros y hy, exact s.smul_mem _ (hg y (hl1 hy)).1 },
    { exact zero_smul }, { exact λ _ _ _, add_smul _ _ _ } },
  { rw [linear_map.mem_ker, f.map_sub, ← hl2],
    rw [lc.total_apply, lc.total_apply, lc.map_apply],
    rw [finsupp.sum_map_domain_index, finsupp.sum, finsupp.sum, f.map_sum],
    rw sub_eq_zero,
    refine finset.sum_congr rfl (λ y hy, _),
    rw [f.map_smul, (hg y (hl1 hy)).2],
    { exact zero_smul }, { exact λ _ _ _, add_smul _ _ _ } }
end

end submodule

section
variables {α : Type*} {β : Type*} {γ : Type*}
variables [ring α] [add_comm_group β] [add_comm_group γ]
variables [module α β] [module α γ]
include α

open set lattice

theorem is_noetherian_submodule {N : submodule α β} :
  is_noetherian α N ↔ ∀ s : submodule α β, s ≤ N → s.fg :=
⟨λ hn s hs, have s ≤ N.subtype.range, from (N.range_subtype).symm ▸ hs,
  linear_map.map_comap_eq_self this ▸ submodule.fg_map (hn _),
λ h s, submodule.fg_exact N.subtype (h _ $ submodule.map_subtype_le _ _) $
  by rw [submodule.ker_subtype, inf_bot_eq]; exact submodule.fg_bot⟩

theorem is_noetherian_submodule_left {N : submodule α β} :
  is_noetherian α N ↔ ∀ s : submodule α β, (N ⊓ s).fg :=
is_noetherian_submodule.trans
⟨λ H s, H _ inf_le_left, λ H s hs, (inf_of_le_right hs) ▸ H _⟩

theorem is_noetherian_submodule_right {N : submodule α β} :
  is_noetherian α N ↔ ∀ s : submodule α β, (s ⊓ N).fg :=
is_noetherian_submodule.trans
⟨λ H s, H _ inf_le_right, λ H s hs, (inf_of_le_left hs) ▸ H _⟩

variable (β)
theorem is_noetherian_of_surjective (f : β →ₗ γ) (hf : f.range = ⊤)
  (hb : is_noetherian α β) : is_noetherian α γ :=
λ s, have (s.comap f).map f = s, from linear_map.map_comap_eq_self $ hf.symm ▸ le_top,
this ▸ submodule.fg_map $ hb _
variable {β}

theorem is_noetherian_of_linear_equiv (f : β ≃ₗ γ)
  (hb : is_noetherian α β) : is_noetherian α γ :=
is_noetherian_of_surjective _ f.to_linear_map f.range hb

theorem is_noetherian_prod (hb : is_noetherian α β)
  (hc : is_noetherian α γ) : is_noetherian α (β × γ) :=
λ s, submodule.fg_exact (linear_map.snd β γ) (hc _) $
have s ⊓ linear_map.ker (linear_map.snd β γ) ≤ linear_map.range (linear_map.inl β γ),
from λ x ⟨hx1, hx2⟩, ⟨x.1, trivial, prod.ext rfl $ eq.symm $ linear_map.mem_ker.1 hx2⟩,
linear_map.map_comap_eq_self this ▸ submodule.fg_map (hb _)

theorem is_noetherian_pi {α ι : Type*} {β : ι → Type*} [ring α]
  [Π i, add_comm_group (β i)] [Π i, module α (β i)] [fintype ι]
  (hb : ∀ i, is_noetherian α (β i)) : is_noetherian α (Π i, β i) :=
begin
  haveI := classical.dec_eq ι,
  suffices : ∀ s : finset ι, is_noetherian α (Π i : (↑s : set ι), β i),
  { refine is_noetherian_of_linear_equiv ⟨_, _, _, _, _, _⟩ (this finset.univ),
    { exact λ f i, f ⟨i, finset.mem_univ _⟩ },
    { intros, ext, refl },
    { intros, ext, refl },
    { exact λ f i, f i.1 },
    { intro, ext i, cases i, refl },
    { intro, ext i, refl } },
  intro s,
  induction s using finset.induction with a s has ih,
  { intro s, convert submodule.fg_bot, apply eq_bot_iff.2,
    intros x hx, refine submodule.mem_bot.2 _, ext i, cases i.2 },
  refine is_noetherian_of_linear_equiv ⟨_, _, _, _, _, _⟩ (is_noetherian_prod (hb a) ih),
  { exact λ f i, or.by_cases (finset.mem_insert.1 i.2)
      (λ h : i.1 = a, show β i.1, from (eq.rec_on h.symm f.1))
      (λ h : i.1 ∈ s, show β i.1, from f.2 ⟨i.1, h⟩) },
  { intros f g, ext i, unfold or.by_cases, cases i with i hi,
    rcases finset.mem_insert.1 hi with rfl | h,
    { change _ = _ + _, simp only [dif_pos], refl },
    { change _ = _ + _, have : ¬i = a, { rintro rfl, exact has h },
      simp only [dif_neg this, dif_pos h], refl } },
  { intros c f, ext i, unfold or.by_cases, cases i with i hi,
    rcases finset.mem_insert.1 hi with rfl | h,
    { change _ = c • _, simp only [dif_pos], refl },
    { change _ = c • _, have : ¬i = a, { rintro rfl, exact has h },
      simp only [dif_neg this, dif_pos h], refl } },
  { exact λ f, (f ⟨a, finset.mem_insert_self _ _⟩, λ i, f ⟨i.1, finset.mem_insert_of_mem i.2⟩) },
  { intro f, apply prod.ext,
    { simp only [or.by_cases, dif_pos] },
    { ext i, cases i with i his,
      have : ¬i = a, { rintro rfl, exact has his },
      dsimp only [or.by_cases], change i ∈ s at his,
      rw [dif_neg this, dif_pos his] } },
  { intro f, ext i, cases i with i hi,
    rcases finset.mem_insert.1 hi with rfl | h,
    { simp only [or.by_cases, dif_pos], refl },
    { have : ¬i = a, { rintro rfl, exact has h },
      simp only [or.by_cases, dif_neg this, dif_pos h], refl } }
end

omit α
theorem is_noetherian_of_fg_of_noetherian {R M} [ring R] [add_comm_group M] [module R M] (N : submodule R M)
  (h : is_noetherian_ring R) (hN : N.fg) : is_noetherian R N :=
let ⟨s, hs⟩ := hN in
begin
  haveI := classical.dec_eq M,
  have : ∀ x ∈ s, x ∈ N, from λ x hx, hs ▸ submodule.subset_span hx,
  refine @@is_noetherian_of_surjective ((↑s : set M) → R) _ _ _ (pi.module _)
    _ _ _ (is_noetherian_pi $ λ _, h),
  { fapply linear_map.mk,
    { exact λ f, ⟨s.attach.sum (λ i, f i • i.1), N.sum_mem (λ c _, N.smul_mem _ $ this _ c.2)⟩ },
    { intros f g, apply subtype.eq,
      change s.attach.sum (λ i, (f i + g i) • _) = _,
      simp only [add_smul, finset.sum_add_distrib], refl },
    { intros c f, apply subtype.eq,
      change s.attach.sum (λ i, (c • f i) • _) = _,
      simp only [smul_eq_mul, mul_smul],
      refine finset.sum_hom _ _ _,
      { apply smul_zero }, { apply smul_add } } },
  rw linear_map.range_eq_top,
  rintro ⟨n, hn⟩, change n ∈ N at hn,
  rw [← hs, mem_span_iff_lc] at hn,
  rcases hn with ⟨l, hl1, hl2⟩,
  refine ⟨λ x, l x.1, subtype.eq _⟩,
  change s.attach.sum (λ i, l i.1 • i.1) = n,
  rw [@finset.sum_attach M M s _ (λ i, l i • i), ← hl2,
      lc.total_apply, finsupp.sum, eq_comm],
  refine finset.sum_subset hl1 (λ x _ hx, _),
  rw [finsupp.not_mem_support_iff.1 hx, zero_smul]
end

end

-- ring_theory.noetherian END



variables (R : Type u) [comm_ring R] [decidable_eq R]

namespace polynomial

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree ≤ `n`. -/
def degree_le (n : with_bot ℕ) :
  submodule R (polynomial R) :=
⨅ k : ℕ, ⨅ h : ↑k > n, (lcoeff R k).ker

variable {R}

theorem mem_degree_le {n : with_bot ℕ} {f : polynomial R} :
  f ∈ degree_le R n ↔ degree f ≤ n :=
by simp only [degree_le, submodule.mem_infi, degree_le_iff_coeff_zero, linear_map.mem_ker]; refl

theorem degree_le_mono {m n : with_bot ℕ} (H : m ≤ n):
  degree_le R m ≤ degree_le R n :=
λ f hf, mem_degree_le.2 (le_trans (mem_degree_le.1 hf) H)

theorem degree_le_eq_span_X_pow {n : ℕ} :
  degree_le R n = submodule.span ↑((finset.range (n+1)).image (λ n, X^n) : finset (polynomial R)) :=
begin
  apply le_antisymm,
  { intros p hp, replace hp := mem_degree_le.1 hp,
    rw [← finsupp.sum_single p, finsupp.sum, submodule.mem_coe],
    refine submodule.sum_mem _ (λ k hk, _),
    have := with_bot.coe_le_coe.1 (finset.sup_le_iff.1 hp k hk),
    rw [single_eq_C_mul_X, C_mul'],
    refine submodule.smul_mem _ _ (submodule.subset_span $ finset.mem_coe.2 $
      finset.mem_image.2 ⟨_, finset.mem_range.2 (nat.lt_succ_of_le this), rfl⟩) },
  rw [submodule.span_le, finset.coe_image, set.image_subset_iff],
  intros k hk, apply mem_degree_le.2,
  apply le_trans (degree_X_pow_le _) (with_bot.coe_le_coe.2 $ nat.le_of_lt_succ $ finset.mem_range.1 hk)
end

end polynomial

variables {R}

-- https://github.com/leanprover/mathlib/pull/461/
theorem is_noetherian_ring_polynomial (hnr : is_noetherian_ring R) : is_noetherian_ring (polynomial R) := sorry
theorem is_noetherian_ring_closure (σ : set R) (hfσ : set.finite σ) :
  is_noetherian_ring (ring.closure σ) := sorry