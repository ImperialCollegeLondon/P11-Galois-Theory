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


-- https://github.com/leanprover/mathlib/pull/461/
theorem is_noetherian_ring_polynomial (hnr : is_noetherian_ring R) : is_noetherian_ring (polynomial R) := sorry
theorem is_noetherian_ring_closure (σ : set R) (hfσ : set.finite σ) :
  is_noetherian_ring (ring.closure σ) := sorry