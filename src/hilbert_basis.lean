import linear_algebra.multivariate_polynomial
import data.polynomial
import ring_theory.principal_ideal_domain
import ring_theory.subring

universes u v

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
  degree_le R n = submodule.span R ↑((finset.range (n+1)).image (λ n, X^n) : finset (polynomial R)) :=
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