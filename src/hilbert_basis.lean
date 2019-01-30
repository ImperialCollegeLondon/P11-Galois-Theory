import linear_algebra.multivariate_polynomial
import ring_theory.polynomial
import ring_theory.principal_ideal_domain
import ring_theory.subring

universes u v

variables {R : Type u} [comm_ring R] [decidable_eq R]

-- https://github.com/leanprover/mathlib/pull/461/
theorem is_noetherian_ring_closure (σ : set R) (hfσ : set.finite σ) :
  is_noetherian_ring (ring.closure σ) := sorry