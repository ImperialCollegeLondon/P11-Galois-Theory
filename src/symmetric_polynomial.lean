/- Symmetric polynomials. -/

import .polynomial_action

noncomputable theory
local attribute [instance] classical.dec
universes u v w

variables (G : Type u) [fintype G] [group G] (R : Type v) [comm_ring R] [mul_semiring_action G R]

def mul_semiring_action.polynomial (x : R) : polynomial R :=
(finset.univ : finset G).prod $ λ g, polynomial.X - polynomial.C (g • x)

theorem polynomial.monic_prod {R : Type u} [comm_semiring R] {ι : Type v}
  (s : finset ι) (f : ι → polynomial R) (H : ∀ i ∈ s, polynomial.monic (f i)) :
  polynomial.monic (s.prod f) :=
finset.induction_on s (λ _, polynomial.monic_one)
  (λ a s has ih H, by rw finset.prod_insert has; rw finset.forall_mem_insert at H;
    exact polynomial.monic_mul H.1 (ih H.2)) H

theorem mul_semiring_action.polynomial.monic (x : R) :
  polynomial.monic (mul_semiring_action.polynomial G R x) :=
polynomial.monic_prod _ _ $ λ g _, polynomial.monic_X_sub_C (g • x)

theorem mul_semiring_action.polynomial.eval (x : R) :
  (mul_semiring_action.polynomial G R x).eval x = 0 :=
(finset.prod_hom _ (polynomial.eval x)).symm.trans $ finset.prod_eq_zero (finset.mem_univ 1) $
by rw [one_smul, polynomial.eval_sub, polynomial.eval_X, polynomial.eval_C, sub_self]

theorem finset.smul_prod {M : Type u} [monoid M] {R : Type v} [comm_semiring R]
  [mul_semiring_action M R] {ι : Type w} (s : finset ι) (f : ι → R) (m : M) :
  m • s.prod f = s.prod (λ i, m • f i) :=
finset.induction_on s (smul_one m) $ λ a s has ih,
by rw [finset.prod_insert has, finset.prod_insert has, smul_mul', ih]

theorem smul_sub' {M : Type u} [monoid M] {R : Type v} [ring R] [mul_semiring_action M R]
  (m : M) (r s : R) : m • (r - s) = m • r - m • s :=
(mul_semiring_action.to_semiring_hom M R m).map_sub r s

theorem mul_semiring_action.polynomial.smul (x : R) (g : G) :
  g • mul_semiring_action.polynomial G R x = mul_semiring_action.polynomial G R x :=
(finset.smul_prod _ _ _).trans $ finset.prod_bij (λ g' _, g * g') (λ _ _, finset.mem_univ _)
  (λ g' _, by rw [smul_sub', polynomial.smul_X, polynomial.smul_C, smul_smul])
  (λ _ _ _ _, mul_left_cancel)
  (λ g' _, ⟨g ⁻¹ * g', finset.mem_univ _, (mul_inv_cancel_left g g').symm⟩)

theorem mul_semiring_action.polynomial.coeff (x : R) (g : G) (n : ℕ) :
  g • (mul_semiring_action.polynomial G R x).coeff n =
  (mul_semiring_action.polynomial G R x).coeff n :=
by rw [← polynomial.coeff_smul', mul_semiring_action.polynomial.smul]
