import data.polynomial
import .group_ring_action

noncomputable theory
local attribute [instance] classical.dec
universes u v

variables {M : Type u} [monoid M] {R : Type v} [comm_semiring R] [mul_semiring_action M R]

instance : mul_semiring_action M (polynomial R) :=
{ smul := λ m, polynomial.map $ mul_semiring_action.to_semiring_hom M R m,
  one_smul := λ p, by ext n; erw polynomial.coeff_map; exact one_smul M (p.coeff n),
  mul_smul := λ m n p, by ext i;
    iterate 3 { rw polynomial.coeff_map (mul_semiring_action.to_semiring_hom M R _) };
    exact mul_smul m n (p.coeff i),
  smul_add := λ m p q, polynomial.map_add (mul_semiring_action.to_semiring_hom M R m),
  smul_zero := λ m, polynomial.map_zero (mul_semiring_action.to_semiring_hom M R m),
  smul_one := λ m, polynomial.map_one (mul_semiring_action.to_semiring_hom M R m),
  smul_mul := λ m p q, polynomial.map_mul (mul_semiring_action.to_semiring_hom M R m), }

@[simp] lemma polynomial.coeff_smul' (m : M) (p : polynomial R) (n : ℕ) :
  (m • p).coeff n = m • p.coeff n :=
polynomial.coeff_map _ _

@[simp] lemma polynomial.smul_C (m : M) (r : R) : m • polynomial.C r = polynomial.C (m • r) :=
polynomial.map_C _

@[simp] lemma polynomial.smul_X (m : M) : (m • polynomial.X : polynomial R) = polynomial.X :=
polynomial.map_X _
