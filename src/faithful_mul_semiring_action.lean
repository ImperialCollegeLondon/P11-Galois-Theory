import algebra.group_ring_action

universes u v

variables (M : Type u) [monoid M] (R : Type v) [semiring R]

class faithful_mul_semiring_action extends mul_semiring_action M R :=
(eq_of_smul_eq_smul' : ∀ {m₁ m₂ : M}, (∀ r : R, m₁ • r = m₂ • r) → m₁ = m₂)

variables {M} [faithful_mul_semiring_action M R]

theorem eq_of_smul_eq_smul {m₁ m₂ : M} : (∀ r : R, m₁ • r = m₂ • r) → m₁ = m₂ :=
faithful_mul_semiring_action.eq_of_smul_eq_smul'

theorem injective_to_semiring_hom (M : Type u) [monoid M] (R : Type v) [semiring R]
  [faithful_mul_semiring_action M R] :
  function.injective (mul_semiring_action.to_semiring_hom M R) :=
λ m₁ m₂ h, eq_of_smul_eq_smul R $ λ r, ring_hom.ext_iff.1 h r
