/- Reverse Galois theory. -/

import field_theory.subfield ring_theory.polynomial
import .symmetric_polynomial .normal .splitting_theorem

noncomputable theory
local attribute [instance] classical.dec

universes u v w

variables (G : Type u) [group G] (F : Type v) [field F] [mul_semiring_action G F] (g : G)

def fixed : set F :=
{ x | ∀ g : G, g • x = x }

def fixed_one : set F :=
{ x | g • x = x }

instance fixed_one.is_subfield : is_subfield (fixed_one G F g) :=
{ zero_mem := smul_zero g,
  add_mem := λ x y hx hy, (smul_add g x y).trans $ congr_arg2 _ hx hy,
  neg_mem := λ x hx, (smul_neg' g x).trans $ congr_arg _ hx,
  one_mem := smul_one g,
  mul_mem := λ x y hx hy, (smul_mul' g x y).trans $ congr_arg2 _ hx hy,
  inv_mem := λ x hx, (smul_inv F g x).trans $ congr_arg _ hx }

theorem fixed_eq_Inter_fixed_one : fixed G F = ⋂ g : G, fixed_one G F g :=
set.ext $ λ x, ⟨λ hx, set.mem_Inter.2 $ λ g, hx g, λ hx g, by convert set.mem_Inter.1 hx g⟩

instance fixed.is_subfield : is_subfield (fixed G F) :=
by convert @is_subfield.Inter F _ G (fixed_one G F) _; rw fixed_eq_Inter_fixed_one

@[priority 1000000000]
instance fixed.algebra : algebra (fixed G F) F :=
algebra.of_subring _

variables [fintype G] (x : F)

def fixed.polynomial : polynomial (fixed G F) :=
(mul_semiring_action.minpoly G F x).to_subring _ $ λ c hc g,
let ⟨hc0, n, hn⟩ := finsupp.mem_frange.1 hc in
hn ▸ mul_semiring_action.minpoly.coeff G F x g n

theorem fixed.polynomial.monic : (fixed.polynomial G F x).monic :=
subtype.eq $ mul_semiring_action.minpoly.monic G F x

theorem fixed.polynomial.eval₂ : (fixed.polynomial G F x).eval₂ subtype.val x = 0 :=
mul_semiring_action.minpoly.eval G F x

theorem is_integral_fixed : is_integral (fixed G F) x :=
⟨fixed.polynomial G F x, fixed.polynomial.monic G F x, fixed.polynomial.eval₂ G F x⟩

-- why is the statement so slow to elaborate?
theorem fixed.polynomial.irreducible : irreducible (fixed.polynomial G F x : polynomial (fixed G F)) :=
sorry

theorem fixed.polynomial.minimal_polynomial :
  (minimal_polynomial (is_integral_fixed G F x) : polynomial (fixed G F)) = fixed.polynomial G F x :=
_

#exit

instance fixed.normal : normal (fixed G F) F :=
λ x, ⟨is_integral_fixed G F x, _⟩
