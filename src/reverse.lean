/- Reverse Galois theory. -/

import field_theory.subfield
import normal

universes u v w

variables {α : Type u} [field α] (G : finset (ring_aut α)) (f : ring_aut α)

def fixed : set α :=
{ x | ∀ g ∈ G, (g : ring_aut α) x = x }

def fixed_one : set α :=
{ x | f x = x }

instance fixed_one.is_subfield : is_subfield (fixed_one f) :=
{ zero_mem := f.map_zero,
  add_mem := λ x y hx hy, (f.map_add x y).trans $ congr_arg2 _ hx hy,
  neg_mem := λ x hx, (f.map_neg x).trans $ congr_arg _ hx,
  one_mem := f.map_one,
  mul_mem := λ x y hx hy, (f.map_mul x y).trans $ congr_arg2 _ hx hy,
  inv_mem := λ x hx, f.to_ring_hom.map_inv.trans $ congr_arg _ hx }

theorem fixed_eq_Inter_fixed_one : fixed G = ⋂ (g : ↥(↑G : set (ring_aut α))), fixed_one g.val :=
set.ext $ λ x, ⟨λ hx, set.mem_Inter.2 $ λ g, hx g.1 g.2, λ hx g hg, by convert set.mem_Inter.1 hx ⟨g, hg⟩⟩

instance fixed.is_subfield : is_subfield (fixed G) :=
by convert @is_subfield.Inter α _ (↑G : set (ring_aut α)) (λ g, fixed_one g.1) _; rw fixed_eq_Inter_fixed_one

@[priority 1000000000]
instance fixed.algebra : algebra (fixed G) α :=
algebra.of_subring _


#exit

-- oh no i need symmetric polynomials
theorem is_integral_fixed (h1 : (1 : ring_aut α) ∈ G) (x : α) : is_integral (fixed G) x :=
⟨G.prod $ λ f, polynomial.X - _, _⟩

instance fixed.normal (HG : set.finite G) : normal (fixed G) α :=
λ x, ⟨⟨_, _⟩, _⟩
