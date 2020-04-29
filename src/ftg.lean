import ring_theory.algebra data.fintype.basic linear_algebra.dimension

universes u v w

variables (K : Type u) (L : Type v) [field K] [field L]

class finite_Galois_extension extends algebra K L.

definition galois_group : Type u → Type v → Type w := sorry

instance [finite_Galois_extension K L] :
fintype (galois_group L K) := sorry

-- needs fixing
theorem fundamental_theorem_of_Galois_theory (HL : finite_Galois_extension K L) :
(fintype.card (galois_group L K) : cardinal) = vector_space.dim K L := sorry
