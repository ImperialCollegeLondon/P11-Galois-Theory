import data.fintype

definition is_finite_Galois_extension_of : Type* → Type* → Type* := sorry

definition galois_group : Type* → Type* → Type* := sorry

instance {L K : Type*} (Hfin : is_finite_Galois_extension_of L K) :
fintype (galois_group L K) := sorry

-- needs fixing
theorem fundamental_theorem_of_Galois_theory
(K : Type*) [field K]
(L : Type*) (HL : is_finite_Galois_extension_of K L) :
fintype.card (galois_group L K) = dimension K L := sorry

