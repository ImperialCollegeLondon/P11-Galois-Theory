import field_theory.minimal_polynomial
import ring_theory.algebra
import field_theory.subfield
import ring_theory.adjoin_root
import linear_algebra.basic

universes u v w

noncomputable theory
open_locale classical

def galois_conjugates (α : Type u) {β : Type v} {γ : Type w} 
[field α] [field β] [field γ] [algebra α β] [algebra α γ] 
{b : β} {c : γ} (Hb : is_integral α b) (Hc : is_integral α c) : Prop := 
minimal_polynomial Hb = minimal_polynomial Hc

open algebra
open field
open adjoin_root

/-
Goal 1 : Let L, N be K-extensions and a ∈ L algebraic over K.
Then the K-extension morphisms from K(a) to N biject with
the set of galois K-conjugates of a in N. 

Formalize as two functions, 
(1) taking K-ext morphisms from K(a) into N to a galois conjugate
(2) taking a galois conjugate in N, returning a K-ext morphism
from K(a) to N
-/

open ideal.quotient
open quotient

instance wdihtpt1 {α : Type u} [comm_ring α] (I : ideal α) : 
algebra α (I.quotient) := 
ring_hom.to_algebra $ mk_hom I

instance wdihtpt2 {α : Type u} {β : Type v} 
[comm_ring α] [comm_ring β] [algebra α β]
(f : polynomial α) : algebra α (adjoin_root f) := 
comap.algebra α (polynomial α) (adjoin_root f)

def wdihtpt3 {α : Type u} {β : Type v} {γ : Type w} 
[comm_semiring α] [semiring β] [semiring γ] 
[algebra α β] [algebra α γ] (φ : β →+* γ) 
(h : ∀ a : α, φ (algebra_map α β a) = algebra_map α γ a) : 
β →ₐ[α] γ := ⟨φ.to_fun, ring_hom.map_one _,ring_hom.map_mul _,
ring_hom.map_zero _,ring_hom.map_add _,h⟩

-- Essentially function (2)
-- Actually already exists in ring_theory.adjoin_root
-- but only as a ring map. 
def algebra_lift
{α : Type u} {β : Type v} [comm_ring α] [comm_ring β] [algebra α β]
(f : polynomial α) {x : β} (h : f.eval₂ (algebra_map α β) x = 0) : 
(adjoin_root f) →ₐ[α] β := wdihtpt3 (adjoin_root.lift (algebra_map α β) x h)
$ λ a : α, lift_of

#check @algebra_lift

open minimal_polynomial

def field.adjoin {K : Type u} {L : Type v} 
[field K] [field L] [algebra K L] {x : L} (Hx : is_integral K x) : 
subalgebra K L := 
alg_hom.range $ algebra_lift (minimal_polynomial Hx) $ aeval Hx

open function
lemma adjoin_root_to_field_adjoin_inj {K : Type u} {L : Type v} 
[field K] [field L] [algebra K L] {x : L} (Hx : is_integral K x) : 
injective (algebra_lift (minimal_polynomial Hx) (aeval Hx)) := 
@ring_hom.injective (adjoin_root (minimal_polynomial Hx)) L 
(@field.to_division_ring _ (
  @adjoin_root.field _ _ (minimal_polynomial Hx) 
  (minimal_polynomial.irreducible Hx))
) _ ↑(algebra_lift (minimal_polynomial Hx) (aeval Hx))

lemma adjoin_root_to_field_adjoin_surj {K : Type u} {L : Type v} 
[field K] [field L] [algebra K L] {x : L} (Hx : is_integral K x) : 
surjective (algebra_lift (minimal_polynomial Hx) (aeval Hx)) := sorry

def adjoin_equiv_adjoin {K : Type u} {L : Type v} 
[field K] [field L] [algebra K L] {x : L} (Hx : is_integral K x) : 
adjoin_root (minimal_polynomial Hx) ≃ₐ[K] field.adjoin Hx := 
sorry

-- instance field.adjoin.is_subfield {K : Type u} {L : Type v} 
-- [field K] [field L] [algebra K L] {x : L} (Hx : is_integral K x) : 
-- is_subfield (field.adjoin Hx).carrier := sorry

theorem adjoin_eq_closure {K : Type u} {L : Type v} 
[field K] [field L] [algebra K L] {x : L} (Hx : is_integral K x) : 
(field.adjoin Hx).carrier = closure ((set.range $ algebra_map K L) ∪ {x}) := 
sorry -- do we actually care about this? 