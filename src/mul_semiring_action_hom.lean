import algebra.group_ring_action

universes u v w

variables (M : Type u) [monoid M]
variables (R : Type v) [semiring R] [mul_semiring_action M R]
variables (R' : Type w) [semiring R'] [mul_semiring_action M R']
variables (B : Type v) [comm_semiring B] [mul_semiring_action M B]
variables (B' : Type w) [comm_semiring B'] [mul_semiring_action M B']

set_option old_structure_cmd true

/-- Equivariant ring homomorphisms. -/
@[nolint has_inhabited_instance]
structure mul_semiring_action_hom extends R →+* R' :=
(map_smul' : ∀ (m : M) (r : R), to_fun (m • r) = m • to_fun r)

/-- Reinterpret an equivariant ring homomorphism as a ring homomorphism. -/
add_decl_doc mul_semiring_action_hom.to_ring_hom

notation β ` →+*[`:25 α:25 `] `:0 γ:0 := mul_semiring_action_hom α β γ

namespace mul_semiring_action_hom

instance : has_coe_to_fun (R →+*[M] R') :=
⟨_, λ c, c.to_fun⟩

instance : has_coe (R →+*[M] R') (R →+* R') :=
⟨λ c, c.to_ring_hom⟩

variables {M R R'} (f : R →+*[M] R')

@[simp] theorem coe_coe : ((f : R →+* R') : R → R') = f :=
rfl

theorem map_smul (m : M) (r : R) : f (m • r) = m • f r :=
f.map_smul' m r

variables {M B B'} (g : B →+*[M] B')

open polynomial

/-- An equivariant map induces an equivariant map on polynomials. -/
protected noncomputable def polynomial : polynomial B →+*[M] polynomial B' :=
⟨map g, map_one g, λ p q, map_mul g, map_zero g, λ p q, map_add g,
λ m p, polynomial.induction_on p
  (λ b, by rw [smul_C, map_C, coe_coe, g.map_smul, map_C, coe_coe, smul_C])
  (λ p q ihp ihq, by rw [smul_add, map_add, ihp, ihq, map_add, smul_add])
  (λ n b ih, by rw [smul_mul', smul_C, smul_pow, smul_X, map_mul, map_C, map_pow, map_X,
      coe_coe, g.map_smul, map_mul, map_C, map_pow, map_X,
      smul_mul', smul_C, smul_pow, smul_X, coe_coe])⟩

theorem coe_polynomial : (g.polynomial : polynomial B → polynomial B') = map g :=
rfl

end mul_semiring_action_hom

variables {A : Type v} [ring A] [mul_semiring_action M A]
variables (S : set A)

set_option old_structure_cmd false

/-- A subring invariant under the action. -/
class is_invariant_subring [is_subring S] : Prop :=
(smul_mem : ∀ (m : M) {x : A}, x ∈ S → m • x ∈ S)

variables [is_subring S] [is_invariant_subring M S]

instance is_invariant_subring.to_mul_semiring_action : mul_semiring_action M S :=
{ smul := λ m x, ⟨m • x, is_invariant_subring.smul_mem m x.2⟩,
  one_smul := λ s, subtype.eq $ one_smul M s,
  mul_smul := λ m₁ m₂ s, subtype.eq $ mul_smul m₁ m₂ s,
  smul_add := λ m s₁ s₂, subtype.eq $ smul_add m s₁ s₂,
  smul_zero := λ m, subtype.eq $ smul_zero m,
  smul_one := λ m, subtype.eq $ smul_one m,
  smul_mul := λ m s₁ s₂, subtype.eq $ smul_mul' m s₁ s₂ }

/-- The canonical inclusion from an invariant subring. -/
def is_invariant_subring.subtype : S →+*[M] A :=
{ map_smul' := λ m s, rfl, .. is_subring.subtype S }

theorem is_invariant_subring.coe_subtype :
  (is_invariant_subring.subtype M S : S → A) = coe :=
rfl

@[simp] theorem is_invariant_subring.coe_subtype' :
  (is_invariant_subring.subtype M S : S →+* A) = is_subring.subtype S :=
rfl
