/-import .cmodule data.polynomial
import category_theory.examples.rings
import category_theory.comma
import category_theory.punit
import category_theory.yoneda

universes u v

set_option pp.universes true
namespace category_theory.examples
open category_theory

variables (R : CommRing.{u})

def Algebra : Type (u+1) := comma.{u} (functor.of_obj R) (functor.id _)

instance : category (Algebra R) :=
category_theory.comma_category

namespace Algebra

instance : has_coe (Algebra.{u} R) (CommRing.{u}) := ⟨λ A, A.right⟩

@[simp] def to_comm_ring : Algebra.{u} R ⥤ CommRing.{u} :=
comma.snd _ _

variables {R} {A B : Algebra.{u} R}

theorem hom_eq (φ : A ⟶ B) (x : R) : φ.right (A.hom x) = B.hom x :=
(congr_fun (congr_arg subtype.val φ.w) x).symm

variables (A B)

@[simp] def to_module_obj : left_module R :=
{ carrier := A,
  grp := infer_instance,
  mod := module.of_core
  { smul := λ c x, A.hom c * x,
    smul_add := λ _, mul_add _,
    add_smul := λ _ _ _, show _ * _ = _,
      by rw [is_ring_hom.map_add A.hom, add_mul],
    mul_smul := λ _ _ _, show _ * _ = _,
      by rw [is_ring_hom.map_mul A.hom, mul_assoc],
    one_smul := λ _, show A.hom 1 * _ = _,
      by rw [is_ring_hom.map_one A.hom, one_mul] } }

variable (R)
@[simp] def to_module : Algebra.{u} R ⥤ left_module R :=
{ obj := to_module_obj,
  map := λ A B φ,
  { to_fun := (to_comm_ring R).map φ,
    add := λ _ _, is_ring_hom.map_add _,
    smul := λ c x, show φ.right (_ * _) = _,
      by rw [is_ring_hom.map_mul φ.right, hom_eq]; refl } }

open polynomial
variables [decidable_eq R]
@[simp] def apoly : Algebra.{u} R :=
{ left := punit.star,
  right := { α := polynomial R },
  hom := ⟨C, by apply_instance⟩ }

variables {R}
@[simp] def aeval (A : Algebra.{u} R) (x : A) : apoly R ⟶ A :=
{ right := ⟨eval₂ A.hom x, eval₂.is_ring_hom _⟩,
  w' := subtype.eq $ funext $ λ c, eq.symm $ eval₂_C _ _ }

def polynomial_hom_equiv : coyoneda.obj (apoly R) ≅ to_comm_ring R ⋙ forget _ :=
{ hom := { app := λ A φ, (to_comm_ring R).map φ X },
  inv := { app := λ A x, aeval A x,
    naturality' := λ A B φ, funext $ λ r, comma_morphism.ext rfl $ subtype.eq $ funext $ λ p,
      show eval₂ B.hom (φ.right r) p = φ.right (eval₂ A.hom r p),
      from polynomial.induction_on p
        (λ c, by rw [eval₂_C, eval₂_C, hom_eq])
        (λ p q ihp ihq, by rw [eval₂_add, eval₂_add, ihp, ihq, is_ring_hom.map_add φ.right])
        (λ n c ih, by rw [eval₂_mul, eval₂_C, eval₂_mul, eval₂_C, is_ring_hom.map_mul φ.right, hom_eq,
          eval₂_pow, eval₂_X, eval₂_pow, eval₂_X, is_semiring_hom.map_pow φ.right]) },
  hom_inv_id' := nat_trans.ext _ _ $ λ A, funext $ λ φ, comma_morphism.ext (by obviously) $ subtype.eq $ funext $ λ p,
    show eval₂ A.hom (φ.right X) p = φ.right p,
    from polynomial.induction_on p
      (λ c, by rw [eval₂_C, ← hom_eq φ]; refl)
      (λ p q ihp ihq, by rw [eval₂_add, ihp, ihq, is_ring_hom.map_add φ.right])
      (λ n c ih, by rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, ← hom_eq φ,
        is_ring_hom.map_mul φ.right, is_semiring_hom.map_pow φ.right]; refl),
  inv_hom_id' := nat_trans.ext _ _ $ λ A, funext $ λ r,
    show eval₂ A.hom _ _ = r, from eval₂_X _ _ }

end Algebra

namespace Ring

open polynomial

-- this is stupid
local attribute [instance, priority 0] classical.dec
noncomputable def polynomial : CommRing.{u} ⥤ CommRing.{u} :=
{ obj := λ R, { α := polynomial R },
  map := λ R S φ, ⟨map φ, by apply_instance⟩,
  map_id' := λ R, subtype.eq $ funext $ λ p,
    show map id p = p, from polynomial.induction_on p (λ c, map_C _)
      (λ p q ihp ihq, by rw [map_add, ihp, ihq])
      (λ n c ih, by rw [pow_succ', ← mul_assoc, map_mul, ih, map_X]),
  map_comp' := λ R S T f g, subtype.eq $ funext $ λ p,
    show map (g ∘ f) p = map g (map f p), from polynomial.induction_on p
      (λ c, by rw [map_C, map_C, map_C])
      (λ p q ihp ihq, by rw [map_add, map_add, map_add, ihp, ihq])
      (λ n c ih, by rw [map_mul, map_pow, map_mul, map_pow, map_mul, map_pow,
        map_C, map_C, map_C, map_X, map_X, map_X]) }

end Ring

end category_theory.examples-/