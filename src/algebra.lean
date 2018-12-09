import algebra.module data.polynomial

universes u v w

class algebra (R : out_param $ Type u) (A : Type v) [out_param $ comm_ring R] [ring A] :=
(f : R → A) [hom : is_ring_hom f]
(commutes : ∀ r s, s * f r = f r * s)

attribute [instance] algebra.hom

namespace algebra

variables (R : Type u) (A : Type v)
variables [comm_ring R] [ring A] [algebra R A]

@[simp] lemma f_add (r s : R) : f A (r + s) = f A r + f A s :=
is_ring_hom.map_add _

@[simp] lemma f_zero : f A (0 : R) = 0 :=
is_ring_hom.map_zero _

@[simp] lemma f_neg (r : R) : f A (-r) = -f A r :=
is_ring_hom.map_neg _

@[simp] lemma f_sub (r s : R) : f A (r - s) = f A r - f A s :=
is_ring_hom.map_sub _

@[simp] lemma f_mul (r s : R) : f A (r * s) = f A r * f A s :=
is_ring_hom.map_mul _

@[simp] lemma f_one : f A (1 : R) = 1 :=
is_ring_hom.map_one _

instance to_module : module R A := module.of_core
{ smul := λ r x, f A r * x,
  smul_add := by intros; simp [mul_add],
  add_smul := by intros; simp [add_mul],
  mul_smul := by intros; simp [mul_assoc],
  one_smul := by intros; simp }

instance to_vector_space {F : Type u} {K : Type v}
  [discrete_field F] [field K] [algebra F K] : vector_space F K :=
{ .. algebra.to_module F K }

theorem smul_def {r : R} {x : A} : r • x = f A r * x :=
rfl

@[simp] lemma mul_smul (s : R) (x y : A) :
  (x * (has_scalar.smul.{u v} s y) : A) = has_scalar.smul.{u v} s (x * y) :=
by rw [smul_def, smul_def, ← mul_assoc, commutes, mul_assoc]

@[simp] lemma smul_mul (r : R) (x y : A) :
  (r • x) * y = has_scalar.smul.{u v} r (x * y) :=
mul_assoc _ _ _

end algebra

structure alg_hom {R : Type u} (A : Type v) (B : Type w)
  [comm_ring R] [ring A] [ring B] [algebra R A] [algebra R B] :=
(to_fun : A → B) [hom : is_ring_hom to_fun]
(commutes : ∀ r : R, to_fun (has_scalar.smul.{u v} r 1) = has_scalar.smul.{u w} r 1)

infixr ` →ₐ `:25 := alg_hom

namespace alg_hom

variables (R : Type u) {A : Type v} {B : Type w}
variables [comm_ring R] [ring A] [ring B] [algebra R A] [algebra R B]
variables (φ : A →ₐ B)
include R

instance : has_coe_to_fun (A →ₐ B) := ⟨_, to_fun⟩

instance : is_ring_hom ⇑φ := hom φ

def to_linear_map : linear_map A B :=
{ to_fun := φ,
  add := λ _ _, is_ring_hom.map_add φ,
  smul := λ c x, by rw [algebra.smul_def, is_ring_hom.map_mul φ, ← mul_one (algebra.f A c),
    ← algebra.smul_def, show φ (has_scalar.smul.{u v} c 1) = _, from commutes φ c,
    algebra.smul_mul, one_mul] }

end alg_hom

namespace polynomial

variables (R : Type u) (A : Type v)
variables [comm_ring R] [comm_ring A] [algebra R A]
variables [decidable_eq R] (x : A)

instance : algebra R (polynomial R) :=
{ f := C,
  commutes := λ _ _, mul_comm _ _ }

def aeval : (polynomial R) →ₐ A :=
{ to_fun := eval₂ (algebra.f A) x,
  hom := ⟨eval₂_one _ x, λ _ _, eval₂_mul _ x, λ _ _, eval₂_add _ x⟩,
  commutes := λ r, show eval₂ (algebra.f A) x (C r * 1) = _,
    by rw [eval₂_mul, eval₂_C, eval₂_one]; refl }

theorem aeval_def (p : polynomial R) : aeval R A x p = eval₂ (algebra.f A) x p :=
rfl

instance aeval.is_ring_hom : is_ring_hom (aeval R A x) :=
alg_hom.hom _

theorem eval_unique (φ : polynomial R →ₐ A) (p) :
  φ p = eval₂ (algebra.f A) (φ X) p :=
begin
  apply polynomial.induction_on p,
  { intro r,
    rw [← mul_one (C r), eval₂_mul, eval₂_C, eval₂_one],
    exact alg_hom.commutes φ r },
  { intros f g ih1 ih2,
    simp [is_ring_hom.map_add φ, ih1, ih2] },
  { intros n r ih,
    rw [pow_succ, mul_left_comm, is_ring_hom.map_mul φ, ih],
    simp }
end

end polynomial

variables (R : Type*) [ring R]

def ring.to_ℤ_algebra : algebra ℤ R :=
{ f := coe,
  hom := by constructor; intros; simp,
  commutes := λ n r, int.induction_on n (by simp)
    (λ i ih, by simp [mul_add, add_mul, ih])
    (λ i ih, by simp [mul_add, add_mul, ih]), }

def is_ring_hom.to_ℤ_alg_hom
  (R : Type u) [ring R] [algebra ℤ R]
  (S : Type v) [ring S] [algebra ℤ S]
  (f : R → S) [is_ring_hom f] : R →ₐ S :=
{ to_fun := f, hom := by apply_instance,
  commutes := begin
    letI : module ℤ R := algebra.to_module ℤ R,
    letI : module ℤ S := algebra.to_module ℤ S,
    refine λ i, int.induction_on i (by rw [zero_smul, zero_smul, is_ring_hom.map_zero f])
      (λ i ih, by rw [add_smul i 1 (1:R), add_smul, one_smul, one_smul];
        rw [is_ring_hom.map_add f, is_ring_hom.map_one f, ih])
      (λ i ih, by rw [sub_smul, sub_smul, one_smul, one_smul];
        rw [is_ring_hom.map_sub f, is_ring_hom.map_one f, ih])
  end }

local attribute [instance] ring.to_ℤ_algebra

instance : ring (polynomial ℤ) :=
comm_ring.to_ring _

instance int.cast_hom : is_ring_hom (coe : ℤ → R) :=
⟨int.cast_one, int.cast_mul, int.cast_add⟩
