import linear_algebra.basic data.polynomial ring_theory.subring

universes u v w

open lattice

structure algebra (R : out_param $ Type u) (A : Type v) [out_param $ comm_ring R] [ring A] :=
(to_fun : R → A) [hom : is_ring_hom to_fun]
(commutes' : ∀ r s, s * to_fun r = to_fun r * s)

attribute [instance] algebra.hom

namespace algebra

variables (R : Type u) (A : Type v)
variables [comm_ring R] [ring A]

instance : has_coe_to_fun (algebra R A) :=
⟨_, to_fun⟩

variables {R A} (i : algebra R A)

theorem commutes (r s) : s * i r = i r * s := i.commutes' r s

@[simp] lemma map_add (r s : R) : i (r + s) = i r + i s :=
is_ring_hom.map_add _

@[simp] lemma map_zero : i (0 : R) = 0 :=
is_ring_hom.map_zero _

@[simp] lemma map_neg (r : R) : i (-r) = -i r :=
is_ring_hom.map_neg _

@[simp] lemma map_sub (r s : R) : i (r - s) = i r - i s :=
is_ring_hom.map_sub _

@[simp] lemma map_mul (r s : R) : i (r * s) = i r * i s :=
is_ring_hom.map_mul _

@[simp] lemma map_one : i (1 : R) = 1 :=
is_ring_hom.map_one _

variables {R A}
def to_module (i : algebra R A) : Type v := A

instance to_module.comm_ring : ring (to_module i) :=
by dunfold to_module; apply_instance

instance to_module.module : module R (to_module i) := module.of_core
{ smul := λ r x, i r * x,
  smul_add := by intros; simp [mul_add],
  add_smul := by intros; simp [add_mul],
  mul_smul := by intros; simp [mul_assoc],
  one_smul := by intros; simp; exact one_mul x }

instance to_module.vector_space {F : Type u} {K : Type v}
  [discrete_field F] [field K] (i : algebra F K) :
  vector_space F (to_module i) :=
{ .. algebra.to_module.module i }

theorem smul_def {r : R} {x : to_module i} : r • x = i r * x :=
rfl

@[simp] lemma mul_smul (s : R) (x y : to_module i) :
  x * (has_scalar.smul.{u v} s y) = has_scalar.smul.{u v} s (x * y) :=
by rw [smul_def, smul_def, ← mul_assoc, commutes, mul_assoc]

@[simp] lemma smul_mul (r : R) (x y : to_module i) :
  (r • x) * y = has_scalar.smul.{u v} r (x * y) :=
mul_assoc _ _ _

def polynomial (R : Type u) [comm_ring R] [decidable_eq R] : algebra R (polynomial R) :=
{ to_fun := polynomial.C,
  commutes' := λ _ _, mul_comm _ _ }

end algebra

structure alg_hom {R : Type u} {A : Type v} {B : Type w}
  [comm_ring R] [ring A] [ring B] (iA : algebra R A) (iB : algebra R B) :=
(to_fun : A → B) [hom : is_ring_hom to_fun]
(commutes' : ∀ r : R, to_fun (iA r) = iB r)

infixr ` →ₐ `:25 := alg_hom

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_ring R] [ring A] [ring B]
variables (iA : algebra R A) (iB : algebra R B)
include R

instance : has_coe_to_fun (iA →ₐ iB) := ⟨λ _, A → B, to_fun⟩

variables {iA iB} (φ : iA →ₐ iB)

instance : is_ring_hom ⇑φ := hom φ

theorem commutes (r) : φ (iA r) = iB r := φ.commutes' r

@[simp] lemma map_add (r s : A) : φ (r + s) = φ r + φ s :=
is_ring_hom.map_add _

@[simp] lemma map_zero : φ (0 : A) = 0 :=
is_ring_hom.map_zero _

@[simp] lemma map_neg (r : A) : φ (-r) = -φ r :=
is_ring_hom.map_neg _

@[simp] lemma map_sub (r s : A) : φ (r - s) = φ r - φ s :=
is_ring_hom.map_sub _

@[simp] lemma map_mul (r s : A) : φ (r * s) = φ r * φ s :=
is_ring_hom.map_mul _

@[simp] lemma map_one : φ (1 : A) = 1 :=
is_ring_hom.map_one _

def to_linear_map : iA.to_module →ₗ iB.to_module :=
{ to_fun := φ,
  add := φ.map_add,
  smul := λ c x, by rw [algebra.smul_def, φ.map_mul, φ.commutes c, algebra.smul_def] }

end alg_hom

namespace polynomial

variables (R : Type u) {A : Type v}
variables [comm_ring R] [comm_ring A] (i : algebra R A)
variables [decidable_eq R] (x : A)

def aeval : (algebra.polynomial R) →ₐ i :=
{ to_fun := eval₂ i x,
  hom := ⟨eval₂_one _ x, λ _ _, eval₂_mul _ x, λ _ _, eval₂_add _ x⟩,
  commutes' := λ r, eval₂_C _ _ }

theorem aeval_def (p : polynomial R) : aeval R i x p = eval₂ i x p :=
rfl

instance aeval.is_ring_hom : is_ring_hom (aeval R i x) :=
alg_hom.hom _

theorem eval_unique (φ : algebra.polynomial R →ₐ i) (p) :
  φ p = eval₂ i (φ X) p :=
begin
  apply polynomial.induction_on p,
  { intro r, rw eval₂_C, exact φ.commutes r },
  { intros f g ih1 ih2,
    rw [is_ring_hom.map_add φ, ih1, ih2, eval₂_add] },
  { intros n r ih,
    rw [pow_succ', ← mul_assoc, is_ring_hom.map_mul φ, eval₂_mul, eval₂_X, ih] }
end

end polynomial

section

variables (R : Type*) [ring R]

def ring.to_ℤ_algebra : algebra ℤ R :=
{ to_fun := coe,
  hom := by constructor; intros; simp,
  commutes' := λ n r, int.induction_on n (by simp)
    (λ i ih, by simp [mul_add, add_mul, ih])
    (λ i ih, by simp [mul_add, add_mul, ih]), }

def is_ring_hom.to_ℤ_alg_hom
  (R : Type u) [ring R] (iR : algebra ℤ R)
  (S : Type v) [ring S] (iS : algebra ℤ S)
  (f : R → S) [is_ring_hom f] : iR →ₐ iS :=
{ to_fun := f, hom := by apply_instance,
  commutes' := λ i, int.induction_on i (by rw [iR.map_zero, iS.map_zero, is_ring_hom.map_zero f])
      (λ i ih, by rw [iR.map_add, iS.map_add, iR.map_one, iS.map_one];
        rw [is_ring_hom.map_add f, is_ring_hom.map_one f, ih])
      (λ i ih, by rw [iR.map_sub, iS.map_sub, iR.map_one, iS.map_one];
        rw [is_ring_hom.map_sub f, is_ring_hom.map_one f, ih]) }

instance : ring (polynomial ℤ) :=
comm_ring.to_ring _

instance int.cast_hom : is_ring_hom (coe : ℤ → R) :=
⟨int.cast_one, int.cast_mul, int.cast_add⟩

end

structure subalgebra {R : Type u} {A : Type v}
  [comm_ring R] [ring A] (i : algebra R A) : Type v :=
(carrier : set A) [subring : is_subring carrier]
(range_le : set.range i ≤ carrier)

attribute [instance] subalgebra.subring

namespace subalgebra

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] (i : algebra R A)

instance : has_coe (subalgebra i) (set A) :=
⟨λ S, S.carrier⟩

instance : has_coe_to_sort (subalgebra i) :=
by apply_instance

instance : has_mem A (subalgebra i) :=
⟨λ x S, x ∈ S.carrier⟩

variables {i}

theorem mem_coe {x : A} {s : subalgebra i} : x ∈ (s : set A) ↔ x ∈ s :=
iff.rfl

@[extensionality] theorem ext {S T : subalgebra i}
  (h : ∀ x : A, x ∈ S ↔ x ∈ T) : S = T :=
by cases S; cases T; congr; ext x; exact h x

variables (S : subalgebra i)

instance : is_subring (S : set A) := S.subring

instance : ring S := @@subtype.ring _ S.is_subring

def algebra : algebra R S :=
{ to_fun := λ r, ⟨i r, S.range_le ⟨r, rfl⟩⟩,
  hom := ⟨subtype.eq i.map_one, λ x y, subtype.eq $ i.map_mul x y,
    λ x y, subtype.eq $ i.map_add x y⟩,
  commutes' := λ r s, subtype.eq $ i.commutes r s }

def val : S.algebra →ₐ i :=
{ to_fun := subtype.val,
  hom := ⟨rfl, λ _ _, rfl, λ _ _, rfl⟩,
  commutes' := λ r, rfl }

def to_submodule : submodule R i.to_module :=
{ carrier := S.carrier,
  zero := (0:S).2,
  add := λ x y hx hy, (⟨x, hx⟩ + ⟨y, hy⟩ : S).2,
  smul := λ c x hx, (⟨i c, S.range_le ⟨c, rfl⟩⟩ * ⟨x, hx⟩:S).2 }

instance : partial_order (subalgebra i) :=
{ le := λ S T, S.carrier ≤ T.carrier,
  le_refl := λ _, le_refl _,
  le_trans := λ _ _ _, le_trans,
  le_antisymm := λ S T hst hts, ext $ λ x, ⟨@hst x, @hts x⟩ }

end subalgebra

namespace alg_hom

variables {R : Type u} {A : Type v} {B : Type w}
variables [comm_ring R] [ring A] [ring B]
variables {iA : algebra R A} {iB : algebra R B}
variables (φ : iA →ₐ iB)

protected def range : subalgebra iB :=
{ carrier := set.range φ,
  subring :=
  { one_mem := ⟨1, φ.map_one⟩,
    mul_mem := λ y₁ y₂ ⟨x₁, hx₁⟩ ⟨x₂, hx₂⟩, ⟨x₁ * x₂, hx₁ ▸ hx₂ ▸ φ.map_mul x₁ x₂⟩ },
  range_le := λ y ⟨r, hr⟩, ⟨iA r, hr ▸ φ.commutes r⟩ }

end alg_hom

namespace algebra

variables {R : Type u} {A : Type v}
variables [comm_ring R] [ring A] (i : algebra R A)

variables (R)
protected def id : algebra R R :=
{ to_fun := id, commutes' := λ _ _, mul_comm _ _ }
variables {R}

def of_id : algebra.id R →ₐ i :=
{ to_fun := i, commutes' := λ _, rfl }

def adjoin (s : set A) : subalgebra i :=
{ carrier := ring.closure (set.range i ∪ s),
  range_le := le_trans (set.subset_union_left _ _) ring.subset_closure }

protected def gc : galois_connection i.adjoin coe :=
λ s S, ⟨λ H, le_trans (le_trans (set.subset_union_right _ _) ring.subset_closure) H,
λ H, ring.closure_subset $ set.union_subset S.range_le H⟩

protected def gi : galois_insertion i.adjoin coe :=
{ choice := λ s hs, i.adjoin s,
  gc := i.gc,
  le_l_u := λ S, (i.gc S (i.adjoin S)).1 (le_refl _),
  choice_eq := λ _ _, rfl }

instance : complete_lattice (subalgebra i) :=
galois_insertion.lift_complete_lattice i.gi

theorem mem_bot {x : A} : x ∈ (⊥ : subalgebra i) ↔ x ∈ set.range i :=
suffices (⊥ : subalgebra i) = i.of_id.range, by rw this; refl,
le_antisymm bot_le $ subalgebra.range_le _

theorem mem_top {x : A} : x ∈ (⊤ : subalgebra i) :=
ring.mem_closure $ or.inr trivial

def to_top : i →ₐ (⊤ : subalgebra i).algebra :=
{ to_fun := λ x, ⟨x, i.mem_top⟩,
  hom := ⟨rfl, λ _ _, rfl, λ _ _, rfl⟩,
  commutes' := λ _, rfl }

end algebra