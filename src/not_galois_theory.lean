import algebra.field
import field_theory.subfield
import ring_theory.principal_ideal_domain
import data.polynomial

local attribute [instance, priority 0] classical.prop_decidable

open function

variables {K L ι : Type} [discrete_field K] [discrete_field L] (f : K → L) (homf : is_field_hom f)

def subfields : set (set L) := {K' : set L | is_subfield K'}

def prime_subfield := set.sInter (@subfields L _)

theorem field_intersect_two (F1 F2 : set K) [h1 : is_subfield F1] [h2 : is_subfield F2] : is_subfield (F1 ∩ F2) := 
{   zero_mem := and.intro h1.zero_mem h2.zero_mem,
    one_mem := and.intro h1.one_mem h2.one_mem,
    add_mem := λ a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩, and.intro (is_add_submonoid.add_mem ha1 hb1) (is_add_submonoid.add_mem ha2 hb2),
    mul_mem := λ a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩, and.intro (is_submonoid.mul_mem ha1 hb1) (is_submonoid.mul_mem ha2 hb2),
    neg_mem := λ a ⟨ha1, ha2⟩, and.intro (is_add_subgroup.neg_mem ha1) (is_add_subgroup.neg_mem ha2),
    inv_mem := λ x ⟨hx1, hx2⟩, and.intro (is_subfield.inv_mem hx1) (is_subfield.inv_mem hx2) }

theorem field_intersect (Fi : ι → set K) [hi : ∀ i, is_subfield (Fi i)] : is_subfield (set.Inter Fi) := 
{   zero_mem := by { simp, exact λ i, (hi i).zero_mem },
    one_mem := by { simp, exact λ i, (hi i).one_mem },
    add_mem := by { simp, exact λ a b ha hb i, is_add_submonoid.add_mem (ha i) (hb i) },
    mul_mem := by { simp, exact λ a b ha hb i, is_submonoid.mul_mem (ha i) (hb i) },
    neg_mem := by { simp, exact λ a h i, is_add_subgroup.neg_mem (h i) },
    inv_mem := by { simp, exact λ a h i, is_subfield.inv_mem (h i) } }

theorem field_intersect' (PL : set (set L)) [H : ∀ J ∈ PL, is_subfield J] : is_subfield (set.sInter PL) :=
{   zero_mem := λ J HJ, (H J HJ).zero_mem,
    one_mem := λ J HJ, (H J HJ).one_mem,
    add_mem := λ a b ha hb J HJ, let X := (H J HJ).add_mem in X (ha J HJ) (hb J HJ),
    mul_mem := λ a b ha hb J HJ, let X := (H J HJ).mul_mem in X (ha J HJ) (hb J HJ),
    neg_mem := λ a h J HJ, let X := (H J HJ).neg_mem in X (h J HJ),
    inv_mem := λ a h J HJ, let X := (H J HJ).inv_mem in X (h J HJ) }

instance subfields_are_subfields : ∀ J ∈ @subfields L _, is_subfield J := by simp [subfields]

instance prime_subfield_is_subfield : is_subfield (@prime_subfield L _) := 
@field_intersect' _ _ subfields subfields_are_subfields

theorem rat_cast_hom [char_zero L] : is_field_hom (@rat.cast L _) :=
⟨rat.cast_one, rat.cast_mul, rat.cast_add⟩

def rat_cast_img : set L := set.range rat.cast

lemma rat_cast_img_def : rat_cast_img = { l : L | ∃ q : ℚ, ↑q = l } := rfl

lemma rat_cast_eq_coe {q : ℚ} : @rat.cast L _ q = ↑q := rfl

lemma int_cast_eq_coe {n : ℤ} : @int.cast L _ _ _ _ n = ↑n := rfl

noncomputable def rat_cast_equiv [char_zero L] : equiv ℚ (↥(@rat_cast_img L _ )) 
:= equiv.set.range rat.cast rat.cast_injective

instance rat_cast_img_subfield [char_zero L] : is_subfield (@rat_cast_img L _) :=
{   zero_mem := Exists.intro 0 rat.cast_zero,
    one_mem := Exists.intro 1 rat.cast_one,
    add_mem := λ a b ⟨aq, ha⟩ ⟨bq, hb⟩, Exists.intro (aq + bq) 
      (by rw [rat_cast_eq_coe, rat.cast_add, ←rat_cast_eq_coe, ←rat_cast_eq_coe, ha, hb]),
    mul_mem := λ a b ⟨aq, ha⟩ ⟨bq, hb⟩, Exists.intro (aq * bq) 
      (by rw [rat_cast_eq_coe, rat.cast_mul, ←rat_cast_eq_coe, ←rat_cast_eq_coe, ha, hb]),
    neg_mem := λ a ⟨aq, ha⟩, Exists.intro (- aq) 
      (by rw [rat_cast_eq_coe, rat.cast_neg, ←rat_cast_eq_coe, ha]),
    inv_mem := λ a ⟨aq, ha⟩, Exists.intro (aq⁻¹) 
      (by rw [rat_cast_eq_coe, rat.cast_inv, ←rat_cast_eq_coe, ha]) }

theorem nat_to_subfield [char_zero L] (J : set L) [hj : is_subfield J]
: ∀ n : ℕ, ↑n ∈ J 
| 0 := hj.zero_mem
| (n + 1) := by rw nat.cast_succ; exact is_add_submonoid.add_mem (nat_to_subfield n) hj.one_mem

theorem int_to_subfield [char_zero L] (J : set L) [hj : is_subfield J]
: ∀ n : ℤ, ↑n ∈ J 
| (int.of_nat n) := by rw [int.of_nat_eq_coe, int.cast_coe_nat]; apply nat_to_subfield
| (int.neg_succ_of_nat n) := by 
    { rw [int.cast_neg_succ_of_nat], 
      apply is_add_subgroup.neg_mem, 
      apply is_add_submonoid.add_mem, 
      apply nat_to_subfield, 
      apply hj.one_mem }

theorem prime_subfield_of_char_zero [char_zero L] : @prime_subfield L _ = rat_cast_img :=
begin
  ext, split,
  { exact λ hp, hp _ rat_cast_img_subfield },
  { rintro ⟨q, hq⟩ J HJ,
    rw [rat.num_denom q, rat_cast_eq_coe, rat.cast_mk, div_eq_mul_inv] at hq, rw ←hq,
    apply @is_submonoid.mul_mem _ _ _ HJ.to_is_submonoid _ _, 
    apply @int_to_subfield _ _ _ _ HJ,
    apply HJ.inv_mem,
    apply @int_to_subfield _ _ _ _ HJ }
end

def int_cast_ker_set := is_add_group_hom.ker (@int.cast L _ _ _ _)

def int_cast_ker : ideal ℤ :=
{ carrier := @int_cast_ker_set L _,
  zero := (is_add_group_hom.mem_ker int.cast).mpr int.cast_zero,
  add := λ x y hx hy,
    (is_add_group_hom.mem_ker int.cast).mpr (eq.trans (int.cast_add _ _) 
      (by rw [
        (is_add_group_hom.mem_ker int.cast).mp hx, 
        (is_add_group_hom.mem_ker int.cast).mp hy, zero_add] 
      : int.cast x + int.cast y = _)),
  smul := λ c x hx, by 
  { have hx' : ↑x = (0 : L) := (is_add_group_hom.mem_ker int.cast).mp hx,
    apply (is_add_group_hom.mem_ker int.cast).mpr,
    rw [smul_eq_mul, int_cast_eq_coe, int.cast_mul, hx', mul_zero] } }

theorem int_cast_ker_singleton [char_zero L] : @int_cast_ker_set L _ = {0} :=
by ext; simp [int_cast_ker_set, is_add_group_hom.mem_ker]; exact int.cast_eq_zero

theorem int_cast_ker_not_singleton (hn : ¬ injective (@int.cast L _ _ _ _)) 
: ∃ (n : ℤ), n ≠ 0 ∧ ↑ n = (0 : L) :=
begin
  simp [(not_forall_not).symm, not_and'],
  intro hs, apply hn, intros a b hab,
  rw [←sub_eq_zero, int_cast_eq_coe, int_cast_eq_coe, ←int.cast_sub] at hab,
  rw [←sub_eq_zero], exact hs _ hab,
end

theorem int_cast_ker'_principal : (@int_cast_ker L _).is_principal 
:= principal_ideal_domain.principal _

/-
theorem int_cast_ker_is_multiples (hn : ¬ injective (@int.cast L _ _ _ _))
: ∃ n : ℤ, n ≠ 0 ∧ (∀ m : ℤ, (↑m = (0 : L) ↔ (∃ k : ℤ, m = k * n))) := 
begin
  sorry
end
lemma int_cast_ker_has_multiples (hn : ¬ injective (@int.cast L _ _ _ _))
: ∃ n : ℤ, n ≠ 0 ∧ ∀ k : ℤ, ↑(k * n) = (0 : L) :=
begin
  let n := classical.some (int_cast_ker_not_singleton hn),
  have hn : n ≠ 0 ∧ ↑ n = (0 : L) 
  := classical.some_spec (int_cast_ker_not_singleton hn),
  existsi n, exact ⟨hn.1, λ k, by rw [int.cast_mul, hn.2, mul_zero]⟩,
end

-/

include homf

theorem inj_field_hom : injective f := λ a b hf, 
by { rwa [←sub_eq_zero, ←is_ring_hom.map_sub f, is_field_hom.map_eq_zero f, sub_eq_zero] at hf }

def algebraic (a : L) := ∃ p : polynomial K, polynomial.eval₂ f a p = 0
def transcendental (a : L) := ¬ (algebraic _ homf a)

