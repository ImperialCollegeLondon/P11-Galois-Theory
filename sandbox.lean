import algebra.euclidean_domain
import ring_theory.euclidean_domain
import data.polynomial
open euclidean_domain 

#check @ideal.is_coprime_def
#check @dvd_add
#check @mul_add
#check @dvd_mul_right
#check @dvd_mul_of_dvd_right
-- theorem mul_dvd_of_coprime {α : Type} [euclidean_domain α] 
-- (x y z : α) (H : ideal.is_coprime x y) (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z 
-- := let ⟨a,b,hab⟩ := ideal.is_coprime_def.1 H 1 in 
-- (calc a * x * z + b * y * z = (a * x + b * y) * z : sorry 
-- ... = 1 * z : sorry 
-- ... = z : sorry ) ▸ dvd_add 
-- (dvd_mul_of_dvd_right _ b) _ 
#check @polynomial.X

universes u v

def pairwise_coprime {α : Type u} [comm_ring α] {I : Type v} (s : I → α) : Prop :=
∀ i j : I, i ≠ j → ideal.is_coprime (s i) (s j)
#check @ideal.is_coprime_def

lemma ideal.is_coprime_def' {α : Type u} [comm_ring α] {x y : α} :
  ideal.is_coprime x y ↔ ∃ (a b : α), a * x + b * y = 1 :=
⟨λ h, ideal.is_coprime_def.1 h 1,
λ ⟨a, b, h⟩, ideal.is_coprime_def.2 $ λ z,
⟨z * a, z * b, by rw [mul_assoc, mul_assoc, ← mul_add, h, mul_one]⟩⟩

#check @neg_mul_eq_neg_mul_symm
#check @sub_eq_add_neg
-- a * b + (-a) * d
-- a * b + -(a * d)
-- a * b - a * d
-- a * (b - d)
#check mul_sub
-- dsimp only
#check sub_sub_sub_cancel_left
#check @sub_ne_zero_of_ne
#check function.injective.ne
#check polynomial.C_sub

theorem pairwise_coprime_X_sub {α : Type u} [field α] {I : Type v}
  {s : I → α} (H : function.injective s) :
  pairwise_coprime (λ i : I, polynomial.X - polynomial.C (s i)) :=
λ i j hij, have h : s j - s i ≠ 0, from sub_ne_zero_of_ne $ function.injective.ne H hij.symm,
ideal.is_coprime_def'.2  ⟨polynomial.C (s j - s i)⁻¹, -polynomial.C (s j - s i)⁻¹,
by rw [neg_mul_eq_neg_mul_symm, ← sub_eq_add_neg, ← mul_sub, sub_sub_sub_cancel_left,
    ← polynomial.C_sub, ← polynomial.C_mul, inv_mul_cancel h, polynomial.C_1]⟩

theorem mul_dvd_of_coprime {α : Type u} [comm_ring α] {x y z : α} (H : ideal.is_coprime x y)
  (H1 : x ∣ z) (H2 : y ∣ z) : x * y ∣ z :=
begin
  obtain ⟨a, b, h⟩ := ideal.is_coprime_def.1 H 1,
  rw [← mul_one z, ← h, mul_add],
  apply dvd_add,
  { rw [mul_comm z, mul_assoc],
    exact dvd_mul_of_dvd_right (mul_dvd_mul_left _ H2) _ },
  { rw [mul_comm b, ← mul_assoc],
    exact dvd_mul_of_dvd_left (mul_dvd_mul_right H1 _) _ }
end

#check finset.induction_on
#check ()
#check unit.star

/-

x,y,z pwise coprime
a x + b z = 1 
c y + d z = 1
xy,z coprime?
a c x y + (...) z = 1

-/

theorem is_coprime_prod_of_pairwise_coprime {α : Type u} [comm_ring α] 
  {I : Type v} {s : I → α} (hs : pairwise_coprime s) {t : finset I} {a : I} 
  (hat : a ∉ t) : ideal.is_coprime (s a) (t.prod s) :=
sorry

theorem finset.prod_dvd_of_coprime {α : Type u} [comm_ring α] {I : Type v}
  {s : I → α} {z : α} (Hs : pairwise_coprime s) (Hs1 : ∀ i, s i ∣ z) {t : finset I} :
  t.prod s ∣ z :=
by haveI := classical.dec_eq I; exact
finset.induction_on t (one_dvd z) (
  λ a r har ih, by { rw finset.prod_insert har; 
  exact mul_dvd_of_coprime (is_coprime_prod_of_pairwise_coprime Hs har) (Hs1 a) ih}
)

theorem fintype.prod_dvd_of_coprime {α : Type u} [comm_ring α] {I : Type v} [fintype I]
  {s : I → α} {z : α} (Hs : pairwise_coprime s) (Hs1 : ∀ i, s i ∣ z) :
  finset.univ.prod s ∣ z :=
finset.prod_dvd_of_coprime Hs Hs1