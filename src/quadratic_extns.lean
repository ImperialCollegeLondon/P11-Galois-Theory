import data.rat
import data.polynomial
import data.int.basic
import data.set
import ring_theory.adjoin_root
import ring_theory.polynomial
import data.nat.prime
import algebra.ring
import .normal
import data.finsupp
import linear_algebra.finite_dimensional

noncomputable theory
universes u v

open polynomial
open finsupp
open finite_dimensional

variables {F : Type u} {L : Type v}
variables [field F] [field L] [algebra F L] [finite_dimensional F L]

lemma sub_eq_plus_minus (a : F) : (X - C a) = (X + C (-a)) :=
by { simp, ring }

lemma zero_eq_zero_coe : (0 : with_bot ℕ) = ↑(0 : ℕ) :=
by simp

lemma one_eq_one_coe : (1 : with_bot ℕ) = ↑(1 : ℕ) :=
by simp

lemma two_eq_two_coe : (2 : with_bot ℕ) = ↑(2 : ℕ) :=
by simp [bit0]

lemma coe_sum_eq_sum_coe (a b : ℕ) : ↑(a + b) = ↑a + (↑b : with_bot ℕ) :=
by simp

lemma ne_zero_of_degree_eq_n_gt {p : polynomial F} {n : nat} 
  (hn : 0 < n) (hp : degree p = n) : (p ≠ 0) :=
begin 
have degree_gt_zero : 0 < degree p,
  { simp [hp, zero_eq_zero_coe, ←with_bot.some_eq_coe],
    exact hn,
    },
apply ne_zero_of_degree_gt degree_gt_zero,
end

lemma ne_zero_of_degree_one {p : polynomial F}
  (hp : degree p = 1) : (p ≠ 0) :=
ne_zero_of_degree_eq_n_gt zero_lt_one hp

lemma ne_zero_of_degree_two {p : polynomial F}
  (hp : degree p = 2) : (p ≠ 0) := 
ne_zero_of_degree_eq_n_gt zero_lt_two hp

lemma splits_of_degree_two_root (f : polynomial F) 
(f_deg2 : degree f = 2) (a : F) (ha : is_root f a) : 
(splits (algebra_map F L) f) :=
begin
intros,
let i := (algebra_map F L),
let f1 := (X - C a),
have f_nz : f ≠ 0,
  from ne_zero_of_degree_two f_deg2,
have sub_eq_plus_minus : (X - C a) = (X + C (-a)),
{ simp, ring },
have d : f1 ∣ f, 
  from iff.elim_right dvd_iff_is_root ha,
have f1_deg_1 : degree f1 = 1,
by simp [f1],
have f1_nz : f1 ≠ 0,
  from ne_zero_of_degree_one f1_deg_1,
have f1_monic : monic f1,
{ rw congr_arg monic sub_eq_plus_minus, -- this ought to be able to be done by simp
  apply (monic_X_add_C (-a)) },
let f2 := (f /ₘ f1),
have f2_nz : f2 ≠ 0,
{ simp [div_by_monic_eq_zero_iff f1_monic f1_nz, f_deg2],
  rw [two_eq_two_coe], 
  rw [one_eq_one_coe],
  simp [←with_bot.some_eq_coe] },
have f2_deg_1 : degree f2 = 1, -- this section is unwieldly
{ have equation : degree f1 + degree (f /ₘ f1) = degree f,
  { have deg_f1_lt_deg_f : degree f1 ≤ degree f,
    { simp [f1_deg_1, f_deg2],
      rw [two_eq_two_coe],
      rw [one_eq_one_coe],
      simp [←with_bot.some_eq_coe] },
    apply degree_add_div_by_monic f1_monic deg_f1_lt_deg_f },
  have equivalence : degree f1 + degree (f /ₘ f1) = degree f ↔ degree f2 = 1,
  { calc degree f1 + degree (f /ₘ f1) = degree f
       ↔ degree f1 + degree f2 = degree f : by simp [f2]
   ... ↔ 1 + degree f2 = 2 : by rw [f1_deg_1, f_deg2]
   ... ↔ ↑(1) + degree f2 = ↑(2) : by rw [two_eq_two_coe, one_eq_one_coe]
   ... ↔ ↑(1) + ↑(nat_degree f2) = ↑(2) : by rw [degree_eq_nat_degree f2_nz]
   ... ↔ ↑((1 : ℕ) + nat_degree f2) = ↑((2 : ℕ)) : by rw [coe_sum_eq_sum_coe]
   ... ↔ (1 + nat_degree f2) = (2) 
           : with_bot.coe_eq_coe
   ... ↔ nat_degree f2 = 1 : by simp [bit0]
   ... ↔ degree f2 = 1 : by simp [←degree_eq_iff_nat_degree_eq f2_nz]},
  rw [←equivalence],
  apply equation },
have s1 : splits i f1,
  by apply splits_of_degree_eq_one i f1_deg_1,
have s2 : splits i f2,
  by apply splits_of_degree_eq_one i f2_deg_1,
have mul_f : f = f1 * f2,
{ simp [f2, f1],
  exact (eq.symm (iff.elim_right mul_div_by_monic_eq_iff_is_root ha)) },
rw congr_arg (splits i) mul_f,
apply splits_mul i s1 s2
end

lemma degree_le_findim (x : L) {hx : is_integral F x} : 
degree (minimal_polynomial hx) ≤ findim F L :=
sorry

theorem normal_of_degree_two_extension (h : findim F L = 2) :
normal F L :=
sorry