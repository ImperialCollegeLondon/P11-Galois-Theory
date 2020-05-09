import data.polynomial
-- import data.nat.prime
import ring_theory.ideals
import ring_theory.ideal_operations
import ring_theory.unique_factorization_domain

universe u

open polynomial ideal

variables {α : Type u} [integral_domain α]

/-- An eisenstein prime is a prime ideal for which 
    the conditions of eisenstein's criteron are met -/
def is_eisenstein_prime (P : ideal α) (f : polynomial α) : Prop :=
let n := nat_degree f in
(ideal.is_prime P) ∧ 
(∀ (i : ℕ), i ≠ n → coeff f i ∈ P) ∧ -- for n < i this is vacuous
(coeff f n ∉ P) ∧
(coeff f 0 ∉ P • P)

def is_primitive (f : polynomial α) : Prop :=
∀ (a : α), (C a ∣ f) → is_unit a


theorem eisensteins_criterion (f : polynomial α) :
(∃ P : ideal α, is_eisenstein_prime P f) →
∀ (g h : polynomial α), (f = g*h) → 
(∃ (a : α), g = C a) ∨ (∃ (a : α), h = C a) :=
sorry

theorem eisensteins_criterion_primitive (f : polynomial α) :
(∃ P : ideal α, is_eisenstein_prime P f) → 
is_primitive f → irreducible f :=
sorry

variables [unique_factorization_domain α]

theorem eisensteins_criterion_ufd (f : polynomial α) :
(∃ P : ideal α, is_eisenstein_prime P f) → irreducible f :=
-- TODO: this "irreducible" should actually be irreducible
--       over the field of fractions.
sorry


-- Specialize to ℤ and ℚ --> use numbers rather than ideals
-- theorem eisensteins_criteron_int (f : polynomial ℤ) :
--
-- (∃ (p : ℕ), (prime p) ∧
-- (∀ (i : ℕ), (0 ≤ i ∧ i < (nat_degree f) → ((p : ℤ) ∣ (coeff f) i))) ∧
-- (¬((p : ℤ) ∣ (coeff f) (nat_degree f))) ∧
-- (¬((p * p : ℤ) ∣ (coeff f) 0))
-- ) → irreducible f :=
-- sorry