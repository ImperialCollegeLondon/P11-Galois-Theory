import data.polynomial
import data.nat.prime

open polynomial

theorem eisensteins_criteron (f : polynomial ℤ) :
(∃ (p : ℕ), (prime p) ∧
(∀ (i : ℕ), (0 ≤ i ∧ i < (nat_degree f) → ((p : ℤ) ∣ (coeff f) i))) ∧
(¬((p : ℤ) ∣ (coeff f) (nat_degree f))) ∧
(¬((p * p : ℤ) ∣ (coeff f) 0))
) → irreducible f :=
sorry