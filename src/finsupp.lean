import data.finsupp algebra.pi_instances

universes u v w u₁ v₁ w₁

variables {α : Type u} {ι : Type v} {β : Type w} [add_comm_monoid β]
variables {s : finset α} {f : α → (ι →₀ β)} (i : ι)

theorem finset.sum_apply' : (s.sum f) i = s.sum (λ x, f x i) :=
(s.sum_hom $ λ g : ι →₀ β, g i).symm

variables {γ : Type u₁} {δ : Type v₁} [add_comm_monoid δ]
variables (g : ι →₀ β) (k : ι → β → γ → δ) (x : γ)

theorem finsupp.sum_apply' : g.sum k x = g.sum (λ i b, k i b x) :=
finset.sum_apply _ _ _

variables {ε : Type w₁} [add_comm_monoid ε]
variables {t : ι → β → ε} (h0 : ∀ i, t i 0 = 0) (h1 : ∀ i x y, t i (x + y) = t i x + t i y)
include h0 h1

open_locale classical

theorem finsupp.sum_sum_index' : (s.sum f).sum t = s.sum (λ x, (f x).sum t) :=
finset.induction_on s rfl $ λ a s has ih,
by simp_rw [finset.sum_insert has, finsupp.sum_add_index h0 h1, ih]
