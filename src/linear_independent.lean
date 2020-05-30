import linear_algebra.basis

universes u v w

variables {K : Type u} [field K] {V : Type v} [add_comm_group V] [vector_space K V]

theorem linear_independent_insert {s : set V} {a : V} (has : a ∉ s) :
  linear_independent K (λ x : insert a s, (x : V)) ↔
  linear_independent K (λ x : s, (x : V)) ∧ a ∉ submodule.span K s :=
⟨λ h, ⟨h.mono $ set.subset_insert a s,
have (λ (x : ↥(insert a s)), ↑x) '' (set.univ \ {⟨a, set.mem_insert a s⟩}) = s,
from set.ext $ λ x, ⟨λ ⟨y, hy1, hy2⟩, hy2 ▸ y.2.resolve_left (λ H, hy1.2 $ subtype.eq H),
  λ hx, ⟨⟨x, set.mem_insert_of_mem a hx⟩,
    ⟨trivial, λ H, has $ (show x = a, from congr_arg subtype.val H) ▸ hx⟩, rfl⟩⟩,
this ▸ linear_independent_iff_not_mem_span.1 h ⟨a, set.mem_insert a s⟩⟩,
λ ⟨h1, h2⟩, h1.insert h2⟩

variables {R : Type u} [ring R] {M : Type v} [add_comm_group M] [module R M] {ι : Type w}

theorem finsupp.total_apply_of_mem_supported {f : ι → M} {g : ι →₀ R} {s : finset ι}
  (hs : g ∈ finsupp.supported R R (↑s : set ι)) :
  finsupp.total ι M R f g = s.sum (λ i, g i • f i) :=
(finsupp.total_apply R g).trans $ finset.sum_subset hs $ λ x hxs hxg,
show g x • f x = 0, by rw [finsupp.not_mem_support_iff.1 hxg, zero_smul]
