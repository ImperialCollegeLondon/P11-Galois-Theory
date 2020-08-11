import linear_algebra.basis
import .set

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

theorem linear_independent_equiv {ι κ : Type*} (e : ι ≃ κ) {f : κ → V} :
  linear_independent K (f ∘ e) ↔ linear_independent K f :=
⟨λ h, function.comp.right_id f ▸ e.self_comp_symm ▸ h.comp _ e.symm.injective,
λ h, h.comp _ e.injective⟩

theorem linear_independent_equiv' {ι κ : Type*} (e : ι ≃ κ) {f : κ → V} {g : ι → V} (h : f ∘ e = g) :
  linear_independent K g ↔ linear_independent K f :=
h ▸ linear_independent_equiv e

theorem linear_independent_image {ι} {s : set ι} {f : ι → V} (hf : set.inj_on f s) :
  linear_independent K (λ x : s, f x) ↔ linear_independent K (λ x : f '' s, (x : V)) :=
linear_independent_equiv' (equiv.set.image_of_inj_on _ _ hf) rfl

theorem linear_independent.image' {ι} {s : set ι} {f : ι → V}
  (hs : linear_independent K (λ x : s, f x)) : linear_independent K (λ x : f '' s, (x : V)) :=
(linear_independent_image $ set.inj_on_iff_injective.2 hs.injective).1 hs

theorem linear_independent_insert' {ι} {s : set ι} {a : ι} {f : ι → V} (has : a ∉ s) :
  linear_independent K (λ x : insert a s, f x) ↔
  linear_independent K (λ x : s, f x) ∧ f a ∉ submodule.span K (f '' s) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { have hfas : f a ∉ f '' s := λ ⟨x, hxs, hfxa⟩, has (set.mem_of_eq_of_mem (congr_arg subtype.val $
      (@id _ (h.injective) ⟨x, or.inr hxs⟩ ⟨a, or.inl rfl⟩ hfxa)).symm hxs),
    have := h.image',
    rwa [set.image_insert_eq, linear_independent_insert hfas, ← linear_independent_image] at this,
    exact (set.inj_on_iff_injective.2 h.injective).mono (set.subset_insert _ _) },
  { cases h with h1 h2,
    have : set.inj_on f (insert a s) :=
      (set.inj_on.insert has).2 ⟨set.inj_on_iff_injective.2 h1.injective,
        λ h, h2 $ submodule.subset_span h⟩,
    have hfas : f a ∉ f '' s := λ ⟨x, hxs, hfxa⟩, has (set.mem_of_eq_of_mem
      (this (or.inr hxs) (or.inl rfl) hfxa).symm hxs),
    rw [linear_independent_image this, set.image_insert_eq, linear_independent_insert hfas],
    exact ⟨h1.image', h2⟩ }
end

variables {R : Type u} [ring R] {M : Type v} [add_comm_group M] [module R M] {ι : Type w}

theorem finsupp.total_apply_of_mem_supported {f : ι → M} {g : ι →₀ R} {s : finset ι}
  (hs : g ∈ finsupp.supported R R (↑s : set ι)) :
  finsupp.total ι M R f g = s.sum (λ i, g i • f i) :=
(finsupp.total_apply R g).trans $ finset.sum_subset hs $ λ x hxs hxg,
show g x • f x = 0, by rw [finsupp.not_mem_support_iff.1 hxg, zero_smul]
