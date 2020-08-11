import data.set.function

universes u v

variables {α : Type u} {β : Type v}

open set

theorem set.inj_on.insert {f : α → β} {s : set α} {a : α} (has : a ∉ s) :
  set.inj_on f (insert a s) ↔ set.inj_on f s ∧ f a ∉ f '' s :=
⟨λ hf, ⟨hf.mono $ subset_insert a s,
  λ ⟨x, hxs, hx⟩, has $ mem_of_eq_of_mem (hf (or.inl rfl) (or.inr hxs) hx.symm) hxs⟩,
λ ⟨h1, h2⟩ x hx y hy hfxy, or.cases_on hx
  (λ hxa : x = a, or.cases_on hy
    (λ hya : y = a, hxa.trans hya.symm)
    (λ hys : y ∈ s, h2.elim ⟨y, hys, hxa ▸ hfxy.symm⟩))
  (λ hxs : x ∈ s, or.cases_on hy
    (λ hya : y = a, h2.elim ⟨x, hxs, hya ▸ hfxy⟩)
    (λ hys : y ∈ s, h1 hxs hys hfxy))⟩
