import field_theory.splitting_field
import .big_operators

universes u v w

variables {α : Type u} {β : Type v} [field α] [field β] (i : α →+* β)

namespace polynomial

open_locale classical

theorem splits_one : splits i 1 :=
splits_C i 1

theorem splits_X_sub_C {x : α} : (X - C x).splits i :=
splits_of_degree_eq_one _ $ degree_X_sub_C x

theorem splits_of_splits_id' {f : polynomial α} (hf : (f.map i).splits (ring_hom.id β)) :
  f.splits i :=
or.cases_on hf (or.inl ∘ (map_eq_zero i).1) (λ h, or.inr $ by rwa [map_map, ring_hom.id_comp] at h)

theorem splits_mul_iff {f g : polynomial α} (hf : f ≠ 0) (hg : g ≠ 0) :
  (f * g).splits i ↔ f.splits i ∧ g.splits i :=
⟨splits_of_splits_mul i (mul_ne_zero hf hg), λ ⟨hfs, hgs⟩, splits_mul i hfs hgs⟩

theorem splits_prod {ι : Type w} {s : ι → polynomial α} {t : finset ι} :
  (∀ j ∈ t, (s j).splits i) → (t.prod s).splits i :=
begin
  refine finset.induction_on t (λ _, splits_one i) (λ a t hat ih ht, _),
  rw finset.forall_mem_insert at ht, rw finset.prod_insert hat,
  exact splits_mul i ht.1 (ih ht.2)
end

theorem splits_prod_iff {ι : Type w} {s : ι → polynomial α} {t : finset ι} :
  (∀ j ∈ t, s j ≠ 0) → ((t.prod s).splits i ↔ ∀ j ∈ t, (s j).splits i) :=
begin
  refine finset.induction_on t (λ _, ⟨λ _ _ h, h.elim, λ _, splits_one i⟩) (λ a t hat ih ht, _),
  rw finset.forall_mem_insert at ht ⊢,
  rw [finset.prod_insert hat, splits_mul_iff i ht.1 (finset.prod_ne_zero.2 ht.2), ih ht.2]
end

end polynomial
