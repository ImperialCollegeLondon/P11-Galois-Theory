import algebra.group_ring_action

universes u v

variables (M : Type u) [monoid M] (α : Type v) [mul_action M α]

/-- Embedding induced by action. -/
def mul_action.to_fun : α ↪ (M → α) :=
⟨λ x m, m • x, λ x y H, one_smul M x ▸ one_smul M y ▸ by convert congr_fun H 1⟩

variables {M α}

@[simp] lemma mul_action.to_fun_apply (m : M) (x : α) : mul_action.to_fun M α x m = m • x :=
rfl
