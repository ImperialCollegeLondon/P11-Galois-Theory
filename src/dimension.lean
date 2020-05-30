import linear_algebra.dimension
import .cardinal

universes u v w u₁

variables {K : Type u} [field K] {V : Type v} [add_comm_group V] [vector_space K V]

theorem is_basis.mk_eq_dim' {b : set V} (hb : is_basis K (λ x : b, (x : V))) :
  cardinal.mk b = vector_space.dim K V :=
(vector_space.dim K V).lift_id ▸ hb.mk_eq_dim ▸ (cardinal.mk b).lift_id.symm

theorem dim_le {n : ℕ} (H : ∀ s : finset V, linear_independent K (λ i : (↑s : set V), (i : V)) → s.card ≤ n) :
  vector_space.dim K V ≤ n :=
let ⟨b, hb⟩ := exists_is_basis K V in
hb.mk_eq_dim' ▸ card_le_of (λ s, @finset.card_map _ _ ⟨_, subtype.val_injective⟩ s ▸ H _
(by { refine hb.1.mono (λ y h, _),
  rw [finset.mem_coe, finset.mem_map] at h, rcases h with ⟨x, hx, rfl⟩, exact x.2 } ))

theorem le_dim {ι : Type w} (v : ι → V) (hs : linear_independent K v) :
  ((cardinal.mk ι).lift : cardinal.{(max w v u₁)}) ≤ ((vector_space.dim K V).lift : cardinal.{(max v w u₁)}) :=
cardinal.mk_range_eq_lift (hs.injective zero_ne_one) ▸ dim_span hs ▸ cardinal.lift_le.2 (dim_submodule_le _)
