/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau

Adjoining elements to a subring.
-/

import .balgebra
import ring_theory.noetherian
import ring_theory.subring

universes u v

open lattice submodule

namespace ring

variables {R : Type u} {A : Type v}
variables [comm_ring R] [comm_ring A]
variables {i : algebra R A} {s t : set A}

theorem closure_mono {s t : set R} (H : s ⊆ t) : closure s ⊆ closure t :=
closure_subset $ set.subset.trans H subset_closure

theorem subset_adjoin : s ⊆ i.adjoin s :=
set.subset.trans (set.subset_union_right _ _) subset_closure

theorem adjoin_mono (H : s ⊆ t) : i.adjoin s ≤ i.adjoin t :=
closure_subset (set.subset.trans (set.union_subset_union_right _ H) subset_closure)

variables (i s t)
theorem adjoin_adjoin : (i.adjoin s).under ((algebra.of_subring (i.adjoin s : set A)).adjoin t) =
  i.adjoin (s ∪ t) :=
le_antisymm
  (closure_subset $ set.union_subset
    (set.range_subset_iff.2 $ λ x, adjoin_mono (set.subset_union_left _ _) x.2)
    (set.subset.trans (set.subset_union_right _ _) subset_adjoin))
  (closure_mono $ set.union_subset
    (set.range_subset_iff.2 $ λ r, or.inl ⟨(i.adjoin s).algebra r, rfl⟩)
    (set.union_subset_union_left _ $ λ x hxs, ⟨⟨_, subset_adjoin hxs⟩, rfl⟩))

def linear_map.module : module R (i.mod →ₗ i.mod) := linear_map.module

local attribute [instance] linear_map.module

instance : has_mul (submodule R i.mod) :=
⟨λ S1 S2, ⨆ s : S1, S2.map $ i.lmul s.1⟩

variables {i} {S1 S2 T : submodule R i.mod} {s1 s2 : A}

theorem mul_mem_mul (hs1 : s1 ∈ S1) (hs2 : s2 ∈ S2) : s1 * s2 ∈ S1 * S2 :=
have _ ≤ S1 * S2 := le_supr _ ⟨s1, hs1⟩, this ⟨s2, hs2, rfl⟩

theorem mul_le : S1 * S2 ≤ T ↔ ∀ (s1 ∈ S1) (s2 ∈ S2), s1 * s2 ∈ T :=
⟨λ H s1 hs1 s2 hs2, H (mul_mem_mul hs1 hs2),
λ H, supr_le $ λ ⟨s1, hs1⟩, map_le_iff_le_comap.2 $ λ s2 hs2, H s1 hs1 s2 hs2⟩

@[elab_as_eliminator] protected theorem mul_induction
  {r : i.mod} {C : i.mod → Prop} (hr : r ∈ S1 * S2)
  (hm : ∀ (s1 ∈ S1) (s2 ∈ S2), C (s1 * s2))
  (h0 : C 0) (ha : ∀ x y, C x → C y → C (x + y))
  (hs : ∀ r x, C x → C (has_scalar.smul.{u v} r x)) : C r :=
(@mul_le _ _ _ _ _ _ _ ⟨C, h0, ha, hs⟩).2 hm hr

theorem madjoin_union : (i.adjoin (s ∪ t)).to_submodule =
  (i.adjoin s).to_submodule * (i.adjoin t).to_submodule :=
begin
  apply le_antisymm,
  { intros r hr, refine add_group.in_closure.rec_on hr _ _ _ _,
    { intros r hr,
      suffices : ∃ (s' ∈ i.adjoin s) (t' ∈ i.adjoin t), s' * t' = r,
      { rcases this with ⟨s', hs', t', ht', rfl⟩, exact mul_mem_mul hs' ht' },
      refine monoid.in_closure.rec_on hr _ _ _,
      { rintros r (hrS | hrs | hrt),
        { exact ⟨r, (i.adjoin s).range_le hrS, 1, (i.adjoin t).range_le ⟨1, i.map_one⟩, mul_one _⟩ },
        { exact ⟨r, subset_adjoin hrs, 1, (i.adjoin t).range_le ⟨1, i.map_one⟩, mul_one _⟩ },
        { exact ⟨1, (i.adjoin s).range_le ⟨1, i.map_one⟩, r, subset_adjoin hrt, one_mul _⟩ } },
      { exact ⟨1, (i.adjoin s).range_le ⟨1, i.map_one⟩, 1, (i.adjoin t).range_le ⟨1, i.map_one⟩, mul_one _⟩ },
      { rintros x y hx hy ⟨p1, hp1, q1, hq1, rfl⟩ ⟨p2, hp2, q2, hq2, rfl⟩,
        rw [mul_assoc, mul_left_comm q1, ← mul_assoc],
        exact ⟨p1 * p2, subalgebra.mem_coe.1 (is_submonoid.mul_mem hp1 hp2), q1 * q2, subalgebra.mem_coe.1 (is_submonoid.mul_mem hq1 hq2), rfl⟩ } },
    { rw mem_coe, exact zero_mem _ },
    { intros r hr ih, rw ← neg_one_smul, rw mem_coe, exact smul_mem _ _ ih },
    { intros p q hp hq ihp ihq, rw mem_coe, exact add_mem _ ihp ihq } },
  { refine mul_le.2 (λ s1 hs1 s2 hs2, subalgebra.mem_coe.1 _),
    exact is_submonoid.mul_mem (adjoin_mono (set.subset_union_left _ _) hs1)
      (adjoin_mono (set.subset_union_right _ _) hs2) }
end

theorem span_mul_span (s1 s2 : set i.mod) :
  (span s1 * span s2 : submodule R i.mod) = span ((s1.prod s2).image (λ p, p.1 * p.2)) :=
le_antisymm
  (mul_le.2 $ λ x1 hx1 x2 hx2, span_induction hx1
    (λ y1 hy1, span_induction hx2
      (λ y2 hy2, subset_span ⟨(y1, y2), ⟨hy1, hy2⟩, rfl⟩)
      ((mul_zero y1).symm ▸ zero_mem _)
      (λ r1 r2, (mul_add y1 r1 r2).symm ▸ add_mem _)
      (λ s r, (algebra.mul_smul i s y1 r).symm ▸ smul_mem _ _))
    ((zero_mul x2).symm ▸ zero_mem _)
    (λ r1 r2, (add_mul r1 r2 x2).symm ▸ add_mem _)
    (λ s r, (i.smul_mul s r x2).symm ▸ smul_mem _ _))
  (span_le.2 (set.image_subset_iff.2 $ λ ⟨x1, x2⟩ ⟨hx1, hx2⟩,
    mul_mem_mul (subset_span hx1) (subset_span hx2)))

theorem fg_mul (hs1 : S1.fg) (hs2 : S2.fg) : (S1 * S2).fg :=
let ⟨s1, hf1, hs1⟩ := fg_def.1 hs1, ⟨s2, hf2, hs2⟩ := fg_def.1 hs2 in
fg_def.2 ⟨(s1.prod s2).image (λ p, p.1 * p.2),
set.finite_image _ (set.finite_prod hf1 hf2),
span_mul_span s1 s2 ▸ hs1 ▸ hs2 ▸ rfl⟩

theorem exists_list_of_mem_closure' {s : set R} {a : R} (h : a ∈ closure s) :
  (∃ L : list (list R), (∀ l ∈ L, ∀ x ∈ l, x ∈ s ∨ x = (-1:R)) ∧ (L.map list.prod).sum = a) :=
add_group.in_closure.rec_on h
  (λ x hx, match x, monoid.exists_list_of_mem_closure hx with
    | _, ⟨L, h1, rfl⟩ := ⟨[L], list.forall_mem_singleton.2 (λ r hr, or.inl (h1 r hr)), zero_add _⟩
    end)
  ⟨[], list.forall_mem_nil _, rfl⟩
  (λ b _ ih, match b, ih with
    | _, ⟨L1, h1, rfl⟩ := ⟨L1.map (list.cons (-1)),
      λ L2 h2, match L2, list.mem_map.1 h2 with
        | _, ⟨L3, h3, rfl⟩ := list.forall_mem_cons.2 ⟨or.inr rfl, h1 L3 h3⟩
        end,
      by simp only [list.map_map, (∘), list.prod_cons, neg_one_mul];
      exact list.rec_on L1 neg_zero.symm (λ hd tl ih,
        by rw [list.map_cons, list.sum_cons, ih, list.map_cons, list.sum_cons, neg_add])⟩
    end)
  (λ r1 r2 hr1 hr2 ih1 ih2, match r1, r2, ih1, ih2 with
    | _, _, ⟨L1, h1, rfl⟩, ⟨L2, h2, rfl⟩ := ⟨L1 ++ L2, list.forall_mem_append.2 ⟨h1, h2⟩,
      by rw [list.map_append, list.sum_append]⟩
    end)

variables {s}
@[elab_as_eliminator]
protected theorem in_closure.rec_on {C : A → Prop} {x : A} (hx : x ∈ closure s)
  (h1 : C 1) (hneg1 : C (-1)) (hs : ∀ z ∈ s, ∀ n, C n → C (z * n))
  (ha : ∀ {x y}, C x → C y → C (x + y)) : C x :=
begin
  have h0 : C 0 := add_neg_self (1:A) ▸ ha h1 hneg1,
  rcases exists_list_of_mem_closure' hx with ⟨L, HL, rfl⟩, clear hx,
  induction L with hd tl ih, { exact h0 },
  rw list.forall_mem_cons at HL,
  suffices : C (list.prod hd),
  { rw [list.map_cons, list.sum_cons],
    exact ha this (ih HL.2) },
  replace HL := HL.1, clear ih tl,
  suffices : ∃ L : list A, (∀ x ∈ L, x ∈ s) ∧ (list.prod hd = list.prod L ∨ list.prod hd = -list.prod L),
  { rcases this with ⟨L, HL', HP | HP⟩,
    { rw HP, clear HP HL hd, induction L with hd tl ih, { exact h1 },
      rw list.forall_mem_cons at HL',
      rw list.prod_cons,
      exact hs _ HL'.1 _ (ih HL'.2) },
    rw HP, clear HP HL hd, induction L with hd tl ih, { exact hneg1 },
    rw [list.prod_cons, neg_mul_eq_mul_neg],
    rw list.forall_mem_cons at HL',
    exact hs _ HL'.1 _ (ih HL'.2) },
  induction hd with hd tl ih,
  { exact ⟨[], list.forall_mem_nil _, or.inl rfl⟩ },
  rw list.forall_mem_cons at HL,
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩; cases HL.1 with hhd hhd,
  { exact ⟨hd :: L, list.forall_mem_cons.2 ⟨hhd, HL'⟩, or.inl $
      by rw [list.prod_cons, list.prod_cons, HP]⟩ },
  { exact ⟨L, HL', or.inr $ by rw [list.prod_cons, hhd, neg_one_mul, HP]⟩ },
  { exact ⟨hd :: L, list.forall_mem_cons.2 ⟨hhd, HL'⟩, or.inr $
      by rw [list.prod_cons, list.prod_cons, HP, neg_mul_eq_mul_neg]⟩ },
  { exact ⟨L, HL', or.inl $ by rw [list.prod_cons, hhd, HP, neg_one_mul, _root_.neg_neg]⟩ }
end
variables (s)

theorem madjoin_eq_span : (i.adjoin s).to_submodule = span (monoid.closure s) :=
begin
  apply le_antisymm,
  { intros r hr, rcases ring.exists_list_of_mem_closure' hr with ⟨L, HL, rfl⟩, clear hr,
    induction L with hd tl ih, { rw mem_coe, exact zero_mem _ },
    rw list.forall_mem_cons at HL,
    rw [list.map_cons, list.sum_cons, mem_coe],
    refine submodule.add_mem _ _ (ih HL.2),
    replace HL := HL.1, clear ih tl,
    suffices : ∃ z r (hr : r ∈ monoid.closure s), has_scalar.smul.{u v} z r = list.prod hd,
    { rcases this with ⟨z, r, hr, hzr⟩, rw ← hzr,
      exact smul_mem _ _ (subset_span hr) },
    induction hd with hd tl ih, { exact ⟨1, 1, is_submonoid.one_mem _, one_smul _⟩ },
    rw list.forall_mem_cons at HL,
    rcases (ih HL.2) with ⟨z, r, hr, hzr⟩, rw [list.prod_cons, ← hzr],
    rcases HL.1 with ⟨⟨hd, rfl⟩ | hs⟩ | rfl,
    { refine ⟨hd * z, r, hr, _⟩, rw [i.smul_def, i.smul_def, i.map_mul, mul_assoc], refl },
    { refine ⟨z, hd * r, is_submonoid.mul_mem (monoid.subset_closure hs) hr, _⟩,
      rw [i.smul_def, i.smul_def, mul_left_comm] },
    { refine ⟨-z, r, hr, _⟩, rw [neg_smul, neg_one_mul] } },
  exact span_le.2 (show monoid.closure s ⊆ i.adjoin s, from monoid.closure_subset subset_adjoin)
end

variables {s t}
theorem fg_trans (h1 : fg (i.adjoin s).to_submodule)
  (h2 : fg ((algebra.of_subring (i.adjoin s : set A)).adjoin t).to_submodule) :
  fg (i.adjoin (s ∪ t)).to_submodule :=
begin
  rcases fg_def.1 h1 with ⟨p, hp, hp'⟩,
  rcases fg_def.1 h2 with ⟨q, hq, hq'⟩,
  refine fg_def.2 ⟨set.image (λ z : i.mod × i.mod, z.1 * z.2) (p.prod q),
    set.finite_image _ (set.finite_prod hp hq), le_antisymm _ _⟩,
  { rw [span_le, set.image_subset_iff], rintros ⟨x, y⟩ ⟨hx, hy⟩,
    change x * y ∈ _, refine is_submonoid.mul_mem _ _,
    { have : x ∈ (i.adjoin s).to_submodule, { rw ← hp', exact subset_span hx },
      exact adjoin_mono (set.subset_union_left _ _) this },
    have : y ∈ ((algebra.of_subring (i.adjoin s : set A)).adjoin t).to_submodule, { rw ← hq', exact subset_span hy },
    change y ∈ i.adjoin (s ∪ t), rw ← adjoin_adjoin, exact this },
  intros r hr, change r ∈ i.adjoin (s ∪ t) at hr, rw ← adjoin_adjoin at hr,
  change r ∈ ((algebra.of_subring (i.adjoin s : set A)).adjoin t).to_submodule at hr,
  rw [← hq', mem_span_iff_lc] at hr, rcases hr with ⟨l, hlq, rfl⟩,
  haveI := classical.dec_eq i.mod,
  rw [lc.total_apply, finsupp.sum, mem_coe], refine sum_mem _ _,
  intros z hz, change (l z).1 * _ ∈ _,
  have : (l z).1 ∈ (i.adjoin s).to_submodule := (l z).2,
  rw [← hp', mem_span_iff_lc] at this, rcases this with ⟨l2, hlp, hl⟩, rw ← hl,
  rw [lc.total_apply, finsupp.sum_mul], refine sum_mem _ _,
  intros t ht, change _ * _ ∈ _, rw algebra.smul_mul, refine smul_mem _ _ _,
  exact subset_span ⟨⟨t, z⟩, ⟨hlp ht, hlq hz⟩, rfl⟩
end

end ring