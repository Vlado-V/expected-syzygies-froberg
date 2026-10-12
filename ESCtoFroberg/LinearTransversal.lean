module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace ESCtoFroberg

open Module

universe u v w

variable {K : Type u} [Field K]
variable {E : Type v} [AddCommGroup E] [Module K E]
variable {ι : Type w}

def subspacesSum (V : ι → Submodule K E) (s : Finset ι) : Submodule K E :=
  ⨆ i ∈ s, V i

theorem subspacesSum_le {V : ι → Submodule K E} {s : Finset ι}
    {U : Submodule K E} (h : ∀ i ∈ s, V i ≤ U) : subspacesSum V s ≤ U :=
  iSup_le fun i => iSup_le fun hi => h i hi

theorem le_subspacesSum {V : ι → Submodule K E} {s : Finset ι} {i : ι}
    (hi : i ∈ s) : V i ≤ subspacesSum V s :=
  le_iSup_of_le i (le_iSup_of_le hi le_rfl)

@[simp] theorem subspacesSum_empty (V : ι → Submodule K E) : subspacesSum V ∅ = ⊥ := by
  simp [subspacesSum]

@[simp] theorem subspacesSum_singleton [DecidableEq ι] (V : ι → Submodule K E) (i : ι) :
    subspacesSum V {i} = V i := by
  simp [subspacesSum]

theorem subspacesSum_union [DecidableEq ι] (V : ι → Submodule K E) (s t : Finset ι) :
    subspacesSum V (s ∪ t) = subspacesSum V s ⊔ subspacesSum V t := by
  apply le_antisymm
  · apply subspacesSum_le
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact (le_subspacesSum hi).trans le_sup_left
    · exact (le_subspacesSum hi).trans le_sup_right
  · exact sup_le (subspacesSum_le fun i hi => le_subspacesSum (Finset.mem_union_left _ hi))
      (subspacesSum_le fun i hi => le_subspacesSum (Finset.mem_union_right _ hi))

theorem subspacesSum_subtype [DecidableEq ι] {p : ι → Prop} [DecidablePred p]
    (V : ι → Submodule K E) (s : Finset {i // p i}) :
    subspacesSum (fun i : {i // p i} => V i) s = subspacesSum V (s.image Subtype.val) := by
  apply le_antisymm
  · exact subspacesSum_le fun i hi => le_subspacesSum (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  · apply subspacesSum_le
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact le_subspacesSum (V := fun k : {i // p i} => V k.1) hj

theorem subspacesSum_map {F : Type v} [AddCommGroup F] [Module K F]
    (V : ι → Submodule K E) (s : Finset ι) (f : E →ₗ[K] F) :
    subspacesSum (fun i => (V i).map f) s = (subspacesSum V s).map f := by
  simp only [subspacesSum, Submodule.map_iSup]

theorem representatives_glue [DecidableEq ι] (V : ι → Submodule K E)
    (s : Finset ι) (U : Submodule K E)
    (f : {i // i ∈ s} → U) (hf : LinearIndependent K f)
    (hfmem : ∀ i : {i // i ∈ s}, (f i : E) ∈ V i.1)
    (gq : {i // i ∉ s} → E ⧸ U) (hgq : LinearIndependent K gq)
    (hgqmem : ∀ i : {i // i ∉ s}, gq i ∈ (V i.1).map U.mkQ) :
    ∃ x : ι → E, (∀ i, x i ∈ V i) ∧ LinearIndependent K x := by
  classical
  have hex : ∀ i : {i // i ∉ s}, ∃ x : E, x ∈ V i.1 ∧ U.mkQ x = gq i := by
    intro i
    exact Submodule.mem_map.mp (hgqmem i)
  choose g hgmem hg using hex
  let e := Equiv.sumCompl (fun i : ι => i ∈ s)
  let x : ι → E := (Sum.elim (fun i => (f i : E)) g) ∘ e.symm
  refine ⟨x, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ s
    · simpa [x, e, Equiv.sumCompl_symm_apply_of_pos hi] using hfmem ⟨i, hi⟩
    · simpa [x, e, Equiv.sumCompl_symm_apply_of_neg hi] using hgmem ⟨i, hi⟩
  · apply (hf.sumElim_of_quotient g ?_).comp e.symm e.symm.injective
    convert hgq using 1
    funext i
    exact hg i

theorem finrank_le_finrank_map_quotient_add [FiniteDimensional K E] (U W : Submodule K E) :
    finrank K W ≤ finrank K (W.map U.mkQ) + finrank K U := by
  let f : W →ₗ[K] E ⧸ U := U.mkQ.domRestrict W
  have hr : LinearMap.range f = W.map U.mkQ := LinearMap.range_domRestrict W U.mkQ
  have hk : (LinearMap.ker f).map W.subtype ≤ U := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    change U.mkQ y = 0 at hy
    exact (Submodule.Quotient.mk_eq_zero U).mp hy
  have hdim : finrank K (LinearMap.ker f) ≤ finrank K U := by
    rw [← Submodule.finrank_map_subtype_eq W (LinearMap.ker f)]
    exact Submodule.finrank_mono hk
  have h := f.finrank_range_add_finrank_ker
  rw [hr] at h
  exact h.symm.le.trans (Nat.add_le_add_left hdim _)

theorem finrank_sup_eq_finrank_map_quotient_add [FiniteDimensional K E] (U W : Submodule K E) :
    finrank K ↥(W ⊔ U) = finrank K (W.map U.mkQ) + finrank K U := by
  let f : ↥(W ⊔ U) →ₗ[K] E ⧸ U := U.mkQ.domRestrict (W ⊔ U)
  have hr : LinearMap.range f = W.map U.mkQ := by
    rw [LinearMap.range_domRestrict, Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  have hk : (LinearMap.ker f).map (W ⊔ U).subtype = U := by
    apply le_antisymm
    · intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      change U.mkQ y = 0 at hy
      exact (Submodule.Quotient.mk_eq_zero U).mp hy
    · intro x hx
      refine ⟨⟨x, (le_sup_right : U ≤ W ⊔ U) hx⟩, ?_, rfl⟩
      change U.mkQ x = 0
      exact (Submodule.Quotient.mk_eq_zero U).mpr hx
  have hdim : finrank K (LinearMap.ker f) = finrank K U := by
    rw [← Submodule.finrank_map_subtype_eq (W ⊔ U) (LinearMap.ker f), hk]
  have h := f.finrank_range_add_finrank_ker
  rw [hr, hdim] at h
  exact h.symm


set_option maxHeartbeats 1200000 in
/-- Linear Hall's theorem: every finite family of subspaces satisfying the
dimension inequalities admits linearly independent representatives. -/
theorem exists_linearIndependent_representatives [Fintype ι] [FiniteDimensional K E]
    (V : ι → Submodule K E)
    (hHall : ∀ s : Finset ι, s.card ≤ finrank K (subspacesSum V s)) :
    ∃ x : ι → E, (∀ i, x i ∈ V i) ∧ LinearIndependent K x := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ (J : Type w) [Fintype J] (F : Type v) [AddCommGroup F] [Module K F]
      [FiniteDimensional K F] (W : J → Submodule K F),
      Fintype.card J = n →
      (∀ s : Finset J, s.card ≤ finrank K (subspacesSum W s)) →
      ∃ x : J → F, (∀ i, x i ∈ W i) ∧ LinearIndependent K x
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J _ F _ _ _ W hcard hW
      by_cases hempty : Fintype.card J = 0
      · let : IsEmpty J := Fintype.card_eq_zero_iff.mp hempty
        exact ⟨fun i => isEmptyElim i, fun i => isEmptyElim i,
          linearIndependent_empty_type⟩
      let : Nonempty J := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hempty)
      obtain ⟨a⟩ := ‹Nonempty J›
      by_cases htight : ∃ t : Finset J, t.Nonempty ∧ t ≠ Finset.univ ∧
          finrank K (subspacesSum W t) = t.card
      · obtain ⟨t, htne, htproper, htdim⟩ := htight
        let U := subspacesSum W t
        have htlt : Fintype.card {i : J // i ∈ t} < n := by
          rw [Fintype.card_coe, ← hcard]
          exact (Finset.card_lt_card (Finset.ssubset_univ_iff.mpr htproper))
        obtain ⟨f, hfmem, hf⟩ := ih _ htlt {i : J // i ∈ t} F
          (fun i => W i.1) rfl (by
            intro s
            rw [subspacesSum_subtype]
            simpa only [Finset.card_image_of_injective _ Subtype.val_injective] using
              hW (s.image Subtype.val))
        let fU : {i : J // i ∈ t} → U := fun i =>
          ⟨f i, (le_subspacesSum i.2) (hfmem i)⟩
        have hfU : LinearIndependent K fU := hf.of_comp U.subtype
        have hcplt : Fintype.card {i : J // i ∉ t} < n := by
          obtain ⟨b, hb⟩ := htne
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := b) (by simpa using hb)
        have hQ : ∀ s : Finset {i : J // i ∉ t},
            s.card ≤ finrank K (subspacesSum (fun i : {i : J // i ∉ t} =>
              (W i.1).map U.mkQ) s) := by
          intro s
          let r : Finset J := s.image Subtype.val
          have hrdisj : Disjoint r t := by
            apply Finset.disjoint_left.mpr
            intro i hi ht
            obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
            exact j.2 ht
          have hr_card : r.card = s.card :=
            Finset.card_image_of_injective _ Subtype.val_injective
          have hdim := (finrank_sup_eq_finrank_map_quotient_add
            (K := K) U (subspacesSum W r)).le
          have hbound := hW (r ∪ t)
          rw [subspacesSum_union, Finset.card_union_of_disjoint hrdisj,
            hr_card] at hbound
          change s.card + t.card ≤ finrank K ↥(subspacesSum W r ⊔ U) at hbound
          change finrank K ↥(subspacesSum W r ⊔ U) ≤ _ at hdim
          rw [show finrank K U = t.card from htdim] at hdim
          have hout : s.card ≤ finrank K ((subspacesSum W r).map U.mkQ) := by omega
          rw [subspacesSum_map, subspacesSum_subtype]
          exact hout
        obtain ⟨gq, hgqmem, hgq⟩ := ih _ hcplt {i : J // i ∉ t} (F ⧸ U)
          (fun i => (W i.1).map U.mkQ) rfl hQ
        exact representatives_glue W t U fU hfU hfmem gq hgq hgqmem
      · have hWa : W a ≠ ⊥ := by
          have h := hW {a}
          rw [Finset.card_singleton, subspacesSum_singleton] at h
          intro heq
          rw [heq, finrank_bot] at h
          omega
        obtain ⟨z, hzmem, hz⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWa
        let U : Submodule K F := K ∙ z
        let t : Finset J := {a}
        let fU : {i : J // i ∈ t} → U := fun _ => ⟨z, Submodule.mem_span_singleton_self z⟩
        let : Subsingleton {i : J // i ∈ t} := by
          apply Subsingleton.intro
          intro i j
          apply Subtype.ext
          have hi : i.1 = a := Finset.mem_singleton.mp i.2
          have hj : j.1 = a := Finset.mem_singleton.mp j.2
          exact hi.trans hj.symm
        have hfU : LinearIndependent K fU :=
          (linearIndependent_subsingleton_index_iff fU).mpr (fun _ => by
            intro hzero
            exact hz (congrArg Subtype.val hzero))
        have hfmem : ∀ i : {i : J // i ∈ t}, (fU i : F) ∈ W i.1 := by
          intro i
          have hi : i.1 = a := Finset.mem_singleton.mp i.2
          simpa [hi, fU] using hzmem
        have hcplt : Fintype.card {i : J // i ∉ t} < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := a) (by simp [t])
        have hQ : ∀ s : Finset {i : J // i ∉ t},
            s.card ≤ finrank K (subspacesSum (fun i : {i : J // i ∉ t} =>
              (W i.1).map U.mkQ) s) := by
          intro s
          by_cases hs : s = ∅
          · simp [hs]
          let r : Finset J := s.image Subtype.val
          have hrne : r.Nonempty := by simpa [r] using Finset.nonempty_iff_ne_empty.mpr hs
          have ha : a ∉ r := by
            intro ha
            obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp ha
            exact j.2 (by simp [t, heq])
          have hrproper : r ≠ Finset.univ := by
            intro hruniv
            exact ha (by simp [hruniv])
          have hr_card : r.card = s.card :=
            Finset.card_image_of_injective _ Subtype.val_injective
          have hneq : finrank K (subspacesSum W r) ≠ r.card := by
            intro heq
            exact htight ⟨r, hrne, hrproper, heq⟩
          have hstrict : s.card + 1 ≤ finrank K (subspacesSum W r) := by
            have h := hW r
            rw [hr_card] at h hneq
            omega
          have hdim := finrank_le_finrank_map_quotient_add
            (K := K) U (subspacesSum W r)
          rw [show finrank K U = 1 from finrank_span_singleton hz] at hdim
          have hout : s.card ≤ finrank K ((subspacesSum W r).map U.mkQ) := by omega
          rw [subspacesSum_map, subspacesSum_subtype]
          exact hout
        obtain ⟨gq, hgqmem, hgq⟩ := ih _ hcplt {i : J // i ∉ t} (F ⧸ U)
          (fun i => (W i.1).map U.mkQ) rfl hQ
        exact representatives_glue W t U fU hfU hfmem gq hgq hgqmem
  exact hP (Fintype.card ι) ι E V rfl hHall

end ESCtoFroberg
