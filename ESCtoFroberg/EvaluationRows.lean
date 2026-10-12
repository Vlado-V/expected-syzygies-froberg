module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic
public import ESCtoFroberg.LinearTransversal

@[expose] public section

namespace ESCtoFroberg

/-- A monotone concave integer rank sequence cannot have a zero increment and then increase. -/
theorem concaveRank_plateau {p : ℕ} (f : ℕ → ℕ)
    (hmono : ∀ {a b}, a ≤ b → b ≤ p → f a ≤ f b)
    (hconc : ∀ j, 0 < j → j < p → f (j - 1) + f (j + 1) ≤ 2 * f j)
    {k : ℕ} (hk : k + 1 ≤ p) (heq : f (k + 1) = f k) : f p = f k := by
  have hconstant : ∀ n, k ≤ n → n ≤ p → f n = f k := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hkn hnp
      by_cases hn : n ≤ k + 1
      · have hlo := hmono hkn hnp
        have hhi := hmono hn hk
        omega
      · have hm : k ≤ n - 1 := by omega
        have hm2 : k ≤ n - 2 := by omega
        have e1 := ih (n - 1) (by omega) hm (by omega)
        have e2 := ih (n - 2) (by omega) hm2 (by omega)
        have hc := hconc (n - 1) (by omega) (by omega)
        have hn1 : n - 1 + 1 = n := by omega
        have hn2 : n - 1 - 1 = n - 2 := by omega
        rw [hn1, hn2, e1, e2] at hc
        have hlo := hmono hkn hnp
        omega
  exact hconstant p (by omega) le_rfl

/-- The cardinality bound for a monotone concave sequence of nonnegative integer ranks. -/
theorem concaveRank_lowerBound {p : ℕ} (f : ℕ → ℕ) (hz : f 0 = 0)
    (hmono : ∀ {a b}, a ≤ b → b ≤ p → f a ≤ f b)
    (hconc : ∀ j, 0 < j → j < p → f (j - 1) + f (j + 1) ≤ 2 * f j)
    {j : ℕ} (hj : j ≤ p) : min j (f p) ≤ f j := by
  have hgrowth : ∀ j, j ≤ p → f j < f p → j ≤ f j := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      intro hj hlt
      have hle := hmono (show j ≤ j + 1 by omega) hj
      have hprev : f j < f p := by omega
      have hbound := ih (by omega) hprev
      by_cases heq : f (j + 1) = f j
      · have hend := concaveRank_plateau f hmono hconc hj heq
        omega
      · omega
  by_cases hlt : f j < f p
  · exact (min_le_left _ _).trans (hgrowth j hj hlt)
  · exact (min_le_right _ _).trans (by omega)

/-- The sum of the selected block row spaces. -/
def rowSum {K E ι : Type*} [Field K] [AddCommGroup E] [Module K E]
    (V : ι → Submodule K E) (S : Finset ι) : Submodule K E := S.sup V

lemma rowSum_mono {K E ι : Type*} [Field K] [AddCommGroup E] [Module K E]
    (V : ι → Submodule K E) {S T : Finset ι} (h : S ⊆ T) :
    rowSum V S ≤ rowSum V T := Finset.sup_mono h

/-- Generic symmetry of block ranks forces every subset to have rank at least the
minimum of its cardinality and the total rank. -/
theorem symmetricRowRanks_lowerBound {K E ι : Type*} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] [Fintype ι] [DecidableEq ι]
    (V : ι → Submodule K E) (f : ℕ → ℕ)
    (hdim : ∀ S : Finset ι, Module.finrank K (rowSum V S) = f S.card)
    (S : Finset ι) :
    min S.card (Module.finrank K (rowSum V Finset.univ)) ≤
      Module.finrank K (rowSum V S) := by
  have hz : f 0 = 0 := by
    have hh := (hdim ∅).symm
    rw [Finset.card_empty] at hh
    change f 0 = Module.finrank K ↥((∅ : Finset ι).sup V) at hh
    rw [Finset.sup_empty, finrank_bot] at hh
    exact hh
  have hmono : ∀ {a b}, a ≤ b → b ≤ Fintype.card ι → f a ≤ f b := by
    intro a b hab hbp
    obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset ι)) (by simpa using hbp)
    obtain ⟨R, hRT, hR⟩ := Finset.exists_subset_card_eq (s := T) (n := a) (by omega)
    have hm := Submodule.finrank_mono (rowSum_mono V hRT)
    rw [hdim R, hdim T, hR, hT] at hm
    exact hm
  have hconc : ∀ j, 0 < j → j < Fintype.card ι →
      f (j - 1) + f (j + 1) ≤ 2 * f j := by
    intro j hj hjp
    obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset ι)) (show j - 1 ≤ Finset.univ.card by
        simp only [Finset.card_univ]; omega)
    obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := T) (t := Finset.univ) (by simp only [Finset.card_univ]; omega)
    have hTa : (insert a T).card = j := by simp [ha, hT]; omega
    obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := insert a T) (t := Finset.univ) (by simp only [Finset.card_univ]; omega)
    have hba : b ≠ a := by intro h; subst b; exact hb (Finset.mem_insert_self _ _)
    have hbT : b ∉ T := by exact fun h => hb (Finset.mem_insert_of_mem h)
    have hTb : (insert b T).card = j := by simp [hbT, hT]; omega
    have hU : (insert a T ∪ insert b T).card = j + 1 := by
      rw [Finset.insert_union, Finset.union_insert, Finset.union_self]
      simp only [Finset.card_insert_of_notMem (show a ∉ insert b T by simp [ha, Ne.symm hba]),
        Finset.card_insert_of_notMem hbT, hT]
      omega
    have hI : insert a T ∩ insert b T = T := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨ha' | hx, hb' | hy⟩
        · exact False.elim (hba (hb'.symm.trans ha'))
        · exact hy
        · exact hx
        · exact hx
      · intro hx; exact ⟨Or.inr hx, Or.inr hx⟩
    have hsup : rowSum V (insert a T ∪ insert b T) =
        rowSum V (insert a T) ⊔ rowSum V (insert b T) := by
      simp only [rowSum, Finset.sup_union]
    have hinf : rowSum V (insert a T ∩ insert b T) ≤
        rowSum V (insert a T) ⊓ rowSum V (insert b T) :=
      le_inf (rowSum_mono V Finset.inter_subset_left)
        (rowSum_mono V Finset.inter_subset_right)
    have hsub : Module.finrank K (rowSum V (insert a T ∪ insert b T)) +
        Module.finrank K (rowSum V (insert a T ∩ insert b T)) ≤
        Module.finrank K (rowSum V (insert a T)) +
        Module.finrank K (rowSum V (insert b T)) := by
      rw [hsup]
      exact (Nat.add_le_add_left (Submodule.finrank_mono hinf) _).trans_eq
        (Submodule.finrank_sup_add_finrank_inf_eq _ _)
    rw [hdim _, hdim _, hdim _, hdim _, hU, hI, hT, hTa, hTb] at hsub
    omega
  rw [hdim S, hdim Finset.univ, Finset.card_univ]
  exact concaveRank_lowerBound f hz hmono hconc (Finset.card_le_univ S)

/-- Rank symmetry formulated directly, without choosing a numerical rank sequence. -/
theorem symmetricRowRanks_lowerBound_of_symmetry {K E ι : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Fintype ι] [DecidableEq ι]
    (V : ι → Submodule K E)
    (hsym : ∀ S T : Finset ι, S.card = T.card →
      Module.finrank K (rowSum V S) = Module.finrank K (rowSum V T))
    (S : Finset ι) :
    min S.card (Module.finrank K (rowSum V Finset.univ)) ≤
      Module.finrank K (rowSum V S) := by
  classical
  let pick (j : ℕ) (hj : j ≤ Fintype.card ι) : Finset ι :=
    Classical.choose (Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset ι)) (n := j) (by simpa using hj))
  have hpick (j : ℕ) (hj : j ≤ Fintype.card ι) : (pick j hj).card = j :=
    (Classical.choose_spec (Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset ι)) (n := j) (by simpa using hj))).2
  let f (j : ℕ) := if hj : j ≤ Fintype.card ι then
    Module.finrank K (rowSum V (pick j hj)) else 0
  have hdim (T : Finset ι) : Module.finrank K (rowSum V T) = f T.card := by
    dsimp only [f]
    rw [dite_eq_left (Finset.card_le_univ T)]
    exact hsym T _ (hpick T.card (Finset.card_le_univ T)).symm
  exact symmetricRowRanks_lowerBound V f hdim S

/-- Independent scalar rows give a surjection onto their scalar coordinate space. -/
theorem independentRows_surjective {K H β : Type*} [Field K] [AddCommGroup H]
    [Module K H] [Finite β] (w : β → Module.Dual K H)
    (hw : LinearIndependent K w) : Function.Surjective (LinearMap.pi w) := by
  let toFunc : Module.Dual K H →ₗ[K] (H → K) :=
    { toFun := fun l => l
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hw' : LinearIndependent K (fun i x => w i x) :=
    hw.map' toFunc (LinearMap.ker_eq_bot.mpr DFunLike.coe_injective)
  have htop := (span_flip_eq_top_iff_linearIndependent (f := fun i x => w i x)).mpr hw'
  change Submodule.span K (Set.range (LinearMap.pi w)) = ⊤ at htop
  rw [← LinearMap.coe_range, Submodule.span_eq] at htop
  exact LinearMap.range_eq_top.mp htop

/-- Independent representatives can be chosen on any distinct collection of block labels. -/
theorem independentRepresentatives_of_symmetricRanks {K E ι β : Type*} [Field K]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Fintype ι] [Fintype β]
    [DecidableEq ι] [DecidableEq β] (V : ι → Submodule K E)
    (hsym : ∀ S T : Finset ι, S.card = T.card →
      Module.finrank K (rowSum V S) = Module.finrank K (rowSum V T))
    (labels : β → ι) (hinj : Function.Injective labels)
    (hb : Fintype.card β ≤ Module.finrank K (rowSum V Finset.univ)) :
    ∃ x : β → E, (∀ i, x i ∈ V (labels i)) ∧ LinearIndependent K x := by
  have hHall (s : Finset β) : s.card ≤ Module.finrank K
      (subspacesSum (fun i => V (labels i)) s) := by
    have hcard : (s.image labels).card = s.card := Finset.card_image_of_injective s hinj
    have hbound := symmetricRowRanks_lowerBound_of_symmetry V hsym (s.image labels)
    have hs : s.card ≤ Module.finrank K (rowSum V Finset.univ) :=
      (Finset.card_le_univ s).trans hb
    rw [hcard, min_eq_left hs] at hbound
    have heq : rowSum V (s.image labels) = subspacesSum (fun i => V (labels i)) s := by
      rw [rowSum, Finset.sup_image]
      exact Finset.sup_eq_iSup _ _
    rw [heq] at hbound
    exact hbound
  exact exists_linearIndependent_representatives (fun i => V (labels i)) hHall

/-- Abstract pullbacks of scalar block functionals, in the form used by evaluation. -/
theorem independentPullbacks_of_symmetricRanks {K D E ι β : Type*} [Field K]
    [AddCommGroup D] [Module K D] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] [Fintype ι] [Fintype β] [DecidableEq ι] [DecidableEq β]
    (pullback : ι → D →ₗ[K] E)
    (hsym : ∀ S T : Finset ι, S.card = T.card →
      Module.finrank K (rowSum (fun i => (pullback i).range) S) =
      Module.finrank K (rowSum (fun i => (pullback i).range) T))
    (labels : β → ι) (hinj : Function.Injective labels)
    (hb : Fintype.card β ≤ Module.finrank K
      (rowSum (fun i => (pullback i).range) Finset.univ)) :
    ∃ functional : β → D,
      LinearIndependent K (fun i => pullback (labels i) (functional i)) := by
  obtain ⟨x, hx, hli⟩ := independentRepresentatives_of_symmetricRanks
    (fun i => (pullback i).range) hsym labels hinj hb
  have hex : ∀ i, ∃ d, pullback (labels i) d = x i := fun i =>
    LinearMap.mem_range.mp (hx i)
  choose functional heq using hex
  refine ⟨functional, ?_⟩
  simpa only [heq] using hli

/-- Every functional on a finite scalar block is a weighted sum of its coordinates. -/
theorem blockFunctional_eq_weightedRows {K H α : Type*} [Field K] [AddCommGroup H]
    [Module K H] [Fintype α] [DecidableEq α] (block : H →ₗ[K] (α → K))
    (functional : Module.Dual K (α → K)) :
    block.dualMap functional =
      ∑ i, functional (Pi.single i 1) • ((LinearMap.proj i).comp block) := by
  ext x
  change functional (block x) = _
  rw [pi_eq_sum_univ' (block x), map_sum]
  simp only [map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- Lemma 3.1: independent scalar evaluation rows can be chosen on any prescribed distinct
blocks, up to the minimum of the number of blocks and the total evaluation rank. -/
theorem independentEvaluationRows {K H α ι β : Type*} [Field K] [AddCommGroup H]
    [Module K H] [FiniteDimensional K H] [Fintype α] [Fintype ι] [Fintype β]
    [DecidableEq α] [DecidableEq ι] [DecidableEq β]
    (blocks : ι → H →ₗ[K] (α → K))
    (hsym : ∀ S T : Finset ι, S.card = T.card →
      Module.finrank K (rowSum (fun i => (blocks i).dualMap.range) S) =
      Module.finrank K (rowSum (fun i => (blocks i).dualMap.range) T))
    (labels : β → ι) (hinj : Function.Injective labels)
    (hb : Fintype.card β ≤ Module.finrank K
      (rowSum (fun i => (blocks i).dualMap.range) Finset.univ)) :
    ∃ weights : β → α → K, LinearIndependent K
      (fun j => ∑ i, weights j i • ((LinearMap.proj i).comp (blocks (labels j)))) := by
  obtain ⟨functional, hli⟩ := independentPullbacks_of_symmetricRanks
    (fun i => (blocks i).dualMap) hsym labels hinj hb
  refine ⟨fun j i => functional j (Pi.single i 1), ?_⟩
  simpa only [blockFunctional_eq_weightedRows] using hli

/-- The combined row space is the dual image of projection onto the selected blocks. -/
theorem rowSum_dualBlocks {K H D ι : Type*} [Field K] [AddCommGroup H]
    [Module K H] [AddCommGroup D] [Module K D] [DecidableEq ι]
    (blocks : ι → H →ₗ[K] D) (S : Finset ι) :
    rowSum (fun i => (blocks i).dualMap.range) S =
      (LinearMap.pi (fun i : S => blocks i.1)).dualMap.range := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, LinearMap.ker_pi,
    Subspace.dualAnnihilator_iInf_eq]
  simp only [← LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    rowSum, Finset.sup_eq_iSup, iSup_subtype]

/-- Row dimension agrees with the rank of the block projection. -/
theorem finrank_rowSum_dualBlocks {K H D ι : Type*} [Field K] [AddCommGroup H]
    [Module K H] [AddCommGroup D] [Module K D] [DecidableEq ι]
    (blocks : ι → H →ₗ[K] D) (S : Finset ι) :
    Module.finrank K (rowSum (fun i => (blocks i).dualMap.range) S) =
      Module.finrank K (LinearMap.pi (fun i : S => blocks i.1)).range := by
  rw [rowSum_dualBlocks, LinearMap.finrank_range_dualMap_eq_finrank_range]

/-- The total row dimension is the rank of the full evaluation map. -/
theorem finrank_totalRows {K H D ι : Type*} [Field K] [AddCommGroup H]
    [Module K H] [AddCommGroup D] [Module K D] [Fintype ι] [DecidableEq ι]
    (blocks : ι → H →ₗ[K] D) :
    Module.finrank K (rowSum (fun i => (blocks i).dualMap.range) Finset.univ) =
      Module.finrank K (LinearMap.pi blocks).range := by
  have heq : rowSum (fun i => (blocks i).dualMap.range) Finset.univ =
      (LinearMap.pi blocks).dualMap.range := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker, LinearMap.ker_pi,
      Subspace.dualAnnihilator_iInf_eq]
    simp [rowSum, Finset.sup_eq_iSup, LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  rw [heq, LinearMap.finrank_range_dualMap_eq_finrank_range]

/-- The evaluation-row lemma stated using the ranks of the actual block projections. -/
theorem independentEvaluationRows_of_projectionRanks {K H α ι β : Type*} [Field K]
    [AddCommGroup H] [Module K H] [FiniteDimensional K H] [Fintype α]
    [Fintype ι] [Fintype β] [DecidableEq α] [DecidableEq ι] [DecidableEq β]
    (blocks : ι → H →ₗ[K] (α → K))
    (hsym : ∀ S T : Finset ι, S.card = T.card →
      Module.finrank K (LinearMap.pi (fun i : S => blocks i.1)).range =
      Module.finrank K (LinearMap.pi (fun i : T => blocks i.1)).range)
    (labels : β → ι) (hinj : Function.Injective labels)
    (hb : Fintype.card β ≤ Module.finrank K (LinearMap.pi blocks).range) :
    ∃ weights : β → α → K, LinearIndependent K
      (fun j => ∑ i, weights j i • ((LinearMap.proj i).comp (blocks (labels j)))) := by
  apply independentEvaluationRows blocks ?_ labels hinj ?_
  · intro S T hcard
    simpa only [finrank_rowSum_dualBlocks] using hsym S T hcard
  · simpa only [finrank_totalRows] using hb

end ESCtoFroberg
