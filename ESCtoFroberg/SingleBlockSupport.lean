module

public import ESCtoFroberg.BlockSymmetry

@[expose] public section
noncomputable section
namespace ESCtoFroberg
open Module

variable {R H W ι : Type*} [Field R] [AddCommMonoid H] [Module R H]
  [AddCommGroup W] [Module R W] [Fintype ι] [DecidableEq ι]

/-- Projection of the full evaluation image onto selected point blocks. -/
def evaluationImageProjection (E : ι → H →ₗ[R] W) (S : Finset ι) :
    (LinearMap.pi E).range →ₗ[R] (S → W) :=
  LinearMap.pi (fun i => (LinearMap.proj i.val).comp (LinearMap.pi E).range.subtype)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem evaluationImageProjection_apply (E : ι → H →ₗ[R] W)
    (S : Finset ι) (y : (LinearMap.pi E).range) (i : S) :
    evaluationImageProjection E S y i = y.val i.val := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem range_evaluationImageProjection (E : ι → H →ₗ[R] W) (S : Finset ι) :
    (evaluationImageProjection E S).range =
      (LinearMap.pi (fun i : S => E i.val)).range := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨h, hh⟩ := x.property
    exact ⟨h, by ext i; change E i.val h = x.val i.val; exact congrFun hh i.val⟩
  · rintro ⟨h, rfl⟩
    exact ⟨⟨LinearMap.pi E h, ⟨h, rfl⟩⟩, rfl⟩

/-- Vectors in the evaluation image whose only potentially nonzero block is `i`. -/
def singleBlockSupportSpace (E : ι → H →ₗ[R] W) (i : ι) :
    Submodule R (LinearMap.pi E).range :=
  (evaluationImageProjection E (Finset.univ.erase i)).ker

@[simp] theorem mem_singleBlockSupportSpace (E : ι → H →ₗ[R] W)
    (i : ι) (y : (LinearMap.pi E).range) :
    y ∈ singleBlockSupportSpace E i ↔ ∀ j, j ≠ i → y.val j = 0 := by
  simp only [singleBlockSupportSpace, LinearMap.mem_ker, funext_iff,
    evaluationImageProjection_apply, Pi.zero_apply]
  constructor
  · intro h j hji
    exact h ⟨j, by simp [hji]⟩
  · intro h j
    exact h j.val (Finset.mem_erase.mp j.property).1

/-- Equal complement projection ranks imply equal singleton support dimensions. -/
theorem singleBlockSupport_finrank_eq [FiniteDimensional R W]
    (E : ι → H →ₗ[R] W)
    (hsym : ∀ S T : Finset ι, S.card = T.card →
      finrank R (LinearMap.pi (fun i : S => E i.val)).range =
        finrank R (LinearMap.pi (fun i : T => E i.val)).range)
    (i j : ι) :
    finrank R (singleBlockSupportSpace E i) = finrank R (singleBlockSupportSpace E j) := by
  have hdim (k : ι) := (evaluationImageProjection E (Finset.univ.erase k)).finrank_range_add_finrank_ker
  have heq := hsym (Finset.univ.erase i) (Finset.univ.erase j) (by simp)
  have hdi := hdim i
  have hdj := hdim j
  rw [range_evaluationImageProjection] at hdi hdj
  rw [heq] at hdi
  exact Nat.add_left_cancel (hdi.trans hdj.symm)

omit [DecidableEq ι] in
/-- Nonzero vectors confined to distinct blocks are linearly independent. -/
theorem linearIndependent_singleBlockVectors (v : ι → (ι → W))
    (hzero : ∀ i j, j ≠ i → v i j = 0)
    (hne : ∀ i, v i i ≠ 0) : LinearIndependent R v := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hi := congrFun hc i
  have heq : (∑ j, c j • v j) i = c i • v i i := by
    simp only [Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_single i
    · intro j _ hji
      rw [hzero j i (Ne.symm hji), smul_zero]
    · simp
  rw [heq] at hi
  exact (smul_eq_zero.mp hi).resolve_right (hne i)

/-- If the evaluation image has smaller dimension than the number of point
blocks, symmetry forces every singly supported vector to vanish. -/
theorem singleBlockSupport_eq_bot_of_rank_lt [FiniteDimensional R W]
    (E : ι → H →ₗ[R] W)
    (hsym : ∀ S T : Finset ι, S.card = T.card →
      finrank R (LinearMap.pi (fun i : S => E i.val)).range =
        finrank R (LinearMap.pi (fun i : T => E i.val)).range)
    (hrank : finrank R (LinearMap.pi E).range < Fintype.card ι)
    (i : ι) : singleBlockSupportSpace E i = ⊥ := by
  classical
  by_contra hbot
  have hpos : 0 < finrank R (singleBlockSupportSpace E i) := by
    exact Nat.pos_of_ne_zero (fun hz => hbot (Submodule.finrank_eq_zero.mp hz))
  have hex (j : ι) : ∃ y : singleBlockSupportSpace E j, y ≠ 0 := by
    apply (Module.finrank_pos_iff_exists_ne_zero (R := R) (M := ↥(singleBlockSupportSpace E j))).mp
    rw [← singleBlockSupport_finrank_eq E hsym i j]
    exact hpos
  choose v hv using hex
  let y : ι → (LinearMap.pi E).range := fun j => (v j).val
  have hzero (j k : ι) (hkj : k ≠ j) : (y j).val k = 0 :=
    (mem_singleBlockSupportSpace E j (y j)).mp (v j).property k hkj
  have hne (j : ι) : (y j).val j ≠ 0 := by
    intro hz
    apply hv j
    apply Subtype.ext
    apply Subtype.ext
    ext k
    by_cases hk : k = j
    · subst k; exact hz
    · exact hzero j k hk
  have hli : LinearIndependent R y :=
    LinearIndependent.of_comp (LinearMap.pi E).range.subtype
      (linearIndependent_singleBlockVectors (fun j => (y j).val) hzero hne)
  have hbound := hli.fintype_card_le_finrank
  omega

end ESCtoFroberg
