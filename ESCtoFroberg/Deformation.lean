module

public import ESCtoFroberg.FirstOrderRank
public import ESCtoFroberg.Interpolation
public import ESCtoFroberg.EvaluationRows
public import ESCtoFroberg.SyzygyEvaluation

@[expose] public section

/-! # Deforming point equations by independent evaluation rows

Independent scalar rows at distinct marked points can be prescribed as the
values of actual homogeneous perturbations.  Their rank is the first-order
rank of the multiplication pencil, and therefore lowers its actual quotient
Hilbert function by the number of chosen rows.
-/

noncomputable section

namespace ESCtoFroberg.Deformation

set_option backward.isDefEq.respectTransparency false

open Module MvPolynomial

variable {K : Type*} [Field K] {m p d e r b : ℕ}

/-- Place scalar coordinates at selected point labels and put zero elsewhere. -/
def selectedEmbedding (σ : Fin b → Fin p) : (Fin b → K) →ₗ[K] (Fin p → K) :=
  ∑ k, (LinearMap.single K (fun _ : Fin p => K) (σ k)).comp (LinearMap.proj k)

@[simp] theorem selectedEmbedding_apply (σ : Fin b → Fin p) (x : Fin b → K)
    (j : Fin p) :
    selectedEmbedding (K := K) σ x j = ∑ k, if σ k = j then x k else 0 := by
  classical
  simp [selectedEmbedding, Pi.single_apply, eq_comm]

theorem selectedEmbedding_selected (σ : Fin b → Fin p) (hσ : Function.Injective σ)
    (x : Fin b → K) (k : Fin b) : selectedEmbedding σ x (σ k) = x k := by
  classical
  rw [selectedEmbedding_apply]
  simp only [hσ.eq_iff]
  simp

theorem selectedEmbedding_injective (σ : Fin b → Fin p) (hσ : Function.Injective σ) :
    Function.Injective (selectedEmbedding (K := K) σ) := by
  intro x y h
  ext k
  simpa only [selectedEmbedding_selected σ hσ] using congrFun h (σ k)

theorem selectedEmbedding_comp_rank {Z : Type*} [AddCommGroup Z] [Module K Z]
    (σ : Fin b → Fin p) (hσ : Function.Injective σ) (f : Z →ₗ[K] (Fin b → K))
    (hf : Function.Surjective f) : finrank K ((selectedEmbedding σ).comp f).range = b := by
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hf, Submodule.map_top,
    LinearMap.finrank_range_of_inj (selectedEmbedding_injective σ hσ),
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

theorem selectedEmbedding_response_rank {Z : Type*} [AddCommGroup Z] [Module K Z]
    (σ : Fin b → Fin p) (hσ : Function.Injective σ) (R : Z →ₗ[K] (Fin p → K))
    (rows : Fin b → Module.Dual K Z) (hrows : LinearIndependent K rows)
    (hR : R = (selectedEmbedding σ).comp (LinearMap.pi rows)) :
    finrank K R.range = b := by
  rw [hR]
  exact selectedEmbedding_comp_rank σ hσ (LinearMap.pi rows)
    (independentRows_surjective rows hrows)

theorem pointEvaluation_prefixMultiplication (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m + 1) d) (x : Fin r → Forms K (m + 1) e)
    (j : Fin p) :
    pointEvaluation K a (d + e) (Froberg.prefixMultiplication q e x) j =
      ∑ i, pointEvaluation K a d (q i) j * pointEvaluation K a e (x i) j := by
  simp [pointEvaluation_apply, Froberg.prefixMultiplication_val, map_mul]

theorem prefixMultiplication_add_smul (q δ : Fin r → Forms K (m + 1) d) (ε : K) :
    Froberg.prefixMultiplication (q + ε • δ) e =
      Froberg.prefixMultiplication q e + ε • Froberg.prefixMultiplication δ e := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [Froberg.prefixMultiplication_val, add_mul, Finset.sum_add_distrib,
    Finset.smul_sum]

/-- Prescribe actual perturbation equations from scalar weights at marked
points.  The entire first response factors through the selected scalar rows. -/
theorem exists_perturbation_with_response (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m + 1) d)
    (hsurj : Function.Surjective (pointEvaluation K a d))
    (σ : Fin b → Fin p) (w : Fin b → Fin r → K) :
    ∃ δ : Fin r → Forms K (m + 1) d,
      (∀ i, pointEvaluation K a d (δ i) = selectedEmbedding σ (fun k => w k i)) ∧
      FirstOrderRank.firstResponse (Froberg.prefixMultiplication q e)
        (Froberg.prefixMultiplication δ e) (pointEvaluation K a (d + e)) =
      (selectedEmbedding σ).comp (LinearMap.pi (fun k => evaluationRow a q e (σ k) (w k))) := by
  classical
  choose δ hδ using fun i : Fin r => hsurj (selectedEmbedding σ (fun k => w k i))
  refine ⟨δ, hδ, ?_⟩
  ext z j
  change pointEvaluation K a (d + e) (Froberg.prefixMultiplication δ e z.val) j = _
  rw [pointEvaluation_prefixMultiplication]
  simp only [hδ, LinearMap.comp_apply, selectedEmbedding_apply, LinearMap.pi_apply,
    evaluationRow_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hkj : σ k = j
  · simp only [hkj, ite_true]
  · simp only [hkj, ite_false, zero_mul, Finset.sum_const_zero]

/-- Independent rows in distinct blocks give an actual perturbation whose
first-order response has exactly their cardinality. -/
theorem exists_perturbation_response_rank (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m + 1) d)
    (hsurj : Function.Surjective (pointEvaluation K a d))
    (σ : Fin b → Fin p) (hσ : Function.Injective σ) (w : Fin b → Fin r → K)
    (hw : LinearIndependent K (fun k => evaluationRow a q e (σ k) (w k))) :
    ∃ δ : Fin r → Forms K (m + 1) d,
      finrank K (FirstOrderRank.firstResponse (Froberg.prefixMultiplication q e)
        (Froberg.prefixMultiplication δ e) (pointEvaluation K a (d + e))).range = b := by
  obtain ⟨δ, -, hδ⟩ := exists_perturbation_with_response (e := e) a q hsurj σ w
  refine ⟨δ, ?_⟩
  let Z := (Froberg.prefixMultiplication q e).ker
  let R : Z →ₗ[K] (Fin p → K) := FirstOrderRank.firstResponse
    (Froberg.prefixMultiplication q e) (Froberg.prefixMultiplication δ e)
    (pointEvaluation K a (d + e))
  let rows : Fin b → Module.Dual K Z := fun k => evaluationRow a q e (σ k) (w k)
  have hrows : LinearIndependent K rows := hw
  have hR : R = (selectedEmbedding σ).comp (LinearMap.pi rows) := hδ
  have hrank := selectedEmbedding_response_rank (K := K)
    (Z := Z) σ hσ R rows hrows hR
  exact hrank

/-- Concrete deformation of point equations: independent evaluation rows
reduce the actual degree-`d+e` quotient dimension from `p` to at most `p-b`. -/
theorem exists_deformation_hilbert_le [Infinite K] (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m + 1) d)
    (hsurj : Function.Surjective (pointEvaluation K a d))
    (himage : (Froberg.prefixMultiplication q e).range =
      (pointEvaluation K a (d + e)).ker)
    (σ : Fin b → Fin p) (hσ : Function.Injective σ) (w : Fin b → Fin r → K)
    (hw : LinearIndependent K (fun k => evaluationRow a q e (σ k) (w k))) :
    ∃ δ : Fin r → Forms K (m + 1) d, ∃ ε : K, ε ≠ 0 ∧
      Froberg.hilbertFunction (Froberg.familySpace (q + ε • δ)) (d + e) ≤ p - b := by
  obtain ⟨δ, hδ⟩ := exists_perturbation_response_rank a q hsurj σ hσ w hw
  have hπ : (pointEvaluation K a (d + e)).comp (Froberg.prefixMultiplication q e) = 0 := by
    rw [← LinearMap.range_le_ker_iff, himage]
  obtain ⟨ε, hε, hr⟩ := FirstOrderRank.rank_gain (Froberg.prefixMultiplication q e)
    (Froberg.prefixMultiplication δ e) (pointEvaluation K a (d + e)) hπ
  rw [hδ, ← prefixMultiplication_add_smul] at hr
  change finrank K (Froberg.prefixMultiplication q e).range + b ≤
    finrank K (Froberg.prefixMultiplication (q + ε • δ) e).range at hr
  have hp := (pointEvaluation K a (d + e)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (pointEvaluation_surjective_add a hsurj e),
    finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    himage.symm, finrank_forms] at hp
  have hF := Froberg.prefix_hilbert_add_rank (e := e) (show 0 < m + 1 by omega)
    (q + ε • δ)
  have hN : m + 1 + (d + e) - 1 = m + (d + e) := by omega
  rw [hN] at hF
  refine ⟨δ, ε, hε, ?_⟩
  have hsum : Froberg.hilbertFunction (Froberg.familySpace (q + ε • δ)) (d + e) + b ≤ p := by
    have htotal : Froberg.hilbertFunction (Froberg.familySpace (q + ε • δ)) (d + e) + b +
        finrank K (Froberg.prefixMultiplication q e).range ≤
          p + finrank K (Froberg.prefixMultiplication q e).range := by calc
      Froberg.hilbertFunction (Froberg.familySpace (q + ε • δ)) (d + e) + b +
          finrank K (Froberg.prefixMultiplication q e).range =
        Froberg.hilbertFunction (Froberg.familySpace (q + ε • δ)) (d + e) +
          (finrank K (Froberg.prefixMultiplication q e).range + b) := by omega
      _ ≤ Froberg.hilbertFunction (Froberg.familySpace (q + ε • δ)) (d + e) +
          finrank K (Froberg.prefixMultiplication (q + ε • δ) e).range :=
        Nat.add_le_add_left hr _
      _ = p + finrank K (Froberg.prefixMultiplication q e).range := hF.trans hp.symm
    exact Nat.le_of_add_le_add_right htotal
  exact Nat.le_sub_of_add_le hsum

end ESCtoFroberg.Deformation
