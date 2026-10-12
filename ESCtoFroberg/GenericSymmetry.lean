module

public import ESCtoFroberg.GenericSyzygyTransport
public import ESCtoFroberg.SingleBlockSupport
public import ESCtoFroberg.EvaluationRows

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
namespace ESCtoFroberg
open Module MvPolynomial

variable (K : Type*) [Field K] (m p d r : ℕ)

local instance genericScalarField : Field (GenericPointField K m p) := inferInstance

abbrev genericDegreePiece :=
  pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d

/-- An arbitrary basis of the actual generic point-degree kernel. -/
abbrev genericBasisFamily (b : Basis (Fin r) (GenericPointField K m p)
    (genericDegreePiece K m p d)) := basisFormFamily (genericDegreePiece K m p d) b

/-- The action of a point permutation on syzygies includes the induced change
of generator coordinates in the arbitrary chosen basis. -/
def genericSyzygyPermutation (b : Basis (Fin r) (GenericPointField K m p)
    (genericDegreePiece K m p d)) (σ : Equiv.Perm (Fin p)) (e : ℕ) :
    (Froberg.prefixMultiplication (genericBasisFamily K m p d r b) e).ker ≃+
      (Froberg.prefixMultiplication (genericBasisFamily K m p d r b) e).ker :=
  tensorSyzygyAddEquiv (genericDegreePiece K m p d) b
    (pointPermutationFieldEquiv K m p σ) (genericPointKernelAddEquiv K m p d σ)
    (genericPointKernelAddEquiv_smul K m p d σ)
    (genericPointKernelAddEquiv_apply K m p d σ) e

/-- The same generator change acts on each evaluated coefficient block. -/
def genericBlockPermutation (b : Basis (Fin r) (GenericPointField K m p)
    (genericDegreePiece K m p d)) (σ : Equiv.Perm (Fin p)) :
    (Fin r → GenericPointField K m p) ≃+ (Fin r → GenericPointField K m p) :=
  tensorTransportEquiv (R := GenericPointField K m p)
    (V := genericDegreePiece K m p d) b (pointPermutationFieldEquiv K m p σ)
    (genericPointKernelAddEquiv K m p d σ) (genericPointKernelAddEquiv_smul K m p d σ)
    (pointPermutationFieldEquiv K m p σ).toAddEquiv (fun a c => (pointPermutationFieldEquiv K m p σ).map_mul a c)

theorem genericBlockPermutation_smul
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d))
    (σ : Equiv.Perm (Fin p)) (a : GenericPointField K m p)
    (w : Fin r → GenericPointField K m p) :
    genericBlockPermutation K m p d r b σ (a • w) =
      pointPermutationFieldEquiv K m p σ a • genericBlockPermutation K m p d r b σ w := by
  ext j
  change (∑ i, b.repr (genericPointKernelAddEquiv K m p d σ (b i)) j *
    pointPermutationFieldEquiv K m p σ (a * w i)) =
    pointPermutationFieldEquiv K m p σ a *
      ∑ i, b.repr (genericPointKernelAddEquiv K m p d σ (b i)) j *
        pointPermutationFieldEquiv K m p σ (w i)
  simp only [map_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Literal evaluation intertwines the rational-coordinate permutation and
basis transition, even though the chosen generator basis need not be equivariant. -/
theorem genericSyzygyBlock_intertwine
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d))
    (σ : Equiv.Perm (Fin p)) (e : ℕ)
    (z : (Froberg.prefixMultiplication (genericBasisFamily K m p d r b) e).ker)
    (j : Fin p) :
    Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
      (genericBasisFamily K m p d r b) e (σ j)
      (genericSyzygyPermutation K m p d r b σ e z) =
    genericBlockPermutation K m p d r b σ
      (Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
        (genericBasisFamily K m p d r b) e j z) := by
  ext k
  change eval (chartPoint _ (genericPointCoordinates K m p) (σ j))
      ((tensorTransport (R := GenericPointField K m p)
        (V := genericDegreePiece K m p d) b (genericPointKernelAddEquiv K m p d σ)
        (coefficientFormsAddEquiv (pointPermutationFieldEquiv K m p σ) (m+1) e) z.val k).val) = _
  simp only [tensorTransport_apply, Submodule.coe_sum, Submodule.coe_smul]
  change eval (chartPoint _ (genericPointCoordinates K m p) (σ j))
    (∑ i, b.repr (genericPointKernelAddEquiv K m p d σ (b i)) k •
      (coefficientFormsAddEquiv (pointPermutationFieldEquiv K m p σ) (m+1) e (z.val i)).val) =
    ∑ i, b.repr (genericPointKernelAddEquiv K m p d σ (b i)) k *
      pointPermutationFieldEquiv K m p σ
        (eval (chartPoint _ (genericPointCoordinates K m p) j) (z.val i).val)
  simp only [MvPolynomial.smul_eq_C_mul, map_sum, map_mul, eval_C,
    coefficientFormsAddEquiv_apply, eval_pointPermutationFormsEquiv]

/-- For actual syzygy coefficient evaluations at the universal generic points,
all subset projection ranks depend only on the number of selected points. -/
theorem genericSyzygyProjectionRanks
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d))
    (e : ℕ) (S T : Finset (Fin p)) (hST : S.card = T.card) :
    finrank (GenericPointField K m p)
      (LinearMap.pi (fun i : S => Deformation.syzygyBlockEvaluation
        (genericPointCoordinates K m p) (genericBasisFamily K m p d r b) e i.val)).range =
    finrank (GenericPointField K m p)
      (LinearMap.pi (fun i : T => Deformation.syzygyBlockEvaluation
        (genericPointCoordinates K m p) (genericBasisFamily K m p d r b) e i.val)).range := by
  apply blockProjectionRank_cardinality (R := GenericPointField K m p)
    (H := (Froberg.prefixMultiplication (genericBasisFamily K m p d r b) e).ker)
    (W := Fin r → GenericPointField K m p) (ι := Fin p)
    (Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
      (genericBasisFamily K m p d r b) e) ?_ S T hST
  intro σ
  exact ⟨pointPermutationFieldEquiv K m p σ, genericSyzygyPermutation K m p d r b σ e,
    genericBlockPermutation K m p d r b σ, genericBlockPermutation_smul K m p d r b σ,
    fun i z => genericSyzygyBlock_intertwine K m p d r b σ e z i⟩

/-- The dimensions of all singly supported image subspaces are equal. -/
theorem genericSyzygySingleSupportRanks
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d))
    (e : ℕ) (i j : Fin p) :
    finrank (GenericPointField K m p) (singleBlockSupportSpace (R := GenericPointField K m p)
      (H := (Froberg.prefixMultiplication (genericBasisFamily K m p d r b) e).ker)
      (W := Fin r → GenericPointField K m p)
      (Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
        (genericBasisFamily K m p d r b) e) i) =
    finrank (GenericPointField K m p) (singleBlockSupportSpace (R := GenericPointField K m p)
      (H := (Froberg.prefixMultiplication (genericBasisFamily K m p d r b) e).ker)
      (W := Fin r → GenericPointField K m p)
      (Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
        (genericBasisFamily K m p d r b) e) j) :=
  singleBlockSupport_finrank_eq (R := GenericPointField K m p)
    (H := (Froberg.prefixMultiplication (genericBasisFamily K m p d r b) e).ker)
    (W := Fin r → GenericPointField K m p) (ι := Fin p)
    (Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
      (genericBasisFamily K m p d r b) e) (genericSyzygyProjectionRanks K m p d r b e) i j

/-- Lemma 4.2's symmetry conclusion: below the number of points, the generic
syzygy evaluation image contains no nonzero vector supported at one point. -/
theorem genericSyzygyNoSingleSupport
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d))
    (e : ℕ)
    (hτ : finrank (GenericPointField K m p) (LinearMap.pi
      (Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
        (genericBasisFamily K m p d r b) e)).range < p)
    (i : Fin p) : singleBlockSupportSpace (R := GenericPointField K m p)
      (H := (Froberg.prefixMultiplication (genericBasisFamily K m p d r b) e).ker)
      (W := Fin r → GenericPointField K m p)
      (Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
        (genericBasisFamily K m p d r b) e) i = ⊥ :=
  singleBlockSupport_eq_bot_of_rank_lt (R := GenericPointField K m p)
    (H := (Froberg.prefixMultiplication (genericBasisFamily K m p d r b) e).ker)
    (W := Fin r → GenericPointField K m p) (ι := Fin p)
    (Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
      (genericBasisFamily K m p d r b) e) (genericSyzygyProjectionRanks K m p d r b e)
    (by simpa using hτ) i

end ESCtoFroberg
