module

public import ESCtoFroberg.GenericSymmetry
public import ESCtoFroberg.MultiplicationBridge

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace ESCtoFroberg
open Module MvPolynomial

variable (K : Type*) [Field K] (m p d r : ℕ)

/-- The generic endpoint evaluation image has no nonzero vector concentrated
at one marked point whenever its dimension is smaller than the point count. -/
theorem genericNoSinglePointSupport
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d))
    (hτ : finrank (GenericPointField K m p)
      (endpointEvaluationImage (genericBasisFamily K m p d r b)
        (fun j => chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) j)) < p) :
    NoSinglePointSupport (genericBasisFamily K m p d r b)
      (fun j => chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) j) := by
  classical
  have hτ' : finrank (GenericPointField K m p) (LinearMap.pi
      (Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
        (genericBasisFamily K m p d r b) d)).range < p := by
    change finrank (GenericPointField K m p)
      (Deformation.syzygyEvaluation (genericPointCoordinates K m p)
        (genericBasisFamily K m p d r b) d).range < p
    rw [← endpointEvaluationImage_finrank_eq_prefix (genericPointCoordinates K m p)
      (genericBasisFamily K m p d r b)]
    exact hτ
  intro i v hv hzero
  have hv' : v ∈ (LinearMap.pi
      (Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
        (genericBasisFamily K m p d r b) d)).range := by
    simpa only [endpointEvaluationImage_eq_prefix, Deformation.syzygyEvaluation] using hv
  let y : (LinearMap.pi
      (Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
        (genericBasisFamily K m p d r b) d)).range := ⟨v, hv'⟩
  have hy : y ∈ singleBlockSupportSpace
      (Deformation.syzygyBlockEvaluation (genericPointCoordinates K m p)
        (genericBasisFamily K m p d r b) d) i := by
    apply (mem_singleBlockSupportSpace _ i y).mpr
    intro j hji
    funext k
    exact hzero j hji k
  rw [genericSyzygyNoSingleSupport K m p d r b d hτ' i, Submodule.mem_bot] at hy
  exact congrArg Subtype.val hy

end ESCtoFroberg
