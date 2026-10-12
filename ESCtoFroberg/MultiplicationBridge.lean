module

public import ESCtoFroberg.EndpointCriterion
public import ESCtoFroberg.BeforeEndpoint

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open Froberg Module MvPolynomial

variable {K : Type*} [Field K] {m p d r : ℕ}

/-- The two multiplication conventions describe precisely the same endpoint syzygies. -/
theorem endpointMultiplication_zero_iff_prefix
    (q : Fin r → Forms K (m+1) d) (a : Fin r → Forms K (m+1) d) :
    endpointMultiplication q a = 0 ↔ prefixMultiplication q d a = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    simpa [endpointMultiplication_val, prefixMultiplication_val] using hv
  · intro h
    apply Subtype.ext
    have hv := congrArg Subtype.val h
    simpa [endpointMultiplication_val, prefixMultiplication_val] using hv

theorem endpointMultiplication_ker_eq_prefix
    (q : Fin r → Forms K (m+1) d) :
    (endpointMultiplication q).ker = (prefixMultiplication q d).ker := by
  ext a
  exact endpointMultiplication_zero_iff_prefix q a

/-- Evaluation images are identical under the two endpoint target degree conventions. -/
theorem endpointEvaluationImage_eq_prefix
    (a : PointCoordinates K m p) (q : Fin r → Forms K (m+1) d) :
    endpointEvaluationImage q (fun j => chartPoint K a j) =
      (Deformation.syzygyEvaluation a q d).range := by
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z.val, (endpointMultiplication_zero_iff_prefix q z.val).mp z.property⟩, ?_⟩
    rfl
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z.val, (endpointMultiplication_zero_iff_prefix q z.val).mpr z.property⟩, ?_⟩
    rfl

theorem endpointEvaluationImage_finrank_eq_prefix
    (a : PointCoordinates K m p) (q : Fin r → Forms K (m+1) d) :
    finrank K (endpointEvaluationImage q (fun j => chartPoint K a j)) =
      finrank K (Deformation.syzygyEvaluation a q d).range := by
  rw [endpointEvaluationImage_eq_prefix]

theorem endpointEvaluationImage_eq_blockRange
    (a : PointCoordinates K m p) (q : Fin r → Forms K (m+1) d) :
    endpointEvaluationImage q (fun j => chartPoint K a j) =
      (LinearMap.pi (Deformation.syzygyBlockEvaluation a q d)).range :=
  endpointEvaluationImage_eq_prefix a q

end ESCtoFroberg
