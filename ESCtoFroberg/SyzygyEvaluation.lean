module

public import ESCtoFroberg.Points
public import Froberg.Prefix

@[expose] public section

noncomputable section
namespace ESCtoFroberg.Deformation
open Module MvPolynomial
variable {K : Type*} [Field K] {m p d e r : ℕ}

/-- Evaluation of the coefficient tuple of an actual syzygy at one point. -/
def syzygyBlockEvaluation (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m + 1) d) (e : ℕ) (j : Fin p) :
    (Froberg.prefixMultiplication q e).ker →ₗ[K] (Fin r → K) :=
  LinearMap.pi (fun i =>
    (evaluationLinear K (m + 1) e (chartPoint K a j)).comp
      ((LinearMap.proj i).comp (Froberg.prefixMultiplication q e).ker.subtype))

@[simp] theorem syzygyBlockEvaluation_apply (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m + 1) d)
    (z : (Froberg.prefixMultiplication q e).ker) (j : Fin p) (i : Fin r) :
    syzygyBlockEvaluation a q e j z i = pointEvaluation K a e (z.val i) j := rfl

/-- The scalar row determined by weights in one point block. -/
def evaluationRow (a : PointCoordinates K m p) (q : Fin r → Forms K (m + 1) d)
    (e : ℕ) (j : Fin p) (w : Fin r → K) :
    Module.Dual K (Froberg.prefixMultiplication q e).ker :=
  ∑ i, w i • ((LinearMap.proj i).comp (syzygyBlockEvaluation a q e j))

@[simp] theorem evaluationRow_apply (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m + 1) d)
    (z : (Froberg.prefixMultiplication q e).ker) (j : Fin p) (w : Fin r → K) :
    evaluationRow a q e j w z = ∑ i, w i * pointEvaluation K a e (z.val i) j := by
  simp [evaluationRow, smul_eq_mul]


end ESCtoFroberg.Deformation
