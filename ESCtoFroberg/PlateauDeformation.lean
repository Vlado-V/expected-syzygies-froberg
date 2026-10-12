module

public import ESCtoFroberg.Deformation
public import ESCtoFroberg.BeforeEndpoint
public import ESCtoFroberg.LowerBound
public import ESCtoFroberg.CoefficientArithmetic

@[expose] public section

/-! The plateau case of the manuscript: enough independent syzygy evaluations
produce an actual deformation attaining the raw quotient dimension. -/
noncomputable section
namespace ESCtoFroberg
open Module MvPolynomial Froberg

variable {K : Type*} [Field K] {m p d e r : ℕ}

/-- Before the endpoint, injective coefficient evaluation identifies the full
syzygy-evaluation image dimension with the plateau minus the raw coefficient. -/
theorem prefixSyzygyEvaluation_euler (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m + 1) d)
    (hspace : familySpace q = pointDegreeSpace K a d)
    (hH : choppedHilbertFunction K a d (d + e) = p)
    (he : e < d) (heval : Function.Injective (pointEvaluation K a e)) :
    (finrank K (Deformation.syzygyEvaluation a q e).range : ℤ) =
      (p : ℤ) - predictionCoefficient (m + 1) d r (d + e) := by
  rw [Deformation.syzygyEvaluation_finrank_range a q heval]
  have hdim := prefix_euler_identity (e := e) (show 0 < m + 1 by omega) q
  have hHF : hilbertFunction (familySpace q) (d + e) = p := by
    rw [hspace]
    exact hH
  rw [hHF] at hdim
  rw [predictionCoefficient_prefix (show 1 ≤ m + 1 by omega) he]
  unfold N
  zify at hdim
  omega

/-- Thus the full evaluation image supplies the required number of deformation
rows before the endpoint, including a nonpositive raw coefficient. -/
theorem prefixPlateau_deformation_row_bound (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m + 1) d)
    (hspace : familySpace q = pointDegreeSpace K a d)
    (hH : choppedHilbertFunction K a d (d + e) = p)
    (he : e < d) (heval : Function.Injective (pointEvaluation K a e)) :
    p - (predictionCoefficient (m + 1) d r (d + e)).toNat ≤
      finrank K (Deformation.syzygyEvaluation a q e).range := by
  have h := prefixSyzygyEvaluation_euler a q hspace hH he heval
  omega

/-- A point-ideal plateau, symmetric projection ranks, and the needed full
image rank give the raw generic Hilbert value by actual polynomial deformation. -/
theorem exists_family_raw_of_plateau [Infinite K]
    (a : PointCoordinates K m p) (q : Fin r → Forms K (m + 1) d)
    (hq : LinearIndependent K q)
    (hspace : familySpace q = pointDegreeSpace K a d)
    (hsurj : Function.Surjective (pointEvaluation K a d))
    (hH : choppedHilbertFunction K a d (d + e) = p)
    (hd : 1 ≤ d) (he : e ≤ d) (hr : r ≤ N (m + 1) d)
    (hsym : ∀ S T : Finset (Fin p), S.card = T.card →
      finrank K (LinearMap.pi (fun j : S => Deformation.syzygyBlockEvaluation a q e j.val)).range =
      finrank K (LinearMap.pi (fun j : T => Deformation.syzygyBlockEvaluation a q e j.val)).range)
    (hτ : p - (predictionCoefficient (m + 1) d r (d + e)).toNat ≤
      finrank K (Deformation.syzygyEvaluation a q e).range) :
    ∃ q' : Fin r → Forms K (m + 1) d,
      hilbertFunction (familySpace q') (d + e) =
        (predictionCoefficient (m + 1) d r (d + e)).toNat := by
  have hn : 0 < m + 1 := by omega
  have ht : d + e ≤ 2 * d := by omega
  have hHF : hilbertFunction (familySpace q) (d + e) = p := by
    rw [hspace]
    exact hH
  have hraw_le : (predictionCoefficient (m + 1) d r (d + e)).toNat ≤ p := by
    have h := hilbertFunction_raw_lower_bound hn (by omega) q hq (d + e) ht
    rwa [hHF] at h
  have himage := Deformation.prefixMultiplication_range_eq_pointKernel a q hspace
    (pointEvaluation_surjective_add a hsurj e) hH
  classical
  let b := p - (predictionCoefficient (m + 1) d r (d + e)).toNat
  let μ := prefixMultiplication q e
  let Z := μ.ker
  let blocks : Fin p → Z →ₗ[K] (Fin r → K) := Deformation.syzygyBlockEvaluation a q e
  let σ : Fin b → Fin p := Fin.castLE (Nat.sub_le _ _)
  have hσ : Function.Injective σ := Fin.castLE_injective (Nat.sub_le _ _)
  have hsym' : ∀ S T : Finset (Fin p), S.card = T.card →
      finrank K (LinearMap.pi (fun j : S => blocks j.val)).range =
      finrank K (LinearMap.pi (fun j : T => blocks j.val)).range := hsym
  have hfull : b ≤ finrank K (LinearMap.pi blocks).range := hτ
  have hfull' : Fintype.card (Fin b) ≤ finrank K (LinearMap.pi blocks).range := by
    simpa only [Fintype.card_fin] using hfull
  have hRado := @independentEvaluationRows_of_projectionRanks K Z (Fin r) (Fin p) (Fin b)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance blocks hsym' σ hσ hfull'
  obtain ⟨w, hw⟩ := hRado
  have hw' : LinearIndependent K (fun k => Deformation.evaluationRow a q e (σ k) (w k)) := hw
  obtain ⟨δ, ε, -, hupp⟩ := Deformation.exists_deformation_hilbert_le a q hsurj himage σ hσ w hw'
  let q' : Fin r → Forms K (m + 1) d := q + ε • δ
  have hcoord : coefficientForms K (m + 1) d r (coefficientCoordinates q') = q' :=
    coefficientCoordinates.symm_apply_apply q'
  have hlow := coefficientHilbertFunction_raw_lower_bound hn (by omega) hr
    (d + e) ht (coefficientCoordinates q')
  change (predictionCoefficient (m + 1) d r (d + e)).toNat ≤
    hilbertFunction (familySpace (coefficientForms K (m + 1) d r (coefficientCoordinates q'))) (d + e) at hlow
  rw [hcoord] at hlow
  have hEq : hilbertFunction (familySpace q') (d + e) =
      (predictionCoefficient (m + 1) d r (d + e)).toNat := by
    change hilbertFunction (familySpace q') (d + e) ≤
      p - (p - (predictionCoefficient (m + 1) d r (d + e)).toNat) at hupp
    omega
  exact ⟨q', hEq⟩

/-- The actual plateau deformation supplies the raw value on a nonempty open
of arbitrary coefficient tuples. -/
theorem genericRawHilbertAt_of_plateau [Infinite K]
    (a : PointCoordinates K m p) (q : Fin r → Forms K (m + 1) d)
    (hq : LinearIndependent K q)
    (hspace : familySpace q = pointDegreeSpace K a d)
    (hsurj : Function.Surjective (pointEvaluation K a d))
    (hH : choppedHilbertFunction K a d (d + e) = p)
    (hd : 1 ≤ d) (he : e ≤ d) (hr : r ≤ N (m + 1) d)
    (hsym : ∀ S T : Finset (Fin p), S.card = T.card →
      finrank K (LinearMap.pi (fun j : S => Deformation.syzygyBlockEvaluation a q e j.val)).range =
      finrank K (LinearMap.pi (fun j : T => Deformation.syzygyBlockEvaluation a q e j.val)).range)
    (hτ : p - (predictionCoefficient (m + 1) d r (d + e)).toNat ≤
      finrank K (Deformation.syzygyEvaluation a q e).range) :
    GenericRawHilbertAt K (m + 1) d r (d + e) := by
  obtain ⟨q', hq'⟩ := exists_family_raw_of_plateau a q hq hspace hsurj hH hd he hr hsym hτ
  exact genericRawHilbertAt_of_family_witness (by omega) (by omega) hr
    (d + e) (by omega) q' hq'

/-- The prefix plateau provides an actual attaining family using injectivity
of coefficient evaluation and the generic projection symmetry. -/
theorem exists_family_raw_of_prefix_plateau [Infinite K]
    (a : PointCoordinates K m p) (q : Fin r → Forms K (m + 1) d)
    (hq : LinearIndependent K q)
    (hspace : familySpace q = pointDegreeSpace K a d)
    (hsurj : Function.Surjective (pointEvaluation K a d))
    (hH : choppedHilbertFunction K a d (d + e) = p)
    (hd : 1 ≤ d) (he : e < d) (hr : r ≤ N (m + 1) d)
    (heval : Function.Injective (pointEvaluation K a e))
    (hsym : ∀ S T : Finset (Fin p), S.card = T.card →
      finrank K (LinearMap.pi (fun j : S => Deformation.syzygyBlockEvaluation a q e j.val)).range =
      finrank K (LinearMap.pi (fun j : T => Deformation.syzygyBlockEvaluation a q e j.val)).range) :
    ∃ q' : Fin r → Forms K (m + 1) d,
      hilbertFunction (familySpace q') (d + e) =
        (predictionCoefficient (m + 1) d r (d + e)).toNat :=
  exists_family_raw_of_plateau a q hq hspace hsurj hH hd he.le hr hsym
    (prefixPlateau_deformation_row_bound a q hspace hH he heval)

/-- In the prefix, the row bound follows directly from injective coefficient
evaluation, leaving only the proved generic projection symmetry to supply. -/
theorem genericRawHilbertAt_of_prefix_plateau [Infinite K]
    (a : PointCoordinates K m p) (q : Fin r → Forms K (m + 1) d)
    (hq : LinearIndependent K q)
    (hspace : familySpace q = pointDegreeSpace K a d)
    (hsurj : Function.Surjective (pointEvaluation K a d))
    (hH : choppedHilbertFunction K a d (d + e) = p)
    (hd : 1 ≤ d) (he : e < d) (hr : r ≤ N (m + 1) d)
    (heval : Function.Injective (pointEvaluation K a e))
    (hsym : ∀ S T : Finset (Fin p), S.card = T.card →
      finrank K (LinearMap.pi (fun j : S => Deformation.syzygyBlockEvaluation a q e j.val)).range =
      finrank K (LinearMap.pi (fun j : T => Deformation.syzygyBlockEvaluation a q e j.val)).range) :
    GenericRawHilbertAt K (m + 1) d r (d + e) :=
  genericRawHilbertAt_of_plateau a q hq hspace hsurj hH hd he.le hr hsym
    (prefixPlateau_deformation_row_bound a q hspace hH he heval)

end ESCtoFroberg
