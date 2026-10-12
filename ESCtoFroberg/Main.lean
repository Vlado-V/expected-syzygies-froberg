module

public import ESCtoFroberg.UniversalChop
public import ESCtoFroberg.UniversalEndpoint
public import ESCtoFroberg.GenericBasis
public import ESCtoFroberg.PlateauDeformation
public import ESCtoFroberg.Descent
public import ESCtoFroberg.LowPointRange
public import ESCtoFroberg.StatementComparison

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open Module MvPolynomial Froberg

variable {K : Type*} [Field K] [CharZero K]

theorem N_succ (m j : ℕ) : N (m+1) j = (m+j).choose j := by
  unfold N
  congr 1
  omega

/-- Interpolation or the conjecture determines the universal chop: its value
is the point plateau or the positive part of the raw coefficient. -/
theorem universal_chop_plateau_or_raw (hESC : ExpectedSyzygyConjecture K)
    (m p d e : ℕ) (hm : 1 ≤ m) (hp : 1 ≤ p) (hd : 1 ≤ d)
    (hpD : p ≤ N (m+1) d) :
    choppedHilbertFunction (GenericPointField K m p)
        (genericPointCoordinates K m p) d (d+e) = p ∨
      choppedHilbertFunction (GenericPointField K m p)
        (genericPointCoordinates K m p) d (d+e) =
          (choppedRawCoefficient (m+1) d p e).toNat := by
  by_cases hprev : p ≤ N (m+1) (d-1)
  · left
    have hsurj := genericPoint_pointEvaluation_surjective (K := K) m p (d-1)
      (by simpa only [N_succ] using hprev)
    rw [choppedHilbertFunction_eq_point_above _ hd hsurj (by omega)]
    apply pointHilbertFunction_constant_above _ (show d-1 ≤ d+e by omega)
    rw [genericPoint_pointHilbertFunction,
      min_eq_right (by simpa only [N_succ] using hprev)]
  · have hinterp := isInterpolationDegree_of_bounds (show 1 ≤ m+1 by omega)
      hd (Nat.lt_of_not_ge hprev) hpD
    obtain ⟨D,hD,hgood⟩ := hESC m p d hm hp hd hinterp
    have hvalue : choppedHilbertFunction (GenericPointField K m p)
        (genericPointCoordinates K m p) d (d+e) = choppedPrediction (m+1) d p e :=
      genericPoint_choppedHF_transfer ⟨D,hD,fun a ha => (hgood a ha).2 e⟩
    by_cases hplateau : PlateauReached (m+1) d p e
    · exact Or.inl (hvalue.trans (choppedPrediction_after_plateau hplateau))
    · exact Or.inr (hvalue.trans (choppedPrediction_before_plateau hplateau))

/-- All nontrivial offsets attain the raw coefficient, using only the
Expected Syzygy Conjecture over the original characteristic-zero field. -/
theorem genericRawHilbertAt_inner (hESC : ExpectedSyzygyConjecture K)
    (m d r e : ℕ) (hm : 1 ≤ m) (hd : 2 ≤ d)
    (_hr : 1 ≤ r) (hrD : r < N (m+1) d) (he : 1 ≤ e) (heD : e ≤ d) :
    GenericRawHilbertAt K (m+1) d r (d+e) := by
  classical
  let p := N (m+1) d - r
  have hp : 1 ≤ p := by dsimp [p]; omega
  have hpD : p ≤ N (m+1) d := Nat.sub_le _ _
  have hcount : N (m+1) d - p = r := by dsimp [p]; omega
  by_cases hlow : e < d ∧ p < N (m+1) e
  · have h := genericRawHilbertAt_low_point_count (K := K)
      (show 1 ≤ m+1 by omega) (show 1 ≤ d by omega) hlow.1 hlow.2
    rwa [hcount] at h
  have hcoeff : e < d → N (m+1) e ≤ p := by omega
  have hfixed : r = (m+d).choose d - p := by
    simpa only [N_succ] using hcount.symm
  obtain ⟨b⟩ := genericPoint_exists_fixed_basis (K := K) (m := m) (p := p) (d := d) hfixed
  let R := GenericPointField K m p
  let a : PointCoordinates R m p := genericPointCoordinates K m p
  let q : Fin r → Forms R (m+1) d := genericBasisFamily K m p d r b
  have hq : LinearIndependent R q := genericBasisFamily_linearIndependent K m p d r b
  have hspace : familySpace q = pointDegreeSpace R a d :=
    genericBasisFamily_familySpace K m p d r b
  have hsurj : Function.Surjective (pointEvaluation R a d) :=
    genericPoint_pointEvaluation_surjective m p d (by simpa only [N_succ] using hpD)
  have hfamily : hilbertFunction (familySpace q) (d+e) =
      choppedHilbertFunction R a d (d+e) := by
    rw [hspace]
    rfl
  have hraw : choppedRawCoefficient (m+1) d p e =
      predictionCoefficient (m+1) d r (d+e) := by
    unfold choppedRawCoefficient
    rw [hcount]
  rcases universal_chop_plateau_or_raw hESC m p d e hm hp (by omega) hpD with hH | hH
  · have hτ : p - (predictionCoefficient (m+1) d r (d+e)).toNat ≤
        finrank R (Deformation.syzygyEvaluation a q e).range := by
      by_cases hprefix : e < d
      · have hinj := genericPoint_pointEvaluation_injective (K := K) m p e
          (by simpa only [N_succ] using hcoeff hprefix)
        exact prefixPlateau_deformation_row_bound a q hspace hH hprefix hinj
      · have hed : e = d := by omega
        subst e
        exact genericEndpoint_prefix_plateau_row_bound K m p d r b hm (by omega)
          (by simpa only [two_mul] using hH)
    obtain ⟨q',hq'⟩ := exists_family_raw_of_plateau a q hq hspace hsurj hH
      (show 1 ≤ d by omega) heD hrD.le
      (genericSyzygyProjectionRanks K m p d r b e) hτ
    exact genericRawHilbertAt_of_rational_family (K := K) (F := R)
      (σ := Fin p × Fin m) (by omega) (by omega) hrD.le heD q' hq'
  · rw [hraw] at hH
    exact genericRawHilbertAt_of_rational_family (K := K) (F := R)
      (σ := Fin p × Fin m) (by omega) (by omega) hrD.le heD q (hfamily.trans hH)

/-- Theorem 1.1: under the Expected Syzygy Conjecture, Fröberg's full positive
truncation holds through degree 2d on one nonempty coefficient open. -/
theorem frobergThrough2d_of_expectedSyzygy (hESC : ExpectedSyzygyConjecture K) :
    FrobergThrough2d K := by
  apply frobergThrough2d_of_inner_raw_offsets
  intro n d hn hd r hr hrD e he heD
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  exact genericRawHilbertAt_inner hESC m d r e (by omega) hd hr hrD he heD

/-- The complete manuscript implication, with no geometric witness premises. -/
theorem main_result : PaperStatement := by
  intro K _ _ hESC
  exact frobergThrough2d_of_expectedSyzygy hESC

/-- The same result in the independently specified, Mathlib-only statement. -/
theorem independent_main_result : Independent.Theorem11 :=
  StatementComparison.theorem11_iff_paperStatement.mpr main_result

end ESCtoFroberg
