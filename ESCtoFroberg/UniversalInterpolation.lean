module

public import ESCtoFroberg.GenericRename
public import ESCtoFroberg.GeneralPoints

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open MvPolynomial Module

variable {K : Type*} [Field K]

/-- Constant coefficient extension of an actual homogeneous form. -/
def genericCoefficientForm (m p : ℕ) {d : ℕ} (f : Forms K (m+1) d) :
    Forms (GenericPointField K m p) (m+1) d :=
  ⟨MvPolynomial.map (algebraMap K (GenericPointField K m p)) f.val,
    f.property.map (algebraMap K (GenericPointField K m p))⟩

/-- The universal evaluation polynomial becomes actual evaluation over its fraction field. -/
theorem algebraMap_chartEvaluationPolynomial (m p : ℕ) {d : ℕ}
    (f : Forms K (m+1) d) (i : Fin p) :
    algebraMap (GenericPointRing K m p) (GenericPointField K m p)
        (chartEvaluationPolynomial f i) =
      pointEvaluation (GenericPointField K m p) (genericPointCoordinates K m p) d
        (genericCoefficientForm m p f) i := by
  rw [chartEvaluationPolynomial, MvPolynomial.eval₂_comp_left]
  change eval₂ ((algebraMap (GenericPointRing K m p) (GenericPointField K m p)).comp C)
    (fun j => algebraMap (GenericPointRing K m p) (GenericPointField K m p)
      (Fin.lastCases 1 (fun k => X (i,k)) j)) f.val =
    eval (chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) i)
      (MvPolynomial.map (algebraMap K (GenericPointField K m p)) f.val)
  rw [MvPolynomial.eval_map]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [genericPointCoordinates]

/-- Constant extension of a scalar coordinate functional. -/
def genericCoordinateFunctional (m p : ℕ) (ell : (Fin p → K) →ₗ[K] K) :
    (Fin p → GenericPointField K m p) →ₗ[GenericPointField K m p]
      GenericPointField K m p :=
  ∑ i, algebraMap K (GenericPointField K m p) (ell (Pi.single i 1)) • LinearMap.proj i

theorem algebraMap_dualEvaluationPolynomial (m p : ℕ) {d : ℕ}
    (f : Forms K (m+1) d) (ell : (Fin p → K) →ₗ[K] K) :
    algebraMap (GenericPointRing K m p) (GenericPointField K m p)
        (dualEvaluationPolynomial f ell) =
      genericCoordinateFunctional m p ell
        (pointEvaluation (GenericPointField K m p) (genericPointCoordinates K m p) d
          (genericCoefficientForm m p f)) := by
  simp only [dualEvaluationPolynomial, map_sum, map_mul,
    algebraMap_chartEvaluationPolynomial, genericCoordinateFunctional, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1

/-- The rank of any fixed configuration is a lower bound for universal-coordinate evaluation. -/
theorem pointHilbertFunction_le_generic (m p d : ℕ) (a₀ : PointCoordinates K m p) :
    pointHilbertFunction K a₀ d ≤
      pointHilbertFunction (GenericPointField K m p) (genericPointCoordinates K m p) d := by
  classical
  let U := LinearMap.range (pointEvaluation K a₀ d)
  let b := Module.finBasis K U
  have hb : LinearIndependent K (fun i => (b i).val) :=
    b.linearIndependent.map' U.subtype U.ker_subtype
  have hpre : ∀ i, ∃ x, pointEvaluation K a₀ d x = (b i).val := fun i => (b i).property
  choose x hx using hpre
  obtain ⟨dual, hdual⟩ := Froberg.exists_coordinate_functionals (fun i => (b i).val) hb
  let M : Matrix (Fin (finrank K U)) (Fin (finrank K U)) (GenericPointRing K m p) :=
    fun i j => dualEvaluationPolynomial (x j) (dual i)
  have hdet : M.det ≠ 0 := by
    have heval : eval a₀ M.det = 1 := by
      rw [(eval a₀).map_det]
      have hm : M.map (eval a₀) = (1 : Matrix (Fin (finrank K U)) _ K) := by
        ext i j
        change eval a₀ (dualEvaluationPolynomial (x j) (dual i)) = if i = j then 1 else 0
        rw [eval_dualEvaluationPolynomial, hx, hdual]
      change (M.map (eval a₀)).det = 1
      rw [hm, Matrix.det_one]
    intro hz
    simp [hz] at heval
  let R := GenericPointField K m p
  let eta := algebraMap (GenericPointRing K m p) R
  have hdetR : (M.map eta).det ≠ 0 := by
    change (eta.mapMatrix M).det ≠ 0
    rw [← eta.map_det]
    exact fun h => hdet ((IsFractionRing.injective (GenericPointRing K m p) R)
      (h.trans (map_zero eta).symm))
  let L : (Fin p → R) →ₗ[R] (Fin (finrank K U) → R) :=
    LinearMap.pi (fun i => genericCoordinateFunctional m p (dual i))
  let y : Fin (finrank K U) → Forms R (m+1) d := fun j => genericCoefficientForm m p (x j)
  have hm : M.map eta = Matrix.of (fun i j =>
      L (pointEvaluation R (genericPointCoordinates K m p) d (y j)) i) := by
    ext i j
    exact algebraMap_dualEvaluationPolynomial m p (x j) (dual i)
  rw [hm] at hdetR
  have hi : LinearIndependent R (fun j => pointEvaluation R
      (genericPointCoordinates K m p) d (y j)) :=
    LinearIndependent.of_comp L (Matrix.linearIndependent_cols_of_det_ne_zero hdetR)
  have hle : Submodule.span R (Set.range (fun j => pointEvaluation R
      (genericPointCoordinates K m p) d (y j))) ≤
      (pointEvaluation R (genericPointCoordinates K m p) d).range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨y j, rfl⟩
  have hdim := Submodule.finrank_mono hle
  rw [finrank_span_eq_card hi, Fintype.card_fin] at hdim
  simpa only [pointHilbertFunction_eq_rank] using hdim

/-- Universal normalized points have the expected Hilbert function in every degree. -/
theorem genericPoint_pointHilbertFunction [Infinite K] (m p d : ℕ) :
    pointHilbertFunction (GenericPointField K m p) (genericPointCoordinates K m p) d =
      min ((m+d).choose d) p := by
  obtain ⟨a₀, ha₀⟩ := exists_pointHilbertFunction_maximal (K := K) m p d
  apply le_antisymm (pointHilbertFunction_le _)
  rw [← ha₀]
  exact pointHilbertFunction_le_generic m p d a₀

/-- Universal point evaluation is onto as soon as there are enough degree-d forms. -/
theorem genericPoint_pointEvaluation_surjective [Infinite K] (m p d : ℕ)
    (hp : p ≤ (m+d).choose d) :
    Function.Surjective (pointEvaluation (GenericPointField K m p)
      (genericPointCoordinates K m p) d) := by
  apply pointEvaluation_surjective_of_hilbert_eq
  rw [genericPoint_pointHilbertFunction, min_eq_right hp]

/-- Universal point evaluation detects every form once the number of points reaches its dimension. -/
theorem genericPoint_pointEvaluation_injective [Infinite K] (m p d : ℕ)
    (hp : (m+d).choose d ≤ p) :
    Function.Injective (pointEvaluation (GenericPointField K m p)
      (genericPointCoordinates K m p) d) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  change finrank (GenericPointField K m p)
    (pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d) = 0
  rw [pointDegreePiece_finrank, genericPoint_pointHilbertFunction, min_eq_left hp, Nat.sub_self]

/-- The precise dimension of the generic degree-d vanishing forms. -/
theorem genericPoint_pointDegreePiece_finrank [Infinite K] (m p d : ℕ) :
    finrank (GenericPointField K m p)
      (pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d) =
        (m+d).choose d - p := by
  rw [pointDegreePiece_finrank, genericPoint_pointHilbertFunction]
  omega

/-- An actual independent generic basis with the expected fixed number of generators. -/
theorem genericPoint_exists_degree_basis [Infinite K] (m p d : ℕ) :
    ∃ q : Fin ((m+d).choose d - p) → Forms (GenericPointField K m p) (m+1) d,
      LinearIndependent (GenericPointField K m p) q ∧
      Submodule.span (GenericPointField K m p) (Set.range q) =
        pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d := by
  have h := exists_subspace_basis
    (pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d)
  rw [genericPoint_pointDegreePiece_finrank (K := K) m p d] at h
  exact h

end ESCtoFroberg
