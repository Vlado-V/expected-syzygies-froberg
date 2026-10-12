module

public import ESCtoFroberg.Points
public import Froberg.Generic
public import Mathlib.Algebra.CharZero.Infinite

@[expose] public section

set_option maxHeartbeats 1000000

noncomputable section
namespace ESCtoFroberg
open MvPolynomial Module

variable {K : Type*} [Field K]

/-- Affine chart evaluations detect every homogeneous form. -/
theorem homogeneous_eq_zero_of_chart_evaluations [Infinite K] {m d : ℕ}
    (f : Forms K (m + 1) d)
    (h : ∀ u : Fin m → K, eval (Fin.lastCases 1 u) f.val = 0) : f = 0 := by
  have hz : (X (Fin.last m) : Poly K (m + 1)) * f.val = 0 := by
    apply MvPolynomial.funext
    intro v
    simp only [map_mul, eval_X, map_zero]
    by_cases hv : v (Fin.last m) = 0
    · simp [hv]
    · let u : Fin m → K := fun j => v j.castSucc / v (Fin.last m)
      have he : (fun i : Fin (m + 1) => v (Fin.last m) * Fin.lastCases 1 u i) = v := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp
        · simp [u, mul_div_cancel₀ _ hv]
      have hs := homogeneous_eval_scale f.property (Fin.lastCases 1 u) (v (Fin.last m))
      rw [he, h] at hs
      simp [hs]
  have hf : f.val = 0 := (mul_eq_zero.mp hz).resolve_left (MvPolynomial.X_ne_zero _)
  exact Subtype.ext hf

/-- Evaluations on the normalized chart span the full dual form space. -/
theorem chart_evaluations_span_dual [Infinite K] (m d : ℕ) :
    Submodule.span K (Set.range (fun u : Fin m → K =>
      evaluationLinear K (m + 1) d (Fin.lastCases 1 u))) = ⊤ := by
  apply Submodule.span_eq_top_of_ne_zero
  intro f hf
  by_contra! h
  apply hf
  apply homogeneous_eq_zero_of_chart_evaluations f
  intro u
  exact h (evaluationLinear K (m + 1) d (Fin.lastCases 1 u)) ⟨u, rfl⟩

/-- Independent chart evaluations of every admissible finite size exist. -/
theorem exists_independent_chart_evaluations [Infinite K] (m d q : ℕ)
    (hq : q ≤ (m + d).choose d) :
    ∃ u : Fin q → Fin m → K,
      LinearIndependent K (fun i => evaluationLinear K (m + 1) d (Fin.lastCases 1 (u i))) := by
  classical
  induction q with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type⟩
  | succ q ih =>
      obtain ⟨u, hu⟩ := ih (by omega)
      let W := Submodule.span K (Set.range (fun i =>
        evaluationLinear K (m + 1) d (Fin.lastCases 1 (u i))))
      have hW : finrank K W = q := by simp [W, finrank_span_eq_card hu]
      have hproper : W ≠ ⊤ := by
        intro heq
        have ht : finrank K W = (m + d).choose d := by
          rw [heq, finrank_top, Subspace.dual_finrank_eq, finrank_forms]
        omega
      have hex : ∃ v : Fin m → K,
          evaluationLinear K (m + 1) d (Fin.lastCases 1 v) ∉ W := by
        by_contra! h
        have hle : Submodule.span K (Set.range (fun v : Fin m → K =>
            evaluationLinear K (m + 1) d (Fin.lastCases 1 v))) ≤ W := by
          apply Submodule.span_le.mpr
          rintro _ ⟨v, rfl⟩
          exact h v
        rw [chart_evaluations_span_dual m d] at hle
        exact hproper (top_le_iff.mp hle)
      obtain ⟨v, hv⟩ := hex
      let u' : Fin (q + 1) → Fin m → K := Fin.snoc u v
      refine ⟨u', ?_⟩
      have heq : (fun i : Fin (q + 1) =>
          evaluationLinear K (m + 1) d (Fin.lastCases 1 (u' i))) =
          Fin.snoc (fun i => evaluationLinear K (m + 1) d (Fin.lastCases 1 (u i)))
            (evaluationLinear K (m + 1) d (Fin.lastCases 1 v)) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [u']
      rw [heq]
      exact linearIndependent_finSnoc.mpr ⟨hu, hv⟩

/-- The largest possible degree evaluation rank is attained by actual chart points. -/
theorem exists_pointHilbertFunction_maximal [Infinite K] (m p d : ℕ) :
    ∃ a : PointCoordinates K m p,
      pointHilbertFunction K a d = min ((m + d).choose d) p := by
  classical
  let q := min ((m + d).choose d) p
  obtain ⟨u, hu⟩ := exists_independent_chart_evaluations (K := K) m d q (min_le_left _ _)
  let a : PointCoordinates K m p := fun ik =>
    if h : ik.1.val < q then u ⟨ik.1.val, h⟩ ik.2 else 0
  refine ⟨a, le_antisymm (pointHilbertFunction_le a) ?_⟩
  rw [pointHilbertFunction_eq_rank, ← LinearMap.finrank_range_dualMap_eq_finrank_range]
  have hle : Submodule.span K (Set.range (fun i =>
      evaluationLinear K (m + 1) d (Fin.lastCases 1 (u i)))) ≤
      (pointEvaluation K a d).dualMap.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨LinearMap.proj (Fin.castLE (min_le_right _ _) i), ?_⟩
    apply LinearMap.ext
    intro f
    have ha : chartPoint K a (Fin.castLE (min_le_right _ _) i) = Fin.lastCases 1 (u i) := by
      funext j
      refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [chartPoint, a, i.isLt]
    simp [LinearMap.dualMap_apply, pointEvaluation, evaluationLinear, ha]
  have hdim := Submodule.finrank_mono hle
  simpa only [finrank_span_eq_card hu, Fintype.card_fin] using hdim

/-- Universal-coordinate evaluation of one fixed form at one point. -/
def chartEvaluationPolynomial {m p d : ℕ} (f : Forms K (m + 1) d) (i : Fin p) :
    MvPolynomial (Fin p × Fin m) K :=
  eval₂ C (Fin.lastCases 1 (fun j => X (i, j))) f.val

@[simp] theorem eval_chartEvaluationPolynomial {m p d : ℕ} (f : Forms K (m + 1) d)
    (i : Fin p) (a : PointCoordinates K m p) :
    eval a (chartEvaluationPolynomial f i) = pointEvaluation K a d f i := by
  rw [chartEvaluationPolynomial, MvPolynomial.eval_eval₂]
  change eval₂ ((eval a).comp C)
    (fun j => eval a (Fin.lastCases 1 (fun k => X (i, k)) j)) f.val = _
  have hc : (eval a).comp C = RingHom.id K := by ext c; simp
  rw [hc]
  congr 1
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [chartPoint]

/-- Any dual coordinate of evaluation is a polynomial in point coordinates. -/
def dualEvaluationPolynomial {m p d : ℕ} (f : Forms K (m + 1) d)
    (ell : (Fin p → K) →ₗ[K] K) : MvPolynomial (Fin p × Fin m) K :=
  ∑ i, C (ell (Pi.single i 1)) * chartEvaluationPolynomial f i

@[simp] theorem eval_dualEvaluationPolynomial {m p d : ℕ} (f : Forms K (m + 1) d)
    (ell : (Fin p → K) →ₗ[K] K) (a : PointCoordinates K m p) :
    eval a (dualEvaluationPolynomial f ell) = ell (pointEvaluation K a d f) := by
  classical
  have h := congrArg ell ((Pi.basisFun K (Fin p)).sum_equivFun (pointEvaluation K a d f))
  simpa [dualEvaluationPolynomial, map_sum, Pi.basisFun_apply, Pi.basisFun_equivFun,
    smul_eq_mul, mul_comm] using h

/-- Determinant nonvanishing preserves the rank attained by a fixed configuration. -/
theorem pointEvaluation_rank_principal_open (m p d : ℕ) (a₀ : PointCoordinates K m p) :
    ∃ D : MvPolynomial (Fin p × Fin m) K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → pointHilbertFunction K a₀ d ≤ pointHilbertFunction K a d := by
  classical
  let R := LinearMap.range (pointEvaluation K a₀ d)
  let b := Module.finBasis K R
  have hb : LinearIndependent K (fun i => (b i).val) :=
    b.linearIndependent.map' R.subtype (LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _))
  have hpre : ∀ i, ∃ x, pointEvaluation K a₀ d x = (b i).val := fun i => (b i).property
  choose x hx using hpre
  obtain ⟨dual, hdual⟩ := Froberg.exists_coordinate_functionals (fun i => (b i).val) hb
  let M : Matrix (Fin (finrank K R)) (Fin (finrank K R)) (MvPolynomial (Fin p × Fin m) K) :=
    fun i j => dualEvaluationPolynomial (x j) (dual i)
  have heval (a : PointCoordinates K m p) : eval a M.det =
      (Matrix.of fun i j => dual i (pointEvaluation K a d (x j))).det := by
    rw [(eval a).map_det]
    congr 1
    ext i j
    exact eval_dualEvaluationPolynomial (x j) (dual i) a
  refine ⟨M.det, ?_, ?_⟩
  · rw [heval]
    have hM : (Matrix.of fun i j => dual i (pointEvaluation K a₀ d (x j))) =
        (1 : Matrix (Fin (finrank K R)) (Fin (finrank K R)) K) := by
      ext i j
      simp [hx, hdual, Matrix.one_apply]
    rw [hM, Matrix.det_one]
    exact one_ne_zero
  · intro a ha
    rw [heval] at ha
    let L : (Fin p → K) →ₗ[K] (Fin (finrank K R) → K) := LinearMap.pi dual
    have hi : LinearIndependent K (fun j => pointEvaluation K a d (x j)) :=
      LinearIndependent.of_comp L (Matrix.linearIndependent_cols_of_det_ne_zero ha)
    have hle : Submodule.span K (Set.range (fun j => pointEvaluation K a d (x j))) ≤
        (pointEvaluation K a d).range := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact ⟨x j, rfl⟩
    have hdim := Submodule.finrank_mono hle
    rw [finrank_span_eq_card hi, Fintype.card_fin] at hdim
    simpa only [pointHilbertFunction_eq_rank] using hdim

/-- The expected Hilbert function in one degree holds on a nonempty principal open. -/
theorem generic_pointHilbertFunction_at [Infinite K] (m p d : ℕ) :
    ∃ D : MvPolynomial (Fin p × Fin m) K,
      (∃ a : PointCoordinates K m p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → pointHilbertFunction K a d = min ((m + d).choose d) p := by
  obtain ⟨a₀, ha₀⟩ := exists_pointHilbertFunction_maximal (K := K) m p d
  obtain ⟨D, hD, hgood⟩ := pointEvaluation_rank_principal_open m p d a₀
  refine ⟨D, ⟨a₀, hD⟩, fun a ha => le_antisymm (pointHilbertFunction_le a) ?_⟩
  rw [← ha₀]
  exact hgood a ha

/-- Multiplication by the normalized chart coordinate propagates surjectivity. -/
theorem pointEvaluation_surjective_above {m p q t : ℕ} (a : PointCoordinates K m p)
    (hqt : q ≤ t) (h : Function.Surjective (pointEvaluation K a q)) :
    Function.Surjective (pointEvaluation K a t) := by
  intro y
  obtain ⟨f, hf⟩ := h y
  let g : Forms K (m + 1) t := ⟨f.val * X (Fin.last m) ^ (t - q), by
    have hh := f.property.mul ((isHomogeneous_X (R := K) (Fin.last m)).pow (t - q))
    simpa [Nat.add_sub_of_le hqt] using hh⟩
  refine ⟨g, ?_⟩
  ext i
  change eval (chartPoint K a i) (f.val * X (Fin.last m) ^ (t - q)) = y i
  simpa using congrFun hf i

theorem pointEvaluation_surjective_of_hilbert_eq {m p q : ℕ} (a : PointCoordinates K m p)
    (h : pointHilbertFunction K a q = p) :
    Function.Surjective (pointEvaluation K a q) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa [pointHilbertFunction_eq_rank, Module.finrank_pi_fintype] using h

theorem pointHilbertFunction_constant_above {m p q t : ℕ} (a : PointCoordinates K m p)
    (hqt : q ≤ t) (h : pointHilbertFunction K a q = p) :
    pointHilbertFunction K a t = p := by
  rw [pointHilbertFunction_eq_rank,
    LinearMap.range_eq_top.mpr (pointEvaluation_surjective_above a hqt
      (pointEvaluation_surjective_of_hilbert_eq a h)), finrank_top]
  simp

/-- In a positive dimensional projective space, degree `p` suffices for `p` points. -/
theorem point_count_le_forms (m p : ℕ) (hm : 1 ≤ m) : p ≤ (m + p).choose p := by
  have h : p + 1 ≤ (m + p).choose p := by
    have hp : (p + 1).choose p = p + 1 := by simpa using Nat.choose_succ_self_right p
    rw [← hp]
    exact Nat.choose_le_choose p (by omega)
  omega

/-- A separation polynomial for the first affine coordinate. -/
def distinctnessPolynomial (K : Type*) [Field K] (m p : ℕ) (hm : 1 ≤ m) :
    MvPolynomial (Fin p × Fin m) K :=
  ∏ ij : {ij : Fin p × Fin p // ij.1 < ij.2},
    (X (ij.val.1, ⟨0, hm⟩) - X (ij.val.2, ⟨0, hm⟩))

theorem distinctnessPolynomial_nonempty [CharZero K] (m p : ℕ) (hm : 1 ≤ m) :
    ∃ a : PointCoordinates K m p, eval a (distinctnessPolynomial K m p hm) ≠ 0 := by
  classical
  refine ⟨fun ik => if ik.2.val = 0 then (ik.1.val : K) else 0, ?_⟩
  simp only [distinctnessPolynomial, map_prod, map_sub, eval_X]
  apply Finset.prod_ne_zero_iff.mpr
  intro ij _
  simp only [ite_true]
  apply sub_ne_zero.mpr
  exact_mod_cast (ne_of_lt ij.property : ij.val.1.val ≠ ij.val.2.val)

theorem distinctPoints_of_polynomial_ne_zero {m p : ℕ} (hm : 1 ≤ m)
    (a : PointCoordinates K m p) (h : eval a (distinctnessPolynomial K m p hm) ≠ 0) :
    DistinctPoints K a := by
  classical
  have hall : ∀ ij : {ij : Fin p × Fin p // ij.1 < ij.2},
      a (ij.val.1, ⟨0, hm⟩) - a (ij.val.2, ⟨0, hm⟩) ≠ 0 := by
    simp only [distinctnessPolynomial, map_prod, map_sub, eval_X] at h
    intro ij
    exact (Finset.prod_ne_zero_iff.mp h) ij (Finset.mem_univ ij)
  intro i j hij
  by_contra hn
  have heq : a (i, ⟨0, hm⟩) = a (j, ⟨0, hm⟩) := congrFun hij ⟨0, hm⟩
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · exact hall ⟨(i, j), hlt⟩ (by simp [heq])
  · exact hall ⟨(j, i), hgt⟩ (by simp [heq])

/-- One nonempty principal open gives distinct points and the expected Hilbert
function in every degree simultaneously. -/
theorem generic_pointHilbertFunction [CharZero K] (m p : ℕ) (hm : 1 ≤ m) :
    ∃ D : MvPolynomial (Fin p × Fin m) K,
      (∃ a : PointCoordinates K m p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → DistinctPoints K a ∧
        ∀ t, pointHilbertFunction K a t = min ((m + t).choose t) p := by
  classical
  choose D hD hgood using fun i : Fin (p + 1) =>
    generic_pointHilbertFunction_at (K := K) m p i.val
  let E := distinctnessPolynomial K m p hm * ∏ i, D i
  have hne : E ≠ 0 := by
    apply mul_ne_zero
    · obtain ⟨a, ha⟩ := distinctnessPolynomial_nonempty (K := K) m p hm
      intro hz
      simp [hz] at ha
    · apply Finset.prod_ne_zero_iff.mpr
      intro i _
      obtain ⟨a, ha⟩ := hD i
      intro hz
      simp [hz] at ha
  have hex : ∃ a : PointCoordinates K m p, eval a E ≠ 0 := by
    by_contra! h
    exact hne (MvPolynomial.funext h)
  refine ⟨E, hex, ?_⟩
  intro a ha
  have hparts : eval a (distinctnessPolynomial K m p hm) ≠ 0 ∧
      ∀ i, eval a (D i) ≠ 0 := by
    simpa only [E, map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
      Finset.mem_univ, forall_true_left] using ha
  refine ⟨distinctPoints_of_polynomial_ne_zero hm a hparts.1, ?_⟩
  intro t
  by_cases ht : t ≤ p
  · exact hgood ⟨t, by omega⟩ a (hparts.2 ⟨t, by omega⟩)
  · have hp : pointHilbertFunction K a p = p := by
      simpa only [min_eq_right (point_count_le_forms m p hm)] using
        hgood ⟨p, by omega⟩ a (hparts.2 ⟨p, by omega⟩)
    have hc := pointHilbertFunction_constant_above a (by omega : p ≤ t) hp
    have hle : p ≤ (m + t).choose t := by
      have hpdim := point_count_le_forms m p hm
      rw [← Nat.choose_symm_add] at hpdim ⊢
      exact hpdim.trans (Nat.choose_le_choose m (by omega))
    simpa only [min_eq_right hle] using hc

end ESCtoFroberg
