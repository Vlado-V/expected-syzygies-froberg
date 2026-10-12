module

public import ESCtoFroberg.EndpointCriterion
public import ESCtoFroberg.DerivationFraction
public import ESCtoFroberg.GenericRename
public import Mathlib.LinearAlgebra.Finsupp.Defs

@[expose] public section

noncomputable section
namespace ESCtoFroberg

open MvPolynomial

section Coefficients
variable {K R σ : Type*} [CommRing K] [CommRing R] [Algebra K R]

/-- Apply a derivation of the coefficient field to every polynomial coefficient. -/
def coefficientLinear (D : Derivation K R R) : MvPolynomial σ R →ₗ[K] MvPolynomial σ R :=
  (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap D.toLinearMap ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

@[simp] theorem coefficientLinear_coeff (D : Derivation K R R)
    (f : MvPolynomial σ R) (e : σ →₀ ℕ) :
    (coefficientLinear D f).coeff e = D (f.coeff e) := rfl

@[simp] theorem coefficientLinear_monomial (D : Derivation K R R)
    (e : σ →₀ ℕ) (c : R) :
    coefficientLinear D (monomial e c) = monomial e (D c) := by
  classical
  ext a
  by_cases h : e = a <;> simp [coeff_monomial, h]

/-- Coefficient differentiation is a genuine derivation of the polynomial ring. -/
def coefficientDerivation (D : Derivation K R R) :
    Derivation K (MvPolynomial σ R) (MvPolynomial σ R) where
  toLinearMap := coefficientLinear D
  map_one_eq_zero' := by
    change coefficientLinear D (monomial 0 1) = 0
    rw [coefficientLinear_monomial, Derivation.map_one_eq_zero]
    exact (monomial 0).map_zero
  leibniz' f g := by
    induction f using MvPolynomial.induction_on' with
    | add f g hf hg =>
      simp only [add_mul, map_add, hf, hg, add_smul, smul_add]
      abel
    | monomial e a =>
      induction g using MvPolynomial.induction_on' with
      | add f g hf hg =>
        simp only [mul_add, map_add, hf, hg, add_smul, smul_add]
        abel
      | monomial v b =>
        simp only [monomial_mul_monomial, coefficientLinear_monomial,
          Derivation.leibniz, smul_eq_mul, mul_comm b]
        rw [add_comm v e, ← map_add]

@[simp] theorem coefficientDerivation_coeff (D : Derivation K R R)
    (f : MvPolynomial σ R) (e : σ →₀ ℕ) :
    (coefficientDerivation D f).coeff e = D (f.coeff e) := rfl

@[simp] theorem coefficientDerivation_C (D : Derivation K R R) (c : R) :
    coefficientDerivation (σ := σ) D (C c) = C (D c) := by
  exact coefficientLinear_monomial D 0 c

@[simp] theorem coefficientDerivation_X (D : Derivation K R R) (i : σ) :
    coefficientDerivation D (X i) = 0 := by
  change coefficientLinear D (X i) = 0
  rw [X, coefficientLinear_monomial]
  simp

theorem coefficientDerivation_isHomogeneous (D : Derivation K R R)
    {f : MvPolynomial σ R} {d : ℕ} (hf : f.IsHomogeneous d) :
    (coefficientDerivation D f).IsHomogeneous d := by
  intro e he
  exact hf (fun hz => he (by simp [hz]))

/-- The multivariate chain rule, including derivatives of rational coefficients. -/
theorem deriv_eval (D : Derivation K R R) [Fintype σ] (z : σ → R)
    (f : MvPolynomial σ R) :
    D (eval z f) = eval z (coefficientDerivation D f) +
      ∑ j, D (z j) * eval z (pderiv j f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg =>
    simp only [map_add, hf, hg, mul_add, Finset.sum_add_distrib]
    abel
  | mul_X f k hf =>
    simp only [map_mul, eval_X, Derivation.leibniz, smul_eq_mul,
      coefficientDerivation_X, mul_zero, zero_add, pderiv_X,
      map_add, map_mul, hf]
    simp only [mul_add, Finset.sum_add_distrib, Pi.single_apply, apply_ite, map_one,
      map_zero, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hsum : (∑ x, D (z x) * (z k * eval z (pderiv x f))) =
        z k * ∑ x, D (z x) * eval z (pderiv x f) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hsum]
    ring

end Coefficients

section MovingRelations
variable {K R : Type*} [Field K] [Field R] [Algebra K R] {n d r p : ℕ}

/-- Differentiating coefficients preserves the homogeneous degree. -/
def coefficientDerivativeForm (D : Derivation K R R) (f : Froberg.Forms R n d) :
    Froberg.Forms R n d :=
  ⟨coefficientDerivation D f.val, coefficientDerivation_isHomogeneous D f.property⟩

/-- The coefficient vector obtained by differentiating a genuine symmetric relation. -/
def motionCoefficients (D : Derivation K R R) (M : Matrix (Fin r) (Fin r) R)
    (q : Fin r → Froberg.Forms R n d) : Fin r → Froberg.Forms R n d :=
  fun i => (∑ j, D (M i j) • q j) + (2 : R) •
    (∑ j, M i j • coefficientDerivativeForm D (q j))

@[simp] theorem motionCoefficients_val (D : Derivation K R R)
    (M : Matrix (Fin r) (Fin r) R) (q : Fin r → Froberg.Forms R n d) (i : Fin r) :
    (motionCoefficients D M q i).val =
      differentiatedRelation (coefficientDerivation D) (fun i j => C (M i j))
        (fun j => (q j).val) i := by
  simp [motionCoefficients, differentiatedRelation, coefficientDerivativeForm,
    MvPolynomial.smul_eq_C_mul, Finset.mul_sum, map_ofNat]

/-- Every rational symmetric relation produces a genuine homogeneous polynomial syzygy. -/
theorem motionCoefficients_is_syzygy (D : Derivation K R R)
    (M : Matrix (Fin r) (Fin r) R) (hM : ∀ i j, M i j = M j i)
    (q : Fin r → Froberg.Forms R n d)
    (hrel : Froberg.endpointMultiplication q (matrixAction M q) = 0) :
    Froberg.endpointMultiplication q (motionCoefficients D M q) = 0 := by
  classical
  apply Subtype.ext
  rw [Froberg.endpointMultiplication_val]
  simp only [motionCoefficients_val]
  apply differentiatedRelation_is_syzygy (coefficientDerivation D)
  · intro i j
    rw [hM]
  · have h := congrArg Subtype.val hrel
    simpa [Froberg.endpointMultiplication_val, quadraticRelation, ringMatrixAction,
      matrixAction, MvPolynomial.smul_eq_C_mul] using h

/-- Differentiating the identity that a form vanishes at its varying point. -/
theorem eval_coefficientDerivation_of_vanish (D : Derivation K R R)
    (z : Fin n → R) (f : Froberg.Poly R n) (hz : eval z f = 0) :
    eval z (coefficientDerivation D f) =
      -(∑ j, D (z j) * eval z (pderiv j f)) := by
  have h := deriv_eval D z f
  rw [hz, map_zero] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- Matrix action commutes with the spatial directional derivative. -/
theorem directionalEvaluation_matrixAction (M : Matrix (Fin r) (Fin r) R)
    (q : Fin r → Froberg.Forms R n d) (z v : Fin n → R) (i : Fin r) :
    directionalEvaluation (matrixAction M q i).val z v =
      ∑ j, M i j * directionalEvaluation (q j).val z v := by
  classical
  simp only [directionalEvaluation, matrixAction, Submodule.coe_sum, Submodule.coe_smul,
    map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [(pderiv k).map_smul]
  simp only [MvPolynomial.smul_eq_C_mul, map_mul, eval_C]
  ring

/-- At a common zero only the differentiated generators contribute. -/
theorem eval_motionCoefficients (D : Derivation K R R)
    (M : Matrix (Fin r) (Fin r) R) (q : Fin r → Froberg.Forms R n d)
    (z : Fin n → R) (hqz : ∀ j, eval z (q j).val = 0) (i : Fin r) :
    eval z (motionCoefficients D M q i).val =
      2 * (∑ j, M i j * eval z (coefficientDerivation D (q j).val)) := by
  simp [motionCoefficients, coefficientDerivativeForm, hqz]

/-- Any derivation moving exactly one point realizes the required actual tangent syzygy. -/
theorem endpointMotionProperty_of_pointDerivations
    (q : Fin r → Froberg.Forms R n d) (z : Fin p → Fin n → R)
    (chart : Fin p → Fin n) (hqz : ∀ i a, eval (z a) (q i).val = 0)
    (hderiv : ∀ a (v : Fin n → R), v (chart a) = 0 →
      ∃ D : Derivation K R R, ∀ c j, D (z c j) = if c = a then v j else 0) :
    EndpointMotionProperty q z chart := by
  classical
  intro M hM hrel a v hv
  obtain ⟨D, hD⟩ := hderiv a v hv
  refine ⟨motionCoefficients D M q, motionCoefficients_is_syzygy D M hM q hrel, ?_, ?_⟩
  · intro c hca i
    rw [eval_motionCoefficients D M q (z c) (fun j => hqz j c)]
    have hdq (j : Fin r) : eval (z c) (coefficientDerivation D (q j).val) = 0 := by
      rw [eval_coefficientDerivation_of_vanish D (z c) (q j).val (hqz j c)]
      simp [hD, hca]
    simp [hdq]
  · intro i
    rw [eval_motionCoefficients D M q (z a) (fun j => hqz j a)]
    have hdq (j : Fin r) : eval (z a) (coefficientDerivation D (q j).val) =
        -directionalEvaluation (q j).val (z a) v := by
      rw [eval_coefficientDerivation_of_vanish D (z a) (q j).val (hqz j a)]
      simp [hD, directionalEvaluation]
    rw [directionalEvaluation_matrixAction]
    simp [hdq, mul_neg, Finset.sum_neg_distrib, neg_mul]

end MovingRelations

section GenericPoints
variable (K : Type*) [Field K] (m p : ℕ)

/-- Formal differentiation with respect to one independent moving-point coordinate. -/
def genericCoordinateDerivation (a : Fin p) (j : Fin m) :
    Derivation K (GenericPointField K m p) (GenericPointField K m p) :=
  fractionDerivation (GenericPointField K m p) (pderiv (a,j))

@[simp] theorem genericCoordinateDerivation_coordinate
    (a b : Fin p) (j k : Fin m) :
    genericCoordinateDerivation K m p a j (genericPointCoordinates K m p (b,k)) =
      if b = a ∧ k = j then 1 else 0 := by
  classical
  simp [genericCoordinateDerivation, genericPointCoordinates, pderiv_X,
    Pi.single_apply, Prod.mk.injEq, eq_comm, and_comm, apply_ite]

/-- A tangent on the normalized affine chart defines a derivation of its rational function field. -/
def genericTangentDerivation (a : Fin p)
    (v : Fin (m+1) → GenericPointField K m p) :
    Derivation K (GenericPointField K m p) (GenericPointField K m p) :=
  ∑ j : Fin m, v j.castSucc • genericCoordinateDerivation K m p a j

theorem genericTangentDerivation_coordinate (a b : Fin p)
    (v : Fin (m+1) → GenericPointField K m p) (k : Fin m) :
    genericTangentDerivation K m p a v (genericPointCoordinates K m p (b,k)) =
      if b = a then v k.castSucc else 0 := by
  classical
  change (Derivation.coeFnAddMonoidHom
    (∑ j : Fin m, v j.castSucc • genericCoordinateDerivation K m p a j))
      (genericPointCoordinates K m p (b,k)) = _
  rw [map_sum, Finset.sum_apply]
  simp only [Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply,
    genericCoordinateDerivation_coordinate, smul_eq_mul]
  by_cases hba : b = a
  · simp [hba]
  · simp [hba]

/-- Exactly one universal point moves; every other universal point is stationary. -/
theorem genericTangentDerivation_chartPoint (a b : Fin p)
    (v : Fin (m+1) → GenericPointField K m p) (hv : v (Fin.last m) = 0)
    (j : Fin (m+1)) :
    genericTangentDerivation K m p a v
        (chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) b j) =
      if b = a then v j else 0 := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp [hv]
  · simp [genericTangentDerivation_coordinate]

/-- Lemma4.2's actual moving-point syzygies over the generic configuration field. -/
theorem genericPoint_endpointMotionProperty {d r : ℕ}
    (q : Fin r → Froberg.Forms (GenericPointField K m p) (m+1) d)
    (hqz : ∀ i a, eval
      (chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) a)
        (q i).val = 0) :
    EndpointMotionProperty q
      (chartPoint (GenericPointField K m p) (genericPointCoordinates K m p))
      (fun _ => Fin.last m) := by
  apply endpointMotionProperty_of_pointDerivations (K := K) q _ _ hqz
  intro a v hv
  refine ⟨genericTangentDerivation K m p a v, ?_⟩
  intro b j
  exact genericTangentDerivation_chartPoint K m p a b v hv j

end GenericPoints

end ESCtoFroberg
