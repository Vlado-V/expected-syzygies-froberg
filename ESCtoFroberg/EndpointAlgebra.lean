module

public import Froberg.Koszul
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section

noncomputable section
namespace ESCtoFroberg

open MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {n d r : ℕ}

/-- Vanishing formal partials in characteristic zero force all nonconstant coefficients to vanish. -/
theorem coeff_eq_zero_of_all_pderiv_eq_zero (f : Froberg.Poly K n)
    (h : ∀ i, pderiv i f = 0) (m : Fin n →₀ ℕ) (hm : m ≠ 0) :
    f.coeff m = 0 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hx
    apply hm
    ext i
    simpa using not_exists.mp hx i
  have hs : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
    Finsupp.sub_add_single_one_cancel hi
  have hz := congrArg (fun p : Froberg.Poly K n => p.coeff (m - Finsupp.single i 1)) (h i)
  simp only [coeff_pderiv, hs, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hz
  let t : Fin n →₀ ℕ := m - Finsupp.single i (1 : ℕ)
  have hc : (t i : K) + 1 ≠ 0 := by
    norm_cast
  exact (mul_eq_zero.mp hz).resolve_right hc


/-- Positive-degree homogeneous polynomials with vanishing formal partials are zero. -/
theorem homogeneous_eq_zero_of_all_pderiv_eq_zero (f : Froberg.Poly K n)
    (hf : f.IsHomogeneous d) (hd : 0 < d) (h : ∀ i, pderiv i f = 0) : f = 0 := by
  classical
  apply MvPolynomial.ext
  intro m
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  by_cases hm : m = 0
  · subst m
    exact hf.coeff_eq_zero (by simpa using Nat.ne_of_lt hd)
  · exact coeff_eq_zero_of_all_pderiv_eq_zero f h m hm

omit [CharZero K] in
/-- The derivative of a degree-`d` homogeneous form has degree `d-1`. -/
theorem isHomogeneous_pderiv (f : Froberg.Poly K n)
    (hf : f.IsHomogeneous d) (i : Fin n) :
    (pderiv i f).IsHomogeneous (d - 1) := by
  classical
  intro m hm
  have he : m.degree + 1 = d := by
    have hcoeff : f.coeff (m + Finsupp.single i 1) ≠ 0 := by
      intro hz
      exact hm (by simp [coeff_pderiv, hz])
    have hd' : Finsupp.degree (m + Finsupp.single i 1) = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact hf hcoeff
    simpa only [map_add, Finsupp.degree_single] using hd'
  simp only [Pi.one_def, ← Finsupp.degree_eq_weight_one]
  omega

/-- Formal partial differentiation as a map between actual homogeneous polynomial spaces. -/
def partialForm (i : Fin n) : Froberg.Forms K n d →ₗ[K] Froberg.Forms K n (d - 1) where
  toFun f := ⟨pderiv i f.val, isHomogeneous_pderiv f.val f.property i⟩
  map_add' f g := Subtype.ext ((pderiv i).map_add f.val g.val)
  map_smul' c f := Subtype.ext ((pderiv i).map_smul c f.val)

/-- Injective evaluation of the derivatives gives the endpoint vanishing conclusion. -/
theorem homogeneous_eq_zero_of_pderiv_evaluation_zero (f : Froberg.Forms K n d)
    (hd : 0 < d) {p : ℕ} (z : Fin p → Fin n → K)
    (hinj : Function.Injective (fun g : Froberg.Forms K n (d - 1) =>
      fun a : Fin p => MvPolynomial.eval (z a) g.val))
    (h : ∀ i a, MvPolynomial.eval (z a) (pderiv i f.val) = 0) : f = 0 := by
  apply Subtype.ext
  apply homogeneous_eq_zero_of_all_pderiv_eq_zero f.val f.property hd
  intro i
  have he : partialForm i f = 0 := hinj (by
    funext a
    simpa [partialForm] using h i a)
  exact congrArg Subtype.val he

omit [CharZero K] in
/-- Evaluation of the radial Euler derivative. -/
theorem euler_evaluation (f : Froberg.Poly K n) (hf : f.IsHomogeneous d)
    (z : Fin n → K) :
    (∑ i, z i * MvPolynomial.eval z (pderiv i f)) = (d : K) * MvPolynomial.eval z f := by
  classical
  have h := congrArg (MvPolynomial.eval z) hf.sum_X_mul_pderiv
  simpa using h

/-- The coefficient value of a formal directional derivative. -/
def directionalEvaluation (f : Froberg.Poly K n) (z v : Fin n → K) : K :=
  ∑ i, v i * MvPolynomial.eval z (pderiv i f)

omit [CharZero K] in
/-- Affine-chart tangent directions together with the radial identity detect every partial. -/
theorem pderiv_evaluation_eq_zero_of_chart_tangents (f : Froberg.Poly K n)
    (hf : f.IsHomogeneous d) (z : Fin n → K) (k : Fin n) (hk : z k ≠ 0)
    (hz : MvPolynomial.eval z f = 0)
    (hv : ∀ v : Fin n → K, v k = 0 → directionalEvaluation f z v = 0) :
    ∀ j, MvPolynomial.eval z (pderiv j f) = 0 := by
  classical
  have hoff : ∀ j, j ≠ k → MvPolynomial.eval z (pderiv j f) = 0 := by
    intro j hj
    have h := hv (Pi.single j 1) (by simp [Ne.symm hj])
    simpa [directionalEvaluation, Pi.single_apply] using h
  have he := euler_evaluation f hf z
  rw [hz, mul_zero] at he
  have hsingle : (∑ j, z j * MvPolynomial.eval z (pderiv j f)) =
      z k * MvPolynomial.eval z (pderiv k f) := by
    apply Finset.sum_eq_single k
    · intro j hj hjk
      rw [hoff j hjk, mul_zero]
    · simp
  rw [hsingle] at he
  intro j
  by_cases hj : j = k
  · subst j
    exact (mul_eq_zero.mp he).resolve_left hk
  · exact hoff j hj

section MatrixRelations

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- A scalar relation matrix acting on an actual ordered generator family. -/
def matrixAction (M : Matrix (Fin r) (Fin r) K) (q : Fin r → V) : Fin r → V :=
  fun i => ∑ j, M i j • q j

/-- The elementary commutativity relation with two specified generator labels. -/
def elementaryBoundary (q : Fin r → V) (i j : Fin r) : Fin r → V :=
  Pi.single i (q j) - Pi.single j (q i)

/-- The symmetric part of a scalar relation matrix. -/
def symmetricPart (M : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin r) K :=
  fun i j => (M i j + M j i) / 2

/-- The skew part of a scalar relation matrix. -/
def skewPart (M : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin r) K :=
  fun i j => (M i j - M j i) / 2

omit [CharZero K] in
@[simp] theorem symmetricPart_symmetric (M : Matrix (Fin r) (Fin r) K) (i j : Fin r) :
    symmetricPart M i j = symmetricPart M j i := by
  simp [symmetricPart, add_comm]

@[simp] theorem skewPart_skew (M : Matrix (Fin r) (Fin r) K) (i j : Fin r) :
    skewPart M j i = -skewPart M i j := by
  simp only [skewPart]
  ring

theorem matrix_symmetric_add_skew (M : Matrix (Fin r) (Fin r) K) :
    M = symmetricPart M + skewPart M := by
  ext i j
  simp only [Matrix.add_apply, symmetricPart, skewPart]
  field_simp
  ring

omit [CharZero K] in
theorem matrixAction_add (M N : Matrix (Fin r) (Fin r) K) (q : Fin r → V) :
    matrixAction (M + N) q = matrixAction M q + matrixAction N q := by
  classical
  funext i
  simp [matrixAction, add_smul, Finset.sum_add_distrib]

theorem matrixAction_eq_symmetric_add_skew (M : Matrix (Fin r) (Fin r) K)
    (q : Fin r → V) :
    matrixAction M q = matrixAction (symmetricPart M) q + matrixAction (skewPart M) q := by
  calc
    matrixAction M q = matrixAction (symmetricPart M + skewPart M) q := congrArg (fun A => matrixAction A q) (matrix_symmetric_add_skew M)
    _ = _ := matrixAction_add _ _ _

omit [CharZero K] in
theorem elementaryBoundary_mem_koszul (q : Fin r → V) (i j : Fin r) :
    elementaryBoundary q i j ∈ Submodule.span K (Set.range (Froberg.koszulVector q)) := by
  classical
  rcases lt_trichotomy i j with hij | hij | hij
  · have h : elementaryBoundary q i j = Froberg.koszulVector q ⟨(i,j),hij⟩ := by
      funext a
      simp [elementaryBoundary, Froberg.koszulVector, Pi.single_apply]
    rw [h]
    exact Submodule.subset_span ⟨_, rfl⟩
  · subst j
    simp [elementaryBoundary]
  · have h : elementaryBoundary q i j = -Froberg.koszulVector q ⟨(j,i),hij⟩ := by
      funext a
      simp [elementaryBoundary, Froberg.koszulVector, Pi.single_apply]
    rw [h]
    exact Submodule.neg_mem _ (Submodule.subset_span ⟨_, rfl⟩)

/-- Every skew scalar matrix gives precisely a constant Koszul boundary. -/
theorem matrixAction_mem_koszul_of_skew (M : Matrix (Fin r) (Fin r) K)
    (hM : ∀ i j, M j i = -M i j) (q : Fin r → V) :
    matrixAction M q ∈ Submodule.span K (Set.range (Froberg.koszulVector q)) := by
  classical
  have hrep : matrixAction M q = ∑ i, ∑ j, (M i j / 2) • elementaryBoundary q i j := by
    funext a
    simp only [matrixAction, elementaryBoundary, Finset.sum_apply, Pi.smul_apply,
      Pi.sub_apply, Pi.single_apply, smul_sub, smul_ite, smul_zero,
      Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hfirst : (∑ i : Fin r, ∑ j : Fin r, if a = i then (M i j / 2) • q j else 0) =
        ∑ j, (M a j / 2) • q j := by
      rw [Finset.sum_comm]
      simp
    rw [hfirst, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hM a j, ← sub_smul]
    congr 1
    field_simp
    ring
  rw [hrep]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  exact Submodule.smul_mem _ _ (elementaryBoundary_mem_koszul q i j)

/-- The original relation vector and its symmetric part have the same class modulo Koszul. -/
theorem matrixAction_sub_symmetric_mem_koszul (M : Matrix (Fin r) (Fin r) K)
    (q : Fin r → V) :
    matrixAction M q - matrixAction (symmetricPart M) q ∈
      Submodule.span K (Set.range (Froberg.koszulVector q)) := by
  rw [matrixAction_eq_symmetric_add_skew, add_sub_cancel_left]
  exact matrixAction_mem_koszul_of_skew (skewPart M) (skewPart_skew M) q

omit [CharZero K] in
theorem matrix_eq_zero_of_action_eq_zero (q : Fin r → V) (hq : LinearIndependent K q)
    (M : Matrix (Fin r) (Fin r) K) (hM : matrixAction M q = 0) : M = 0 := by
  classical
  ext i j
  have hi : ∑ a, M i a • q a = 0 := congrFun hM i
  exact Fintype.linearIndependent_iff.mp hq (M i) hi j

end MatrixRelations

/-- The symmetric representative remains a genuine polynomial syzygy. -/
theorem symmetricPart_is_syzygy (q : Fin r → Froberg.Forms K n d)
    (M : Matrix (Fin r) (Fin r) K)
    (hM : Froberg.endpointMultiplication q (matrixAction M q) = 0) :
    Froberg.endpointMultiplication q (matrixAction (symmetricPart M) q) = 0 := by
  have hskew := Froberg.kernel_contains_koszul q
    (matrixAction_mem_koszul_of_skew (skewPart M) (skewPart_skew M) q)
  change Froberg.endpointMultiplication q (matrixAction (skewPart M) q) = 0 at hskew
  rw [matrixAction_eq_symmetric_add_skew, map_add, hskew, add_zero] at hM
  exact hM

/-- The final algebraic step of the moving-point argument. -/
theorem matrix_eq_zero_of_derivative_evaluation_zero
    (q : Fin r → Froberg.Forms K n d) (hq : LinearIndependent K q)
    (M : Matrix (Fin r) (Fin r) K) (hd : 0 < d) {p : ℕ}
    (z : Fin p → Fin n → K)
    (hinj : Function.Injective (fun g : Froberg.Forms K n (d - 1) =>
      fun a : Fin p => MvPolynomial.eval (z a) g.val))
    (h : ∀ i j a, MvPolynomial.eval (z a)
      (pderiv j (matrixAction M q i).val) = 0) : M = 0 := by
  apply matrix_eq_zero_of_action_eq_zero q hq M
  funext i
  exact homogeneous_eq_zero_of_pderiv_evaluation_zero (matrixAction M q i) hd z hinj (h i)

/-- A zero-evaluation symmetric relation is zero once all its moving-point tangent values vanish. -/
theorem matrix_eq_zero_of_chart_tangent_vanishing
    (q : Fin r → Froberg.Forms K n d) (hq : LinearIndependent K q)
    (M : Matrix (Fin r) (Fin r) K) (hd : 0 < d) {p : ℕ}
    (z : Fin p → Fin n → K) (chart : Fin p → Fin n)
    (hchart : ∀ a, z a (chart a) ≠ 0)
    (hqz : ∀ i a, MvPolynomial.eval (z a) (q i).val = 0)
    (hinj : Function.Injective (fun g : Froberg.Forms K n (d - 1) =>
      fun a : Fin p => MvPolynomial.eval (z a) g.val))
    (htan : ∀ i a v, v (chart a) = 0 →
      directionalEvaluation (matrixAction M q i).val (z a) v = 0) : M = 0 := by
  apply matrix_eq_zero_of_derivative_evaluation_zero q hq M hd z hinj
  intro i j a
  apply pderiv_evaluation_eq_zero_of_chart_tangents (matrixAction M q i).val
    (matrixAction M q i).property (z a) (chart a) (hchart a)
  · simp [matrixAction, hqz]
  · exact htan i a

section DifferentiatingRelations

variable {A : Type*} [CommRing A] [Algebra K A]

/-- Matrix action when the entries themselves vary polynomially in parameters. -/
def ringMatrixAction (M : Matrix (Fin r) (Fin r) A) (q : Fin r → A) : Fin r → A :=
  fun i => ∑ j, M i j * q j

/-- The genuine quadratic polynomial relation for a varying family. -/
def quadraticRelation (M : Matrix (Fin r) (Fin r) A) (q : Fin r → A) : A :=
  ∑ i, q i * ringMatrixAction M q i

/-- The relation coefficient produced by differentiating both its matrix and its generators. -/
def differentiatedRelation (D : Derivation K A A)
    (M : Matrix (Fin r) (Fin r) A) (q : Fin r → A) : Fin r → A :=
  fun i => (∑ j, D (M i j) * q j) + 2 * (∑ j, M i j * D (q j))

omit [CharZero K] in
/-- The exact first-order identity, including the derivative of the relation matrix. -/
theorem deriv_quadraticRelation (D : Derivation K A A)
    (M : Matrix (Fin r) (Fin r) A) (hM : ∀ i j, M i j = M j i) (q : Fin r → A) :
    D (quadraticRelation M q) = ∑ i, q i * differentiatedRelation D M q i := by
  classical
  have hswap : (∑ i, ∑ j, D (q i) * M i j * q j) =
      ∑ i, ∑ j, q i * M i j * D (q j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hM j i]
    ring
  calc
    D (quadraticRelation M q) = ∑ i, ∑ j, D (q i * M i j * q j) := by
      simp [quadraticRelation, ringMatrixAction, Finset.mul_sum, mul_assoc]
    _ = ∑ i, ∑ j, (D (q i) * M i j * q j +
        q i * D (M i j) * q j + q i * M i j * D (q j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Derivation.leibniz, smul_eq_mul]
      ring
    _ = (∑ i, ∑ j, D (q i) * M i j * q j) +
      (∑ i, ∑ j, q i * D (M i j) * q j) +
      (∑ i, ∑ j, q i * M i j * D (q j)) := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, q i * D (M i j) * q j) +
        2 * (∑ i, ∑ j, q i * M i j * D (q j)) := by
          rw [hswap]
          ring
    _ = ∑ i, q i * differentiatedRelation D M q i := by
      simp only [differentiatedRelation, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      · apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring

omit [CharZero K] in
/-- Differentiating a varying symmetric quadratic relation gives an actual syzygy. -/
theorem differentiatedRelation_is_syzygy (D : Derivation K A A)
    (M : Matrix (Fin r) (Fin r) A) (hM : ∀ i j, M i j = M j i) (q : Fin r → A)
    (hrel : quadraticRelation M q = 0) :
    (∑ i, q i * differentiatedRelation D M q i) = 0 := by
  rw [← deriv_quadraticRelation D M hM q, hrel, map_zero]

omit [CharZero K] in
/-- At a zero of all generators, the matrix derivative term drops out. -/
theorem map_differentiatedRelation_of_generator_vanish (D : Derivation K A A)
    (M : Matrix (Fin r) (Fin r) A) (q : Fin r → A) (φ : A →+* K)
    (hq : ∀ j, φ (q j) = 0) (i : Fin r) :
    φ (differentiatedRelation D M q i) =
      2 * (∑ j, φ (M i j) * φ (D (q j))) := by
  simp only [differentiatedRelation, map_add, map_sum, map_mul, hq, mul_zero, Finset.sum_const_zero, zero_add]
  congr 1
  exact map_ofNat φ 2

omit [CharZero K] in
/-- At a stationary common zero, the entire differentiated coefficient evaluation is zero. -/
theorem map_differentiatedRelation_eq_zero (D : Derivation K A A)
    (M : Matrix (Fin r) (Fin r) A) (q : Fin r → A) (φ : A →+* K)
    (hq : ∀ j, φ (q j) = 0) (hdq : ∀ j, φ (D (q j)) = 0) (i : Fin r) :
    φ (differentiatedRelation D M q i) = 0 := by
  rw [map_differentiatedRelation_of_generator_vanish D M q φ hq i]
  simp [hdq]

omit [CharZero K] in
/-- At the moving common zero, differentiated coefficient evaluation is minus twice its tangent value. -/
theorem map_differentiatedRelation_moving_point (D : Derivation K A A)
    (M : Matrix (Fin r) (Fin r) A) (q : Fin r → A) (φ : A →+* K)
    (hq : ∀ j, φ (q j) = 0) (w : Fin r → K)
    (hdq : ∀ j, φ (D (q j)) = -w j) (i : Fin r) :
    φ (differentiatedRelation D M q i) =
      -2 * (∑ j, φ (M i j) * w j) := by
  rw [map_differentiatedRelation_of_generator_vanish D M q φ hq i]
  simp only [hdq, mul_neg, Finset.sum_neg_distrib, mul_neg, neg_mul]

end DifferentiatingRelations

end ESCtoFroberg
