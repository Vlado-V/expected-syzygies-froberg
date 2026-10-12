module

public import ESCtoFroberg.EndpointAlgebra

@[expose] public section

noncomputable section
namespace ESCtoFroberg

open Froberg MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {n d r p : ℕ}

/-- Evaluation of homogeneous forms at a fixed tuple of nonzero point representatives. -/
def formEvaluation (z : Fin p → Fin n → K) (e : ℕ) : Forms K n e →ₗ[K] (Fin p → K) where
  toFun f a := MvPolynomial.eval (z a) f.val
  map_add' f g := by ext a; simp
  map_smul' c f := by ext a; simp

/-- All coefficient evaluations, grouped into one generator block per point. -/
def endpointCoefficientEvaluation (z : Fin p → Fin n → K) :
    (Fin r → Forms K n d) →ₗ[K] (Fin p → Fin r → K) where
  toFun a j i := MvPolynomial.eval (z j) (a i).val
  map_add' a b := by ext j i; simp
  map_smul' c a := by ext j i; simp

/-- The evaluation map restricted to genuine endpoint syzygies. -/
def endpointSyzygyEvaluation (q : Fin r → Forms K n d) (z : Fin p → Fin n → K) :
    (endpointMultiplication q).ker →ₗ[K] (Fin p → Fin r → K) :=
  (endpointCoefficientEvaluation z).comp (endpointMultiplication q).ker.subtype

/-- The actual coefficient-evaluation image of endpoint syzygies. -/
def endpointEvaluationImage (q : Fin r → Forms K n d) (z : Fin p → Fin n → K) :
    Submodule K (Fin p → Fin r → K) := LinearMap.range (endpointSyzygyEvaluation q z)

/-- There are no nonzero image vectors supported on just one point block. -/
def NoSinglePointSupport (q : Fin r → Forms K n d) (z : Fin p → Fin n → K) : Prop :=
  ∀ a v, v ∈ endpointEvaluationImage q z → (∀ b, b ≠ a → ∀ i, v b i = 0) → v = 0

/-- The actual infinitesimal syzygies provided by moving one point of a generic configuration. -/
def EndpointMotionProperty (q : Fin r → Forms K n d) (z : Fin p → Fin n → K)
    (chart : Fin p → Fin n) : Prop :=
  ∀ M : Matrix (Fin r) (Fin r) K,
    (∀ i j, M i j = M j i) → endpointMultiplication q (matrixAction M q) = 0 →
    ∀ a v, v (chart a) = 0 →
      ∃ b : Fin r → Forms K n d,
        endpointMultiplication q b = 0 ∧
        (∀ c, c ≠ a → ∀ i, MvPolynomial.eval (z c) (b i).val = 0) ∧
        (∀ i, MvPolynomial.eval (z a) (b i).val =
          -2 * directionalEvaluation (matrixAction M q i).val (z a) v)

omit [CharZero K] in
/-- Independent generators spanning the vanishing space represent every zero-evaluation tuple by a matrix. -/
theorem exists_matrix_of_coefficientEvaluation_zero
    (q : Fin r → Forms K n d) (z : Fin p → Fin n → K)
    (hspan : (formEvaluation z d).ker ≤ Submodule.span K (Set.range q))
    (a : Fin r → Forms K n d) (ha : endpointCoefficientEvaluation z a = 0) :
    ∃ M : Matrix (Fin r) (Fin r) K, matrixAction M q = a := by
  classical
  have hrow : ∀ i, ∃ c : Fin r → K, ∑ j, c j • q j = a i := by
    intro i
    apply (Submodule.mem_span_range_iff_exists_fun K).mp
    apply hspan
    change formEvaluation z d (a i) = 0
    funext j
    exact congrFun (congrFun ha j) i
  choose M hM using hrow
  exact ⟨M, funext hM⟩

omit [CharZero K] in
/-- Constant Koszul boundaries have zero coefficient evaluations at common generator zeros. -/
theorem koszulSpace_le_ker_coefficientEvaluation
    (q : Fin r → Forms K n d) (z : Fin p → Fin n → K)
    (hqz : ∀ i a, MvPolynomial.eval (z a) (q i).val = 0) :
    koszulSpace q ≤ (endpointCoefficientEvaluation z).ker := by
  classical
  apply Submodule.span_le.mpr
  rintro _ ⟨t, rfl⟩
  change endpointCoefficientEvaluation z (koszulVector q t) = 0
  ext a i
  by_cases hi : i = t.val.1 <;> by_cases hj : i = t.val.2 <;>
    simp [endpointCoefficientEvaluation, koszulVector, hi, hj, hqz, ne_of_lt t.property, ne_of_gt t.property]

/-- The endpoint kernel is exactly the incoming constant Koszul space once generic motion is available. -/
theorem endpoint_kernel_eq_koszul_of_motion
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (z : Fin p → Fin n → K) (chart : Fin p → Fin n)
    (hd : 0 < d) (hchart : ∀ a, z a (chart a) ≠ 0)
    (hqz : ∀ i a, MvPolynomial.eval (z a) (q i).val = 0)
    (hspan : (formEvaluation z d).ker ≤ Submodule.span K (Set.range q))
    (hinj : Function.Injective (formEvaluation z (d - 1)))
    (hsupport : NoSinglePointSupport q z)
    (hmotion : EndpointMotionProperty q z chart) :
    (endpointSyzygyEvaluation q z).ker = incomingInKernel q := by
  classical
  apply le_antisymm
  · intro a ha
    have haz : endpointCoefficientEvaluation z a.val = 0 := ha
    obtain ⟨M, hM⟩ := exists_matrix_of_coefficientEvaluation_zero q z hspan a.val haz
    have hrel : endpointMultiplication q (matrixAction M q) = 0 := hM ▸ a.property
    have hsym := symmetricPart_is_syzygy q M hrel
    have hzero : symmetricPart M = 0 := by
      apply matrix_eq_zero_of_chart_tangent_vanishing q hq (symmetricPart M)
        hd z chart hchart hqz hinj
      intro i α v hv
      obtain ⟨b, hb, hbzero, hbvalue⟩ := hmotion (symmetricPart M)
        (symmetricPart_symmetric M) hsym α v hv
      have he : endpointCoefficientEvaluation z b ∈ endpointEvaluationImage q z :=
        ⟨⟨b,hb⟩,rfl⟩
      have hezero := hsupport α (endpointCoefficientEvaluation z b) he hbzero
      have hai : MvPolynomial.eval (z α) (b i).val = 0 :=
        congrFun (congrFun hezero α) i
      rw [hbvalue i] at hai
      exact (mul_eq_zero.mp hai).resolve_left (by norm_num)
    change a.val ∈ koszulSpace q
    have hb := matrixAction_sub_symmetric_mem_koszul M q
    rw [hzero] at hb
    have hz : matrixAction (0 : Matrix (Fin r) (Fin r) K) q = 0 := by
      ext i
      simp [matrixAction]
    simpa [koszulSpace,hM,hz] using hb
  · intro a ha
    exact koszulSpace_le_ker_coefficientEvaluation q z hqz ha

end ESCtoFroberg
