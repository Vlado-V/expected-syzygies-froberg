module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.MvPolynomial.Funext
public import Froberg.Generic
public import Froberg.Prefix
public import Froberg.GenericHilbertDimension
public import ESCtoFroberg.HomogeneousCoordinates
public import ESCtoFroberg.ClearDenominators
public import ESCtoFroberg.GeneralPoints
public import ESCtoFroberg.Statement
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic

@[expose] public section

noncomputable section
namespace ESCtoFroberg
namespace GenericTransfer
open Module MvPolynomial

private theorem dual_apply_sum {F μ : Type*} [Field F] [Fintype μ] [DecidableEq μ]
    (l : (μ → F) →ₗ[F] F) (x : μ → F) :
    l x = ∑ i, l (Pi.single i 1) * x i := by
  have he := congrArg l (pi_eq_sum_univ' x)
  simp only [map_sum, map_smul, smul_eq_mul] at he
  exact he.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _)

/-- A rank factorization together with a full-rank test, without a choice of pivots. -/
theorem rankFactorization {F μ ν : Type*} [Field F] [Fintype μ] [Fintype ν]
    [DecidableEq μ] [DecidableEq ν] (A : Matrix μ ν F) :
    ∃ B : Matrix μ (Fin A.rank) F, ∃ C : Matrix (Fin A.rank) ν F,
    ∃ L : Matrix (Fin A.rank) μ F, ∃ R : Matrix ν (Fin A.rank) F,
      A = B * C ∧ L * A * R = 1 := by
  let U := A.mulVecLin.range
  let b := Module.finBasis F U
  have hb : LinearIndependent F (fun i => (b i).val) :=
    b.linearIndependent.map' U.subtype (LinearMap.ker_eq_bot.mpr U.injective_subtype)
  obtain ⟨dual, hdual⟩ := Froberg.exists_coordinate_functionals (fun i => (b i).val) hb
  have hpre : ∀ i, ∃ x, A.mulVecLin x = (b i).val := fun i => (b i).property
  choose x hx using hpre
  let B : Matrix μ (Fin A.rank) F := fun i j => (b j).val i
  let C : Matrix (Fin A.rank) ν F := fun i j =>
    b.equivFun ⟨A.col j, by
      refine ⟨Pi.single j 1, ?_⟩
      simp [Matrix.mulVec_single]⟩ i
  let L : Matrix (Fin A.rank) μ F := fun i j => dual i (Pi.single j 1)
  let R : Matrix ν (Fin A.rank) F := fun i j => x j i
  have hBC : B * C = A := by
    ext i j
    have he := congrArg (fun y : U => y.val i) (b.sum_equivFun
      ⟨A.col j, by refine ⟨Pi.single j 1, ?_⟩; simp [Matrix.mulVec_single]⟩)
    change (∑ k, (b k).val i * C k j) = A i j
    simpa only [C, Matrix.col_apply, Submodule.coe_sum, Submodule.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using he
  have hLB : L * B = 1 := by
    ext i j
    have he := dual_apply_sum (dual i) (b j).val
    rw [hdual i j] at he
    change (∑ k, dual i (Pi.single k 1) * (b j).val k) = if i = j then 1 else 0
    exact he.symm
  have hAR : A * R = B := by
    ext i j
    exact congrFun (hx j) i
  refine ⟨B, C, L, R, hBC.symm, ?_⟩
  rw [Matrix.mul_assoc, hAR, hLB]

/-- Finite families of rational functions admit one nonzero denominator. -/
theorem clearFractionFamily {A F ι : Type*} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Finite ι] (f : ι → F) :
    ∃ c : A, c ≠ 0 ∧ ∃ g : ι → A, ∀ i,
      algebraMap A F (g i) = algebraMap A F c * f i := by
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors A) f
  have hex : ∀ i, ∃ a : A, algebraMap A F a = algebraMap A F (c : A) * f i := by
    intro i
    simpa only [IsLocalization.IsInteger, RingHom.mem_rangeS, Algebra.smul_def] using hc i
  choose g hg using hex
  exact ⟨c, nonZeroDivisors.coe_ne_zero c, g, hg⟩

private theorem map_matrix_smul {A F μ ν : Type*} [CommRing A] [CommRing F]
    (f : A →+* F) (c : A) (M : Matrix μ ν A) :
    (c • M).map f = f c • M.map f := by
  ext i j
  simp [Matrix.map_apply, smul_eq_mul]

/-- Integral polynomial certificates for both sides of a matrix-rank equality. -/
theorem rankIntegralCertificate {A F μ ν : Type*} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Fintype μ] [Fintype ν]
    [DecidableEq μ] [DecidableEq ν] (M : Matrix μ ν A) :
    ∃ c : A, c ≠ 0 ∧
    ∃ B : Matrix μ (Fin (M.map (algebraMap A F)).rank) A,
    ∃ C : Matrix (Fin (M.map (algebraMap A F)).rank) ν A,
    ∃ L : Matrix (Fin (M.map (algebraMap A F)).rank) μ A,
    ∃ R : Matrix ν (Fin (M.map (algebraMap A F)).rank) A,
      (c * c) • M = B * C ∧ L * M * R = (c * c) • 1 := by
  let f := algebraMap A F
  let MF := M.map f
  obtain ⟨B, C, L, R, hBC, hLR⟩ := rankFactorization MF
  let values : ((μ × Fin MF.rank) ⊕ (Fin MF.rank × ν)) ⊕
      ((Fin MF.rank × μ) ⊕ (ν × Fin MF.rank)) → F :=
    Sum.elim (Sum.elim (fun ij => B ij.1 ij.2) (fun ij => C ij.1 ij.2))
      (Sum.elim (fun ij => L ij.1 ij.2) (fun ij => R ij.1 ij.2))
  obtain ⟨c, hc, g, hg⟩ := clearFractionFamily (A := A) values
  let B' : Matrix μ (Fin MF.rank) A := fun i j => g (.inl (.inl (i,j)))
  let C' : Matrix (Fin MF.rank) ν A := fun i j => g (.inl (.inr (i,j)))
  let L' : Matrix (Fin MF.rank) μ A := fun i j => g (.inr (.inl (i,j)))
  let R' : Matrix ν (Fin MF.rank) A := fun i j => g (.inr (.inr (i,j)))
  have hB : B'.map f = f c • B := by ext i j; exact hg (.inl (.inl (i,j)))
  have hC : C'.map f = f c • C := by ext i j; exact hg (.inl (.inr (i,j)))
  have hL : L'.map f = f c • L := by ext i j; exact hg (.inr (.inl (i,j)))
  have hR : R'.map f = f c • R := by ext i j; exact hg (.inr (.inr (i,j)))
  refine ⟨c, hc, B', C', L', R', ?_, ?_⟩
  · apply Matrix.map_injective (IsFractionRing.injective A F)
    change ((c * c) • M).map f = (B' * C').map f
    rw [map_matrix_smul, Matrix.map_mul, hB, hC, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, ← hBC, map_mul]
  · apply Matrix.map_injective (IsFractionRing.injective A F)
    change (L' * M * R').map f = ((c * c) • (1 : Matrix _ _ A)).map f
    rw [map_matrix_smul, Matrix.map_one, Matrix.map_mul, Matrix.map_mul,
      hL, hR, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
    change (f c * f c) • (L * MF * R) = f (c * c) • 1
    rw [hLR, map_mul]
    all_goals simp

/-- Away from the certificate denominator, every field specialization has exactly the
rank of the matrix over the fraction field. -/
theorem rank_specialize_of_certificate {A F K μ ν : Type*} [CommRing A] [IsDomain A]
    [Field F] [Algebra A F] [IsFractionRing A F] [Field K]
    [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
    (M : Matrix μ ν A) :
    ∃ c : A, c ≠ 0 ∧ ∀ f : A →+* K, f c ≠ 0 →
      (M.map f).rank = (M.map (algebraMap A F)).rank := by
  obtain ⟨c, hc, B, C, L, R, hBC, hLR⟩ := rankIntegralCertificate (F := F) M
  refine ⟨c, hc, ?_⟩
  intro f hf
  have hu : (f c * f c) • M.map f = B.map f * C.map f := by
    have h := congrArg (fun M => M.map f) hBC
    simpa only [map_matrix_smul, Matrix.map_mul, map_mul] using h
  have hl : L.map f * M.map f * R.map f = (f c * f c) • 1 := by
    have h := congrArg (fun M => M.map f) hLR
    simpa only [map_matrix_smul, Matrix.map_mul, map_mul, Matrix.map_one,
      map_zero, map_one] using h
  have hscalar : f c * f c ∈ nonZeroDivisors K :=
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hf hf)
  apply le_antisymm
  · have hr := (Matrix.rank_mul_le_left (B.map f) (C.map f)).trans
      (Matrix.rank_le_card_width (B.map f))
    rw [← hu, Matrix.rank_smul_of_mem_nonZeroDivisors _ hscalar] at hr
    simpa only [Fintype.card_fin] using hr
  · have hr := (Matrix.rank_mul_le_left (L.map f * M.map f) (R.map f)).trans
      (Matrix.rank_mul_le_right (L.map f) (M.map f))
    rw [hl, Matrix.rank_smul_of_mem_nonZeroDivisors _ hscalar, Matrix.rank_one] at hr
    simpa only [Fintype.card_fin] using hr

/-- Universal-coordinate matrix rank is realized on a nonempty principal open over K. -/
theorem polynomialMatrix_rank_principalOpen {K F σ μ ν : Type*} [Field K] [Infinite K]
    [Field F] [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]
    (M : Matrix μ ν (MvPolynomial σ K)) :
    ∃ D : MvPolynomial σ K, (∃ a : σ → K, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 →
      (M.map (eval a)).rank = (M.map (algebraMap (MvPolynomial σ K) F)).rank := by
  obtain ⟨D, hD, hgood⟩ := rank_specialize_of_certificate (F := F) (K := K) M
  refine ⟨D, ?_, fun a ha => hgood (eval a) ha⟩
  by_contra! hn
  exact hD (MvPolynomial.funext hn)

/-- A homogeneous polynomial family after a coefficient-ring specialization. -/
def mappedForms {A F ι : Type*} [CommRing A] [Field F] {n d : ℕ}
    (Q : ι → MvPolynomial (Fin n) A) (hQ : ∀ i, (Q i).IsHomogeneous d)
    (f : A →+* F) : ι → Forms F n d :=
  fun i => ⟨MvPolynomial.map f (Q i), (hQ i).map f⟩

/-- Coefficient matrix over the original parameter ring. -/
def homogeneousCoefficientMatrix {A ι : Type*} [CommRing A] (n d : ℕ)
    (Q : ι → MvPolynomial (Fin n) A) : Matrix (Sym (Fin n) d) ι A :=
  fun s i => (Q i).coeff (Froberg.exponentEquiv n d s).val

/-- The coefficient matrix computes the actual dimension of the family span after
any specialization. -/
theorem homogeneousCoefficientMatrix_rank {A F ι : Type*} [CommRing A] [Field F]
    [Fintype ι] [DecidableEq ι] {n d : ℕ}
    (Q : ι → MvPolynomial (Fin n) A) (hQ : ∀ i, (Q i).IsHomogeneous d)
    (f : A →+* F) :
    ((homogeneousCoefficientMatrix n d Q).map f).rank =
      finrank F (Submodule.span F (Set.range (mappedForms Q hQ f))) := by
  classical
  let b := Pi.basisFun F ι
  let L := b.constr F (mappedForms Q hQ f)
  have heq : (homogeneousCoefficientMatrix n d Q).map f =
      LinearMap.toMatrix b (Froberg.formsBasis F n d) L := by
    ext s i
    change f ((Q i).coeff (Froberg.exponentEquiv n d s).val) = _
    rw [LinearMap.toMatrix_apply, show L (b i) = mappedForms Q hQ f i by
      exact b.constr_basis F _ i]
    rw [← Basis.equivFun_apply, formsBasis_equivFun_eq_coeff]
    exact (MvPolynomial.coeff_map f (Q i) _).symm
  rw [heq, Matrix.rank_eq_finrank_range_toLin _ (Froberg.formsBasis F n d) b,
    Matrix.toLin_toMatrix]
  rw [show L.range = Submodule.span F (Set.range (mappedForms Q hQ f)) from b.constr_range F]

/-- Multiplication by the generators, encoded without choosing any rational basis. -/
def homogeneousMultiplicationMatrix {A : Type*} [CommRing A] {n d r : ℕ}
    (Q : Fin r → MvPolynomial (Fin n) A) (e : ℕ) :
    Matrix (Sym (Fin n) (d + e)) (Fin r × Sym (Fin n) e) A :=
  fun s ib => ((Q ib.1) * monomial (Froberg.exponentEquiv n e ib.2).val 1).coeff
    (Froberg.exponentEquiv n (d + e) s).val

/-- Monomial products span the full multiplication image. -/
theorem range_prefix_eq_span_products {F : Type*} [Field F] {n d r : ℕ}
    (q : Fin r → Forms F n d) (e : ℕ) :
    (Froberg.prefixMultiplication q e).range = Submodule.span F
      (Set.range (fun ib : Fin r × Sym (Fin n) e =>
        Froberg.gradedMultiplication (q ib.1) (Froberg.formsBasis F n e ib.2))) := by
  classical
  let P := Submodule.span F (Set.range (fun ib : Fin r × Sym (Fin n) e =>
    Froberg.gradedMultiplication (q ib.1) (Froberg.formsBasis F n e ib.2)))
  apply le_antisymm
  · rintro f ⟨a, rfl⟩
    have him (i : Fin r) : (Froberg.gradedMultiplication (q i)).range ≤ P := by
      rw [← Submodule.map_top, ← (Froberg.formsBasis F n e).span_eq, LinearMap.map_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨s,rfl⟩,rfl⟩
      exact Submodule.subset_span ⟨(i,s),rfl⟩
    simp only [Froberg.prefixMultiplication, LinearMap.sum_apply,
      LinearMap.comp_apply, LinearMap.proj_apply]
    change (∑ i, Froberg.gradedMultiplication (q i) (a i)) ∈ P
    apply Submodule.sum_mem
    intro i _
    exact him i ⟨a i, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,s⟩,rfl⟩
    refine ⟨Pi.single i (Froberg.formsBasis F n e s), ?_⟩
    apply Subtype.ext
    rw [Froberg.prefixMultiplication_val]
    have hval (j : Fin r) : (Pi.single (M := fun _ : Fin r => Forms F n e) i (Froberg.formsBasis F n e s) j).val =
        if i = j then (Froberg.formsBasis F n e s).val else 0 := by
      by_cases h : i = j <;> simp [h]
    simp only [hval, mul_ite, mul_zero]
    simp [Froberg.gradedMultiplication]

/-- The polynomial multiplication matrix computes the actual specialized rank. -/
theorem homogeneousMultiplicationMatrix_rank {A F : Type*} [CommRing A] [Field F]
    {n d r : ℕ} (Q : Fin r → MvPolynomial (Fin n) A)
    (hQ : ∀ i, (Q i).IsHomogeneous d) (e : ℕ) (f : A →+* F) :
    ((homogeneousMultiplicationMatrix (d := d) Q e).map f).rank =
      finrank F (Froberg.prefixMultiplication (mappedForms Q hQ f) e).range := by
  classical
  let P : (Fin r × Sym (Fin n) e) → MvPolynomial (Fin n) A := fun ib =>
    Q ib.1 * monomial (Froberg.exponentEquiv n e ib.2).val 1
  have hP (ib : Fin r × Sym (Fin n) e) : (P ib).IsHomogeneous (d + e) :=
    (hQ ib.1).mul (isHomogeneous_monomial _ (by
      simpa only [Finsupp.degree_apply] using (Froberg.exponentEquiv n e ib.2).property))
  have hmat : homogeneousMultiplicationMatrix (d := d) Q e =
      homogeneousCoefficientMatrix n (d + e) P := rfl
  rw [hmat, homogeneousCoefficientMatrix_rank P hP f, range_prefix_eq_span_products]
  have heq : mappedForms P hP f = fun ib : Fin r × Sym (Fin n) e =>
      Froberg.gradedMultiplication (mappedForms Q hQ f ib.1)
        (Froberg.formsBasis F n e ib.2) := by
    funext ib
    apply Subtype.ext
    simp [mappedForms, P, Froberg.gradedMultiplication, formsBasis_val_monomial]
  rw [heq]

/-- A common nonzero scaling of all generators leaves their actual ideal span unchanged. -/
theorem familySpace_smul_eq {F : Type*} [Field F] {n d r : ℕ}
    (q : Fin r → Forms F n d) (c : F) (hc : c ≠ 0) :
    Froberg.familySpace (c • q) = Froberg.familySpace q := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hm := Submodule.smul_mem (Froberg.familySpace (c • q)) c⁻¹
      (Submodule.subset_span (s := Set.range (fun i => (c • q i).val)) ⟨i,rfl⟩)
    simpa [inv_smul_smul₀ hc] using hm

/-- The Hilbert dimension of any rational homogeneous family is realized by actual
K-coefficient forms on a nonempty open after clearing denominators. -/
theorem rationalFamily_hilbert_principalOpen {K F σ : Type*} [Field K] [Infinite K]
    [Field F] [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    {n d r : ℕ} (hn : 0 < n) (q : Fin r → Forms F n d) (e : ℕ) :
    ∃ Q : Fin r → MvPolynomial (Fin n) (MvPolynomial σ K),
    ∃ hQ : ∀ i, (Q i).IsHomogeneous d,
    ∃ E : MvPolynomial σ K, (∃ a : σ → K, eval a E ≠ 0) ∧
      ∀ a, eval a E ≠ 0 →
      Froberg.hilbertFunction (Froberg.familySpace (mappedForms Q hQ (eval a))) (d + e) =
        Froberg.hilbertFunction (Froberg.familySpace q) (d + e) := by
  obtain ⟨D,hD,Q,hQ,hmap⟩ := homogeneous_family_clear_denominators
    (A := MvPolynomial σ K) d (fun i => (q i).val) (fun i => (q i).property)
  let η := algebraMap (MvPolynomial σ K) F
  have hD' : η D ≠ 0 := fun hz => hD
    (IsFractionRing.injective (MvPolynomial σ K) F (hz.trans (map_zero η).symm))
  have hfamily : mappedForms Q hQ η = η D • q := by
    funext i
    apply Subtype.ext
    simpa [mappedForms, MvPolynomial.smul_eq_C_mul] using hmap i
  obtain ⟨E,hE,hgood⟩ := polynomialMatrix_rank_principalOpen (F := F)
    (homogeneousMultiplicationMatrix (d := d) Q e)
  refine ⟨Q,hQ,E,hE,?_⟩
  intro a ha
  have hr := hgood a ha
  rw [homogeneousMultiplicationMatrix_rank Q hQ e (eval a),
    homogeneousMultiplicationMatrix_rank Q hQ e η, hfamily] at hr
  have hK := Froberg.prefix_hilbert_add_rank (e := e) hn (mappedForms Q hQ (eval a))
  have hF := Froberg.prefix_hilbert_add_rank (e := e) hn (η D • q)
  rw [familySpace_smul_eq q (η D) hD'] at hF
  omega

/-- Every actual rational-field homogeneous family has a K-valued family with the
same degree Hilbert dimension. -/
theorem rationalFamily_hilbert_witness {K F σ : Type*} [Field K] [Infinite K]
    [Field F] [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    {n d r : ℕ} (hn : 0 < n) (q : Fin r → Forms F n d) (e : ℕ) :
    ∃ qK : Fin r → Forms K n d,
      Froberg.hilbertFunction (Froberg.familySpace qK) (d + e) =
        Froberg.hilbertFunction (Froberg.familySpace q) (d + e) := by
  obtain ⟨Q,hQ,E,⟨a,ha⟩,hgood⟩ := rationalFamily_hilbert_principalOpen (K := K) (F := F) (σ := σ) hn q e
  exact ⟨mappedForms Q hQ (eval a), hgood a ha⟩

/-- Descent gives the desired numerical comparison with the generic K-family. -/
theorem genericHilbertDimension_le_rationalFamily {K F σ : Type*} [Field K] [Infinite K]
    [Field F] [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    {n d r : ℕ} (hn : 0 < n) (q : Fin r → Forms F n d) (e : ℕ) :
    Froberg.genericHilbertDimension K n d r (d + e) ≤
      Froberg.hilbertFunction (Froberg.familySpace q) (d + e) := by
  obtain ⟨qK,hqK⟩ := rationalFamily_hilbert_witness (K := K) (F := F) (σ := σ) hn q e
  let a := Froberg.coefficientCoordinates qK
  have hforms : Froberg.coefficientForms K n d r a = qK :=
    (Froberg.coefficientCoordinates (K := K) (n := n) (d := d) (r := r)).symm_apply_apply qK
  have hmin := Froberg.genericHilbertDimension_le K n d r (d + e) a
  change Froberg.genericHilbertDimension K n d r (d + e) ≤
    Froberg.hilbertFunction (Froberg.familySpace (Froberg.coefficientForms K n d r a)) (d + e) at hmin
  rw [hforms, hqK] at hmin
  exact hmin

/-- Matrix of degree evaluation before passage to the universal point field. -/
def pointEvaluationMatrix (K : Type*) [Field K] (m p d : ℕ) :
    Matrix (Fin p) (Sym (Fin (m + 1)) d) (GenericPointRing K m p) :=
  fun i s => eval (pointRingChart K m p i)
    (monomial (Froberg.exponentEquiv (m + 1) d s).val 1)

/-- The universal point-evaluation matrix represents the actual linear map. -/
theorem pointEvaluationMatrix_generic {K : Type*} [Field K] (m p d : ℕ) :
    (pointEvaluationMatrix K m p d).map
      (algebraMap (GenericPointRing K m p) (GenericPointField K m p)) =
      LinearMap.toMatrix (Froberg.formsBasis (GenericPointField K m p) (m + 1) d)
        (Pi.basisFun (GenericPointField K m p) (Fin p))
        (pointEvaluation (GenericPointField K m p) (genericPointCoordinates K m p) d) := by
  classical
  ext i s
  rw [LinearMap.toMatrix_apply]
  simp only [← Basis.equivFun_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
    pointEvaluation_apply, formsBasis_val_monomial]
  have he := eval_generic_map (K := K) (m := m) (p := p)
    (monomial (Froberg.exponentEquiv (m + 1) d s).val 1) i
  simpa only [pointEvaluationMatrix, Matrix.map_apply, map_monomial, map_one] using he.symm

/-- The same polynomial matrix represents every actual K-point evaluation. -/
theorem pointEvaluationMatrix_specialized {K : Type*} [Field K] {m p : ℕ}
    (a : PointCoordinates K m p) (d : ℕ) :
    (pointEvaluationMatrix K m p d).map (eval a) =
      LinearMap.toMatrix (Froberg.formsBasis K (m + 1) d) (Pi.basisFun K (Fin p))
        (pointEvaluation K a d) := by
  classical
  ext i s
  rw [LinearMap.toMatrix_apply]
  simp only [← Basis.equivFun_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply,
    pointEvaluation_apply, formsBasis_val_monomial]
  have he := eval_specialized_map
    (monomial (Froberg.exponentEquiv (m + 1) d s).val 1) a i
  simpa only [pointEvaluationMatrix, Matrix.map_apply, map_monomial, map_one] using he.symm

/-- Universal degree-evaluation rank agrees with actual rank throughout a nonempty
principal open over the original field. -/
theorem universal_pointHilbert_principalOpen {K : Type*} [Field K] [Infinite K]
    (m p d : ℕ) :
    ∃ D : GenericPointRing K m p,
      (∃ a : PointCoordinates K m p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → pointHilbertFunction K a d =
        pointHilbertFunction (GenericPointField K m p) (genericPointCoordinates K m p) d := by
  obtain ⟨D,hD,hgood⟩ := polynomialMatrix_rank_principalOpen
    (F := GenericPointField K m p) (pointEvaluationMatrix K m p d)
  refine ⟨D,hD,?_⟩
  intro a ha
  have hr := hgood a ha
  rw [pointEvaluationMatrix_generic, pointEvaluationMatrix_specialized,
    Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun K (Fin p)) (Froberg.formsBasis K (m+1) d),
    Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun (GenericPointField K m p) (Fin p))
      (Froberg.formsBasis (GenericPointField K m p) (m+1) d),
    Matrix.toLin_toMatrix, Matrix.toLin_toMatrix] at hr
  simpa only [pointHilbertFunction_eq_rank] using hr

/-- In particular, universal points have the maximal degree-evaluation rank. -/
theorem universal_pointHilbert_eq_min {K : Type*} [Field K] [Infinite K]
    (m p d : ℕ) :
    pointHilbertFunction (GenericPointField K m p) (genericPointCoordinates K m p) d =
      min ((m + d).choose d) p := by
  obtain ⟨D,hD,hgeneric⟩ := universal_pointHilbert_principalOpen (K := K) m p d
  obtain ⟨E,hE,hmax⟩ := generic_pointHilbertFunction_at (K := K) m p d
  obtain ⟨a,haD,haE⟩ := Froberg.principal_opens_intersect hD hE
  exact (hgeneric a haD).symm.trans (hmax a haE)

end GenericTransfer
end ESCtoFroberg
