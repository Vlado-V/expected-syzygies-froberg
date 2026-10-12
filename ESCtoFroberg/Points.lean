module

public import Froberg.QuotientModel
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open MvPolynomial Module

abbrev Poly (K : Type*) [Field K] (n : ℕ) := Froberg.Poly K n
abbrev Forms (K : Type*) [Field K] (n d : ℕ) := Froberg.Forms K n d

variable (K : Type*) [Field K]

abbrev PointCoordinates (m p : ℕ) := Fin p × Fin m → K

def chartPoint {m p : ℕ} (a : PointCoordinates K m p) (i : Fin p) : Fin (m + 1) → K :=
  Fin.lastCases 1 (fun j => a (i, j))

@[simp] theorem chartPoint_last {m p : ℕ} (a : PointCoordinates K m p) (i : Fin p) :
    chartPoint K a i (Fin.last m) = 1 := by simp [chartPoint]

@[simp] theorem chartPoint_castSucc {m p : ℕ} (a : PointCoordinates K m p) (i : Fin p)
    (j : Fin m) : chartPoint K a i j.castSucc = a (i, j) := by simp [chartPoint]

def DistinctPoints {m p : ℕ} (a : PointCoordinates K m p) : Prop :=
  Function.Injective (fun i => fun j => a (i, j))

/-- Substitution along the projective line represented by normalized coordinates. -/
def pointSubstitution {m : ℕ} (x : Fin (m + 1) → K) :
    Poly K (m + 1) →+* Poly K 1 :=
  eval₂Hom C (fun j => X 0 * C (x j))

/-- The homogeneous vanishing ideal of a projective point. -/
def singlePointIdeal {m : ℕ} (x : Fin (m + 1) → K) : Ideal (Poly K (m + 1)) :=
  RingHom.ker (pointSubstitution K x)

def pointIdeal {m p : ℕ} (a : PointCoordinates K m p) : Ideal (Poly K (m + 1)) :=
  ⨅ i : Fin p, singlePointIdeal K (chartPoint K a i)

def evaluationLinear (n d : ℕ) (x : Fin n → K) : Forms K n d →ₗ[K] K where
  toFun f := eval x f.val
  map_add' f g := map_add _ _ _
  map_smul' c f := by simp

@[simp] theorem evaluationLinear_apply {n d : ℕ} (x : Fin n → K) (f : Forms K n d) :
    evaluationLinear K n d x f = eval x f.val := rfl

def pointEvaluation {m p : ℕ} (a : PointCoordinates K m p) (d : ℕ) :
    Forms K (m + 1) d →ₗ[K] (Fin p → K) :=
  LinearMap.pi (fun i => evaluationLinear K (m + 1) d (chartPoint K a i))

def pointDegreePiece {m p : ℕ} (a : PointCoordinates K m p) (d : ℕ) :
    Submodule K (Forms K (m + 1) d) := LinearMap.ker (pointEvaluation K a d)

def pointDegreeSpace {m p : ℕ} (a : PointCoordinates K m p) (d : ℕ) :
    Submodule K (Poly K (m + 1)) :=
  (pointDegreePiece K a d).map (Forms K (m + 1) d).subtype

def choppedIdeal {m p : ℕ} (a : PointCoordinates K m p) (d : ℕ) :
    Ideal (Poly K (m + 1)) := Ideal.span (pointDegreeSpace K a d : Set (Poly K (m + 1)))

def pointHilbertFunction {m p : ℕ} (a : PointCoordinates K m p) (d : ℕ) : ℕ :=
  finrank K ((Forms K (m + 1) d) ⧸ pointDegreePiece K a d)

/-- The degree component in the actual ring quotient by the chopped ideal. -/
def choppedHilbertFunction {m p : ℕ} (a : PointCoordinates K m p) (d t : ℕ) : ℕ :=
  Froberg.hilbertFunction (pointDegreeSpace K a d) t

variable {K}

@[simp] theorem pointEvaluation_apply {m p d : ℕ} (a : PointCoordinates K m p)
    (f : Forms K (m + 1) d) (i : Fin p) :
    pointEvaluation K a d f i = eval (chartPoint K a i) f.val := rfl

@[simp] theorem mem_pointDegreePiece {m p d : ℕ} (a : PointCoordinates K m p)
    (f : Forms K (m + 1) d) :
    f ∈ pointDegreePiece K a d ↔ ∀ i, eval (chartPoint K a i) f.val = 0 := by
  simp [pointDegreePiece, LinearMap.mem_ker, funext_iff]

@[simp] theorem mem_pointDegreeSpace {m p d : ℕ} (a : PointCoordinates K m p)
    (f : Poly K (m + 1)) :
    f ∈ pointDegreeSpace K a d ↔ f.IsHomogeneous d ∧
      ∀ i, eval (chartPoint K a i) f = 0 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.property, (mem_pointDegreePiece a g).mp hg⟩
  · rintro ⟨hf, heval⟩
    exact ⟨⟨f, hf⟩, (mem_pointDegreePiece a ⟨f, hf⟩).mpr heval, rfl⟩

theorem pointDegreeSpace_homogeneous {m p d : ℕ} (a : PointCoordinates K m p) :
    pointDegreeSpace K a d ≤ Forms K (m + 1) d := by
  rintro f ⟨g, hg, rfl⟩
  exact g.property

theorem pointHilbertFunction_eq_rank {m p d : ℕ} (a : PointCoordinates K m p) :
    pointHilbertFunction K a d = finrank K (pointEvaluation K a d).range :=
  (pointEvaluation K a d).quotKerEquivRange.finrank_eq

theorem finrank_forms (m d : ℕ) :
    finrank K (Forms K (m + 1) d) = (m + d).choose d := by
  have h : m + 1 + d - 1 = m + d := by omega
  simpa only [h] using Froberg.finrank_forms K (m + 1) d (by omega)

theorem pointHilbertFunction_le {m p d : ℕ} (a : PointCoordinates K m p) :
    pointHilbertFunction K a d ≤ min ((m + d).choose d) p := by
  rw [pointHilbertFunction_eq_rank]
  apply le_min
  · simpa [finrank_forms] using (pointEvaluation K a d).finrank_range_le
  · have h := Submodule.finrank_le (pointEvaluation K a d).range
    simpa [Module.finrank_pi_fintype] using h

/-- Dimension of the actual degree-d equations from the evaluation quotient. -/
theorem pointDegreePiece_finrank {m p : ℕ} (a : PointCoordinates K m p) (d : ℕ) :
    finrank K (pointDegreePiece K a d) = (m+d).choose d - pointHilbertFunction K a d := by
  have h := (pointDegreePiece K a d).finrank_quotient_add_finrank
  rw [finrank_forms] at h
  change pointHilbertFunction K a d + _ = _ at h
  omega

theorem pointDegreeSpace_finrank {m p : ℕ} (a : PointCoordinates K m p) (d : ℕ) :
    finrank K (pointDegreeSpace K a d) = (m+d).choose d - pointHilbertFunction K a d := by
  rw [pointDegreeSpace, Submodule.finrank_map_subtype_eq, pointDegreePiece_finrank]

/-- A finite-dimensional subspace has an independent ambient spanning tuple. -/
theorem exists_subspace_basis {V : Type*} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (W : Submodule K V) :
    ∃ q : Fin (finrank K W) → V, LinearIndependent K q ∧
      Submodule.span K (Set.range q) = W := by
  classical
  let b := Module.finBasis K W
  let q : Fin (finrank K W) → V := fun i => (b i).val
  refine ⟨q, b.linearIndependent.map' W.subtype W.ker_subtype, ?_⟩
  have hh := congrArg (fun T : Submodule K W => T.map W.subtype) b.span_eq
  rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ←Set.range_comp] at hh
  exact hh

/-- An independent homogeneous basis supplies the actual generators of the chop. -/
theorem exists_degree_generators {m p : ℕ} (a : PointCoordinates K m p) (d : ℕ) :
    ∃ q : Fin (finrank K (pointDegreePiece K a d)) → Forms K (m+1) d,
      LinearIndependent K q ∧
      Submodule.span K (Set.range (fun i => (q i).val)) = pointDegreeSpace K a d := by
  obtain ⟨q,hli,hspan⟩ := exists_subspace_basis (pointDegreePiece K a d)
  refine ⟨q,hli,?_⟩
  have hh := congrArg (fun W : Submodule K (Forms K (m+1) d) =>
    W.map (Forms K (m+1) d).subtype) hspan
  rw [Submodule.map_span, ←Set.range_comp] at hh
  exact hh

/-- Homogeneous scaling after any coefficient-ring map. -/
theorem homogeneous_eval₂_scale {σ R T : Type*} [CommSemiring R] [CommSemiring T]
    {f : MvPolynomial σ R} {d : ℕ} (hf : f.IsHomogeneous d)
    (k : R →+* T) (x : σ → T) (b : T) :
    MvPolynomial.eval₂ k (fun i => b * x i) f = b ^ d * MvPolynomial.eval₂ k x f := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hf.degree_eq_sum_deg_support hu]
  ac_rfl

theorem homogeneous_eval_scale {σ R : Type*} [CommSemiring R]
    {f : MvPolynomial σ R} {d : ℕ} (hf : f.IsHomogeneous d)
    (x : σ → R) (b : R) :
    MvPolynomial.eval (fun i => b * x i) f = b ^ d * MvPolynomial.eval x f := by
  classical
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hf.degree_eq_sum_deg_support hu]
  ac_rfl

theorem homogeneous_mem_singlePointIdeal_iff {m d : ℕ} (x : Fin (m + 1) → K)
    (f : Forms K (m + 1) d) :
    f.val ∈ singlePointIdeal K x ↔ eval x f.val = 0 := by
  have hs : pointSubstitution K x f.val = X 0 ^ d * C (eval x f.val) := by
    change eval₂ C (fun j => X 0 * C (x j)) f.val = _
    rw [homogeneous_eval₂_scale f.property C (fun j => C (x j)) (X 0)]
    congr 1
    simpa [Function.comp_def] using
      (MvPolynomial.eval₂_comp_left C (RingHom.id K) x f.val).symm
  change pointSubstitution K x f.val = 0 ↔ _
  rw [hs]
  simp

theorem homogeneous_mem_pointIdeal_iff {m p d : ℕ} (a : PointCoordinates K m p)
    (f : Forms K (m + 1) d) :
    f.val ∈ pointIdeal K a ↔ f ∈ pointDegreePiece K a d := by
  simp only [pointIdeal, Ideal.mem_iInf, mem_pointDegreePiece]
  apply forall_congr'
  intro i
  exact homogeneous_mem_singlePointIdeal_iff _ f

theorem choppedIdeal_le_pointIdeal {m p d : ℕ} (a : PointCoordinates K m p) :
    choppedIdeal K a d ≤ pointIdeal K a := by
  apply Ideal.span_le.mpr
  rintro f ⟨g, hg, rfl⟩
  exact (homogeneous_mem_pointIdeal_iff a g).mpr hg

/-- Substitution by congruent variables preserves an arbitrary actual ideal. -/
theorem sub_substitution_mem {n : ℕ} (I : Ideal (Poly K n)) (q : Fin n → Poly K n)
    (hq : ∀ i, X i - q i ∈ I) (f : Poly K n) : f - eval₂ C q f ∈ I := by
  let π := Ideal.Quotient.mk I
  have heq : π.comp (eval₂Hom C q) = π := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [π]
    · intro i
      rw [RingHom.comp_apply, eval₂Hom_X']
      exact (Ideal.Quotient.eq.mpr (hq i)).symm
  apply Ideal.Quotient.eq.mp
  exact (congrArg (fun h : Poly K n →+* Poly K n ⧸ I => h f) heq).symm

/-- The normalized point ideal is generated by its affine coordinate equations. -/
theorem singlePointIdeal_chart_eq_span {m p : ℕ} (a : PointCoordinates K m p) (i : Fin p) :
    singlePointIdeal K (chartPoint K a i) =
      Ideal.span (Set.range (fun j : Fin m => X j.castSucc - C (a (i,j)) * X (Fin.last m))) := by
  let I : Ideal (Poly K (m + 1)) :=
    Ideal.span (Set.range (fun j : Fin m => X j.castSucc - C (a (i,j)) * X (Fin.last m)))
  let q : Fin (m + 1) → Poly K (m + 1) := fun j => X (Fin.last m) * C (chartPoint K a i j)
  have hq : ∀ j, X j - q j ∈ I := by
    intro j
    refine Fin.lastCases ?_ (fun l => ?_) j
    · simp [q, I]
    · apply Ideal.subset_span
      exact ⟨l, by simp [q, mul_comm]⟩
  apply le_antisymm
  · intro f hf
    have hh : eval₂ C q f = 0 := by
      let back : Poly K 1 →+* Poly K (m + 1) := eval₂Hom C (fun _ => X (Fin.last m))
      have heq : back.comp (pointSubstitution K (chartPoint K a i)) = eval₂Hom C q := by
        apply MvPolynomial.ringHom_ext
        · intro c
          simp [back, pointSubstitution]
        · intro j
          simp [back, pointSubstitution, q]
      change pointSubstitution K (chartPoint K a i) f = 0 at hf
      have h := congrArg (fun h : Poly K (m + 1) →+* Poly K (m + 1) => h f) heq
      change back (pointSubstitution K (chartPoint K a i) f) = eval₂ C q f at h
      rw [hf, map_zero] at h
      exact h.symm
    simpa [hh] using sub_substitution_mem I q hq f
  · apply Ideal.span_le.mpr
    rintro f ⟨j, rfl⟩
    change pointSubstitution K (chartPoint K a i)
      (X j.castSucc - C (a (i, j)) * X (Fin.last m)) = 0
    simp [pointSubstitution, mul_comm]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual point ideal is homogeneous. -/
theorem pointIdeal_homogeneous {m p : ℕ} (a : PointCoordinates K m p) :
    (pointIdeal K a).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (m+1)) K) := by
  apply Ideal.IsHomogeneous.iInf
  intro i
  rw [singlePointIdeal_chart_eq_span]
  apply Ideal.homogeneous_span
  rintro f ⟨j, rfl⟩
  refine ⟨1, ?_⟩
  exact (isHomogeneous_X K j.castSucc).sub ((isHomogeneous_X K (Fin.last m)).C_mul _)

end ESCtoFroberg
