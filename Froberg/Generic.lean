module

public import Froberg.Koszul
public import Froberg.QuotientModel
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-! A precise nonempty principal-open meaning of a generic endpoint theorem.
The determinant argument generalizes the earlier Quartic/RankOpen construction. -/
noncomputable section
namespace Froberg
open Module MvPolynomial

abbrev CoefficientIndex (n d r : ℕ) := Fin r × Sym (Fin n) d

variable (K : Type*) [Field K] (n d r : ℕ)

def coefficientForms (a : CoefficientIndex n d r → K) (i : Fin r) : Forms K n d :=
  (formsBasis K n d).equivFun.symm (fun m => a (i, m))

def coefficientSpace (a : CoefficientIndex n d r → K) : Submodule K (Poly K n) :=
  Submodule.span K (Set.range (fun i => (coefficientForms K n d r a i).val))

theorem coefficientSpace_homogeneous (a : CoefficientIndex n d r → K) :
    coefficientSpace K n d r a ≤ Forms K n d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact (coefficientForms K n d r a i).property

/-- A genuine nonempty open set, with independent generators and the expected
Hilbert function in the actual quotient ring at the endpoint. -/
def GenericEndpoint : Prop :=
  ∃ D : MvPolynomial (CoefficientIndex n d r) K,
    (∃ a, eval a D ≠ 0) ∧
    ∀ a, eval a D ≠ 0 →
      LinearIndependent K (coefficientForms K n d r a) ∧
      hilbertFunction (coefficientSpace K n d r a) (2 * d) = expectedEndpoint n d r

variable {K n d r}

def coefficientCoordinates : (Fin r → Forms K n d) ≃ₗ[K] (CoefficientIndex n d r → K) where
  toFun f im := (formsBasis K n d).equivFun (f im.1) im.2
  invFun a := coefficientForms K n d r a
  left_inv f := by
    funext i
    exact (formsBasis K n d).equivFun.symm_apply_apply (f i)
  right_inv a := by
    funext im
    exact congrFun ((formsBasis K n d).equivFun.apply_symm_apply (fun m => a (im.1, m))) im.2
  map_add' f g := by ext im; simp
  map_smul' c f := by ext im; simp

def coefficientMultiplicationLinear : (CoefficientIndex n d r → K) →ₗ[K]
    ((Fin r → Forms K n d) →ₗ[K] Forms K n (2 * d)) where
  toFun a := endpointMultiplication (coefficientForms K n d r a)
  map_add' a b := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    simp [endpointMultiplication_val, coefficientForms, add_smul, add_mul, Finset.sum_add_distrib]
  map_smul' c a := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    simp [endpointMultiplication_val, coefficientForms, mul_smul, ← Finset.smul_sum]

/-- A scalar linear map encoded by a degree-one polynomial. -/
def polynomialOfLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → K) →ₗ[K] K) : MvPolynomial ι K :=
  ∑ i, C (L (Pi.single i 1)) * X i

theorem eval_polynomialOfLinear {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : (ι → K) →ₗ[K] K) (a : ι → K) :
    eval a (polynomialOfLinear L) = L a := by
  have h := congrArg L ((Pi.basisFun K ι).sum_equivFun a)
  simpa [polynomialOfLinear, map_sum, Pi.basisFun_apply, Pi.basisFun_equivFun,
    smul_eq_mul, mul_comm] using h

section LinearFamilies
variable {V W ι : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [Fintype ι] [DecidableEq ι]

/-- A determinant neighborhood preserves independence of a linearly varying family. -/
theorem independent_principal_open (q : Fin r → (ι → K) →ₗ[K] V)
    (a₀ : ι → K) (hq : LinearIndependent K (fun i => q i a₀)) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → LinearIndependent K (fun i => q i a) := by
  classical
  obtain ⟨dual, hdual⟩ := exists_coordinate_functionals (fun i => q i a₀) hq
  let M : Matrix (Fin r) (Fin r) (MvPolynomial ι K) :=
    fun i j => polynomialOfLinear ((dual i).comp (q j))
  have heval (a : ι → K) : eval a M.det =
      (Matrix.of fun i j => dual i (q j a)).det := by
    rw [(eval a).map_det]
    congr 1
    ext i j
    exact eval_polynomialOfLinear ((dual i).comp (q j)) a
  refine ⟨M.det, ?_, ?_⟩
  · rw [heval]
    have hM : (Matrix.of fun i j => dual i (q j a₀)) = (1 : Matrix (Fin r) (Fin r) K) := by
      ext i j
      simp [hdual, Matrix.one_apply]
    rw [hM, Matrix.det_one]
    exact one_ne_zero
  · intro a ha
    rw [heval] at ha
    let L : V →ₗ[K] (Fin r → K) := LinearMap.pi dual
    exact LinearIndependent.of_comp L (Matrix.linearIndependent_cols_of_det_ne_zero ha)

/-- Rank is at least its value at any witness on a nonempty principal open. -/
theorem rank_principal_open [FiniteDimensional K V] [FiniteDimensional K W]
    (A : (ι → K) →ₗ[K] (V →ₗ[K] W)) (a₀ : ι → K) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧ ∀ a, eval a D ≠ 0 →
      finrank K (LinearMap.range (A a₀)) ≤ finrank K (LinearMap.range (A a)) := by
  classical
  let R := LinearMap.range (A a₀)
  let b := Module.finBasis K R
  have hb : LinearIndependent K (fun i => (b i).val) :=
    b.linearIndependent.map' R.subtype (LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _))
  have hpre : ∀ i, ∃ x, A a₀ x = (b i).val := fun i => (b i).property
  choose x hx using hpre
  let q : Fin (finrank K R) → (ι → K) →ₗ[K] W := fun i =>
    (LinearMap.applyₗ (R := K) (M₂ := W) (x i)).comp A
  have hq : LinearIndependent K (fun i => q i a₀) := by
    simpa only [q, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply, hx] using hb
  obtain ⟨D, hD, hfamily⟩ := independent_principal_open q a₀ hq
  refine ⟨D, hD, ?_⟩
  intro a ha
  have hle : Submodule.span K (Set.range (fun i => q i a)) ≤ LinearMap.range (A a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨x i, rfl⟩
  have h := Submodule.finrank_mono hle
  rwa [finrank_span_eq_card (hfamily a ha), Fintype.card_fin] at h
end LinearFamilies

/-- A single independent family attaining the lower bound proves the generic
endpoint on an explicitly nonempty principal open. -/
theorem genericEndpoint_of_coefficient_witness (hn : 0 < n)
    (a₀ : CoefficientIndex n d r → K)
    (hlin : LinearIndependent K (coefficientForms K n d r a₀))
    (hdim : finrank K (EndpointQuotient K n d (coefficientSpace K n d r a₀)) =
      expectedEndpoint n d r) : GenericEndpoint K n d r := by
  classical
  let q : Fin r → (CoefficientIndex n d r → K) →ₗ[K] Forms K n d := fun i =>
    (formsBasis K n d).equivFun.symm.toLinearMap.comp (LinearMap.funLeft K K (fun m => (i, m)))
  obtain ⟨D₁, hD₁, hind⟩ := independent_principal_open q a₀ hlin
  obtain ⟨D₂, hD₂, hrank⟩ := rank_principal_open
    (coefficientMultiplicationLinear (K := K) (n := n) (d := d) (r := r)) a₀
  refine ⟨D₁ * D₂, ⟨a₀, by simpa using mul_ne_zero hD₁ hD₂⟩, ?_⟩
  intro a ha
  have hparts : eval a D₁ ≠ 0 ∧ eval a D₂ ≠ 0 := by simpa using ha
  have hi : LinearIndependent K (coefficientForms K n d r a) := hind a hparts.1
  refine ⟨hi, ?_⟩
  rw [← endpoint_finrank_eq_hilbertFunction _ (coefficientSpace_homogeneous K n d r a)]
  have hlow := endpoint_quotient_lower_bound hn (coefficientForms K n d r a) hi
  change expectedEndpoint n d r ≤
    finrank K (EndpointQuotient K n d (coefficientSpace K n d r a)) at hlow
  have hr := hrank a hparts.2
  have hbefore := endpoint_quotient_add_rank hn (coefficientForms K n d r a₀)
  have hafter := endpoint_quotient_add_rank hn (coefficientForms K n d r a)
  change finrank K (EndpointQuotient K n d (coefficientSpace K n d r a₀)) + _ = _ at hbefore
  change finrank K (EndpointQuotient K n d (coefficientSpace K n d r a)) + _ = _ at hafter
  rw [hdim] at hbefore
  change finrank K (LinearMap.range (endpointMultiplication (coefficientForms K n d r a₀))) ≤
    finrank K (LinearMap.range (endpointMultiplication (coefficientForms K n d r a))) at hr
  omega

end Froberg
