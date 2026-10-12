module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-! # The first-order rank of a linear pencil

The actual map from the kernel of the constant term to its cokernel contributes
its full rank to a sufficiently general scalar specialization.  The proof
constructs normalized image columns and a determinant polynomial with constant
term one.
-/

noncomputable section

namespace ESCtoFroberg.FirstOrderRank

open Module Polynomial

variable {K V W J : Type*} [Field K]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]
  [AddCommGroup J] [Module K J]

/-- Injectivity of the constant term persists away from the zero set of an
explicit determinant polynomial whose value at zero is one. -/
theorem injective_pencil_principal_open (E₀ E₁ : V →ₗ[K] W)
    (hE₀ : Function.Injective E₀) :
    ∃ D : K[X], D.eval 0 = 1 ∧
      ∀ ε : K, D.eval ε ≠ 0 → Function.Injective (E₀ + ε • E₁) := by
  classical
  let b := Module.finBasis K V
  obtain ⟨L, hL⟩ := E₀.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hE₀)
  let π : W →ₗ[K] (Fin (finrank K V) → K) := b.equivFun.toLinearMap.comp L
  let M : Matrix (Fin (finrank K V)) (Fin (finrank K V)) K[X] :=
    fun i j => C (π (E₀ (b j)) i) + X * C (π (E₁ (b j)) i)
  have hπ (j) : π (E₀ (b j)) = Pi.single j 1 := by
    have h := LinearMap.congr_fun hL (b j)
    ext i
    have hi := congrArg (fun v => b.equivFun v i) h
    simpa [π, LinearMap.comp_apply, Pi.single_apply, Finsupp.single_apply, eq_comm] using hi
  have heval (ε : K) : M.det.eval ε =
      (Matrix.of fun i j => π ((E₀ + ε • E₁) (b j)) i).det := by
    change (Polynomial.evalRingHom ε) M.det = _
    rw [(Polynomial.evalRingHom ε).map_det]
    congr 1
    ext i j
    change (Polynomial.evalRingHom ε) (M i j) = _
    simp [M, map_add, map_smul, smul_eq_mul]
    exact mul_comm _ _
  refine ⟨M.det, ?_, ?_⟩
  · rw [heval]
    have hm : (Matrix.of fun i j => π ((E₀ + (0 : K) • E₁) (b j)) i) =
        (1 : Matrix (Fin (finrank K V)) (Fin (finrank K V)) K) := by
      ext i j
      simp [hπ, Matrix.one_apply, Pi.single_apply]
    rw [hm, Matrix.det_one]
  · intro ε hε
    rw [heval] at hε
    have hi : LinearIndependent K (fun j => (E₀ + ε • E₁) (b j)) :=
      LinearIndependent.of_comp π (Matrix.linearIndependent_cols_of_det_ne_zero hε)
    have heq : b.constr K (fun j => (E₀ + ε • E₁) (b j)) = E₀ + ε • E₁ := by
      apply b.ext
      intro j
      exact b.constr_basis K _ j
    rw [← heq]
    exact b.injective_constr_of_linearIndependent hi

/-- The actual first response on the old kernel, read in any quotient that
annihilates the old image. -/
def firstResponse (A₀ A₁ : V →ₗ[K] W) (π : W →ₗ[K] J) :
    A₀.ker →ₗ[K] J :=
  π.comp (A₁.comp A₀.ker.subtype)

/-- The first response gives the rank gain on a nonempty determinant open of
nonzero parameters.  No rank or enlarged-minor conclusion is assumed. -/
theorem rank_gain_principal_open (A₀ A₁ : V →ₗ[K] W) (π : W →ₗ[K] J)
    (hπ : π.comp A₀ = 0) :
    ∃ D : K[X], D.eval 0 = 1 ∧
      ∀ ε : K, ε ≠ 0 → D.eval ε ≠ 0 →
        finrank K A₀.range + finrank K (firstResponse A₀ A₁ π).range ≤
          finrank K (A₀ + ε • A₁).range := by
  classical
  let R := firstResponse A₀ A₁ π
  obtain ⟨P, hP⟩ := A₀.rangeRestrict.exists_rightInverse_of_surjective A₀.range_rangeRestrict
  obtain ⟨S, hS⟩ := R.rangeRestrict.exists_rightInverse_of_surjective R.range_rangeRestrict
  have hPval (u : A₀.range) : A₀ (P u) = u.val :=
    congrArg Subtype.val (LinearMap.congr_fun hP u)
  have hSval (u : R.range) : R (S u) = u.val :=
    congrArg Subtype.val (LinearMap.congr_fun hS u)
  let B : R.range →ₗ[K] W := A₁.comp (A₀.ker.subtype.comp S)
  have hB (u : R.range) : π (B u) = u.val := hSval u
  let E₀ : (A₀.range × R.range) →ₗ[K] W := A₀.range.subtype.coprod B
  let E₁ : (A₀.range × R.range) →ₗ[K] W :=
    (A₁.comp P).comp (LinearMap.fst K _ _)
  have hπu (u : A₀.range) : π u.val = 0 := by
    rw [← hPval u]
    exact LinearMap.congr_fun hπ (P u)
  have hE₀ : Function.Injective E₀ := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 0
    change x.1.val + B x.2 = 0 at hx
    have hv : x.2 = 0 := by
      apply Subtype.ext
      have hh := congrArg π hx
      simpa only [map_add, hπu, hB, zero_add, map_zero, Submodule.coe_zero] using hh
    have hu : x.1 = 0 := by
      apply Subtype.ext
      simpa only [hv, map_zero, add_zero, Submodule.coe_zero] using hx
    exact Prod.ext hu hv
  obtain ⟨D, hD, hEinj⟩ := injective_pencil_principal_open E₀ E₁ hE₀
  refine ⟨D, hD, ?_⟩
  intro ε hε hDε
  have hsub : (E₀ + ε • E₁).range ≤ (A₀ + ε • A₁).range := by
    rintro _ ⟨x, rfl⟩
    let z := S x.2
    have hz : A₀ z.val = 0 := z.property
    refine ⟨P x.1 + ε⁻¹ • z.val, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul,
      hz, zero_add, smul_smul, inv_mul_cancel₀ hε, one_smul]
    rw [hPval]
    change x.1.val + ε • A₁ (P x.1) + A₁ z.val =
      x.1.val + B x.2 + ε • A₁ (P x.1)
    change x.1.val + ε • A₁ (P x.1) + B x.2 = _
    abel
  have hr := Submodule.finrank_mono hsub
  rw [LinearMap.finrank_range_of_inj (hEinj ε hDε), Module.finrank_prod] at hr
  exact hr

/-- Over an infinite field an actual nonzero scalar realizes the first-order
rank gain. -/
theorem rank_gain [Infinite K] (A₀ A₁ : V →ₗ[K] W) (π : W →ₗ[K] J)
    (hπ : π.comp A₀ = 0) :
    ∃ ε : K, ε ≠ 0 ∧
      finrank K A₀.range + finrank K (firstResponse A₀ A₁ π).range ≤
        finrank K (A₀ + ε • A₁).range := by
  obtain ⟨D, hD, h⟩ := rank_gain_principal_open A₀ A₁ π hπ
  have hDn : D ≠ 0 := by intro hz; simp [hz] at hD
  have hDX : D * X ≠ 0 := mul_ne_zero hDn Polynomial.X_ne_zero
  have hex : ∃ ε : K, (D * X).eval ε ≠ 0 := by
    by_contra h
    push Not at h
    exact hDX (Polynomial.zero_of_eval_zero _ h)
  obtain ⟨ε, hε⟩ := hex
  have hparts : D.eval ε ≠ 0 ∧ ε ≠ 0 := by simpa using hε
  exact ⟨ε, hparts.2, h ε hparts.2 hparts.1⟩

/-- The intrinsic map from the old kernel to the old cokernel. -/
def cokernelResponse (A₀ A₁ : V →ₗ[K] W) :
    A₀.ker →ₗ[K] (W ⧸ A₀.range) :=
  firstResponse A₀ A₁ A₀.range.mkQ

/-- The intrinsic first-order gain holds on an explicit determinant open. -/
theorem cokernel_rank_gain_principal_open (A₀ A₁ : V →ₗ[K] W) :
    ∃ D : K[X], D.eval 0 = 1 ∧
      ∀ ε : K, ε ≠ 0 → D.eval ε ≠ 0 →
        finrank K A₀.range + finrank K (cokernelResponse A₀ A₁).range ≤
          finrank K (A₀ + ε • A₁).range := by
  apply rank_gain_principal_open A₀ A₁ A₀.range.mkQ
  ext v
  simp

/-- Intrinsic first-order rank deformation, Proposition 3.2's linear algebra
assertion, in a scalar-specialization form. -/
theorem cokernel_rank_gain [Infinite K] (A₀ A₁ : V →ₗ[K] W) :
    ∃ ε : K, ε ≠ 0 ∧
      finrank K A₀.range + finrank K (cokernelResponse A₀ A₁).range ≤
        finrank K (A₀ + ε • A₁).range := by
  apply rank_gain A₀ A₁ A₀.range.mkQ
  ext v
  simp

end ESCtoFroberg.FirstOrderRank
