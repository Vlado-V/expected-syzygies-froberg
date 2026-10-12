module

public import Froberg.Graded
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.LinearAlgebra.Projection

@[expose] public section

/-!
# Linear coordinates on actual homogeneous polynomial spaces

An arbitrary basis of the degree-one forms induces an algebra equivalence of
polynomial rings. Both directions preserve each homogeneous degree. These
are proved coordinate changes, with no rank assumption on higher products.
-/

noncomputable section
namespace Froberg.CoordinateFoundation.LinearCoordinates
open MvPolynomial Module
variable {K σ ι : Type*} [Field K]

abbrev H (K σ : Type*) [Field K] (d : ℕ) := homogeneousSubmodule σ K d

/-- The variables are a basis of the actual linear forms. -/
def variableBasis (K σ : Type*) [Field K] : Basis σ K (H K σ 1) :=
  (Basis.span (linearIndependent_X σ K)).map
    (LinearEquiv.ofEq _ _ homogeneousSubmodule_one_eq_span_X.symm)

@[simp] theorem variableBasis_val (i : σ) : (variableBasis K σ i).val = X i := by
  simp [variableBasis, Basis.span_apply]

/-- The polynomial associated to a linear form in the coordinates of `b`. -/
def coordinateLinear (b : Basis ι K (H K σ 1)) : H K σ 1 →ₗ[K] H K ι 1 :=
  b.constr K (fun i => ⟨X i, isHomogeneous_X K i⟩)

@[simp] theorem coordinateLinear_basis (b : Basis ι K (H K σ 1)) (i : ι) :
    coordinateLinear b (b i) = ⟨X i, isHomogeneous_X K i⟩ := by
  simp [coordinateLinear]

private theorem symmetric_linear (b : Basis ι K (H K σ 1)) (p : H K σ 1) :
    SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι K (H K σ 1) p) =
      (coordinateLinear b p).val := by
  have he : (SymmetricAlgebra.equivMvPolynomial b).toLinearMap.comp
      (SymmetricAlgebra.ι K (H K σ 1)) =
      (H K ι 1).subtype.comp (coordinateLinear b) := by
    apply b.ext
    intro i
    simp
  exact LinearMap.congr_fun he p

private theorem variable_coordinateLinear (p : H K σ 1) :
    (coordinateLinear (variableBasis K σ) p).val = p.val := by
  have he : (H K σ 1).subtype.comp (coordinateLinear (variableBasis K σ)) =
      (H K σ 1).subtype := by
    apply (variableBasis K σ).ext
    intro i
    simp
  exact LinearMap.congr_fun he p

/-- A basis of linear forms extends to a polynomial algebra equivalence. -/
def polynomialEquiv (b : Basis ι K (H K σ 1)) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial σ K :=
  (SymmetricAlgebra.equivMvPolynomial b).symm.trans
    (SymmetricAlgebra.equivMvPolynomial (variableBasis K σ))

@[simp] theorem polynomialEquiv_X (b : Basis ι K (H K σ 1)) (i : ι) :
    polynomialEquiv b (X i) = (b i).val := by
  simp only [polynomialEquiv, AlgEquiv.trans_apply,
    SymmetricAlgebra.equivMvPolynomial_symm_X, symmetric_linear, variable_coordinateLinear]

@[simp] theorem polynomialEquiv_symm_X (b : Basis ι K (H K σ 1)) (i : σ) :
    (polynomialEquiv b).symm (X i) =
      (coordinateLinear b (variableBasis K σ i)).val := by
  simp only [polynomialEquiv, AlgEquiv.symm_trans_apply, AlgEquiv.symm_symm,
    SymmetricAlgebra.equivMvPolynomial_symm_X, symmetric_linear]

theorem polynomialEquiv_homogeneous (b : Basis ι K (H K σ 1)) {d : ℕ}
    (p : MvPolynomial ι K) (hp : p.IsHomogeneous d) :
    (polynomialEquiv b p).IsHomogeneous d := by
  have he : (polynomialEquiv b).toAlgHom = aeval (fun i => (b i).val) := by
    ext i
    simp
  change ((polynomialEquiv b).toAlgHom p).IsHomogeneous d
  rw [he]
  simpa using hp.aeval (fun i => (b i).val) (fun i => (b i).property)

theorem polynomialEquiv_symm_homogeneous (b : Basis ι K (H K σ 1)) {d : ℕ}
    (p : MvPolynomial σ K) (hp : p.IsHomogeneous d) :
    ((polynomialEquiv b).symm p).IsHomogeneous d := by
  have he : (polynomialEquiv b).symm.toAlgHom =
      aeval (fun i => (coordinateLinear b (variableBasis K σ i)).val) := by
    ext i
    simp
  change ((polynomialEquiv b).symm.toAlgHom p).IsHomogeneous d
  rw [he]
  simpa using hp.aeval _ (fun i => (coordinateLinear b (variableBasis K σ i)).property)

/-- The induced equivalence on each actual homogeneous component. -/
def formsEquiv (b : Basis ι K (H K σ 1)) (d : ℕ) : H K ι d ≃ₗ[K] H K σ d where
  toFun p := ⟨polynomialEquiv b p.val, polynomialEquiv_homogeneous b p.val p.property⟩
  invFun p := ⟨(polynomialEquiv b).symm p.val,
    polynomialEquiv_symm_homogeneous b p.val p.property⟩
  left_inv p := Subtype.ext ((polynomialEquiv b).symm_apply_apply p.val)
  right_inv p := Subtype.ext ((polynomialEquiv b).apply_symm_apply p.val)
  map_add' _p _q := Subtype.ext (map_add _ _ _)
  map_smul' _c _p := Subtype.ext (map_smul _ _ _)

@[simp] theorem formsEquiv_val (b : Basis ι K (H K σ 1)) (d : ℕ) (p : H K ι d) :
    (formsEquiv b d p).val = polynomialEquiv b p.val := rfl

theorem map_homogeneous (b : Basis ι K (H K σ 1)) (d : ℕ) :
    (H K ι d).map (polynomialEquiv b).toLinearMap = H K σ d := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact polynomialEquiv_homogeneous b q hq
  · intro hp
    exact ⟨(polynomialEquiv b).symm p, polynomialEquiv_symm_homogeneous b p hp,
      (polynomialEquiv b).apply_symm_apply p⟩

/-- Stars and bars for a homogeneous component on any finite variable set. -/
def homogeneousBasis (K σ : Type*) [Field K] (d : ℕ) : Basis (Sym σ d) K (H K σ d) := by
  classical
  rw [H, homogeneousSubmodule_eq_finsupp_supported]
  exact (basisRestrictSupport K {e : σ →₀ ℕ | e.degree = d}).reindex
    (Sym.equivNatSum σ d).symm

instance homogeneousFinite [Finite σ] (d : ℕ) : Module.Finite K (H K σ d) :=
  Module.Finite.of_basis (homogeneousBasis K σ d)

theorem finrank_homogeneous [Fintype σ] (d : ℕ) :
    finrank K (H K σ d) = (Fintype.card σ + d - 1).choose d := by
  classical
  rw [Module.finrank_eq_card_basis (homogeneousBasis K σ d), Sym.card_sym_eq_choose]

end Froberg.CoordinateFoundation.LinearCoordinates
