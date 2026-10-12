module

public import ESCtoFroberg.GenericRename
public import ESCtoFroberg.BlockSymmetry
public import ESCtoFroberg.SyzygyEvaluation

@[expose] public section
noncomputable section
namespace ESCtoFroberg
open Module MvPolynomial

variable {R : Type*} [Field R] {n d e r : ℕ}

@[simp] theorem coefficientFormsAddEquiv_val (φ : R ≃+* R) {n d : ℕ}
    (f : Forms R n d) :
    (coefficientFormsAddEquiv φ n d f).val = MvPolynomial.map φ.toRingHom f.val := rfl

/-- The actual degree forms selected by a basis of a homogeneous subspace. -/
def basisFormFamily (Q : Submodule R (Forms R n d)) (b : Basis (Fin r) R Q) :
    Fin r → Forms R n d := fun i => (b i).val

theorem prefixMultiplication_tensorTransport
    (Q : Submodule R (Forms R n d)) (b : Basis (Fin r) R Q)
    (φ : R ≃+* R) (F : Q ≃+ Q)
    (_hF : ∀ a q, F (a • q) = φ a • F q)
    (hFval : ∀ q, (F q).val = coefficientFormsAddEquiv φ n d q.val)
    (h : Fin r → Forms R n e) :
    Froberg.prefixMultiplication (basisFormFamily Q b) e
      (tensorTransport (R := R) (V := Q) b F (coefficientFormsAddEquiv φ n e) h) =
      coefficientFormsAddEquiv φ n (d + e)
        (Froberg.prefixMultiplication (basisFormFamily Q b) e h) := by
  apply Subtype.ext
  simp only [Froberg.prefixMultiplication_val, basisFormFamily,
    tensorTransport_apply, Submodule.coe_sum, Submodule.coe_smul,
    MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  have hcoeff (i : Fin r) :
      ∑ j, (b j).val.val * C (b.repr (F (b i)) j) =
        MvPolynomial.map φ.toRingHom (b i).val.val := by
    have hh := congrArg (fun q : Q => q.val.val) (b.sum_repr (F (b i)))
    simpa only [Submodule.coe_sum, Submodule.coe_smul, MvPolynomial.smul_eq_C_mul,
      hFval, coefficientFormsAddEquiv_val, mul_comm] using hh
  simp_rw [hcoeff]
  simp only [coefficientFormsAddEquiv_val, Froberg.prefixMultiplication_val,
    basisFormFamily, map_sum, map_mul]

/-- The permutation action on the generator space induces a genuine automorphism
of the actual multiplication kernel in every multiplier degree. -/
def tensorSyzygyAddEquiv
    (Q : Submodule R (Forms R n d)) (b : Basis (Fin r) R Q)
    (φ : R ≃+* R) (F : Q ≃+ Q)
    (hF : ∀ a q, F (a • q) = φ a • F q)
    (hFval : ∀ q, (F q).val = coefficientFormsAddEquiv φ n d q.val)
    (e : ℕ) :
    (Froberg.prefixMultiplication (basisFormFamily Q b) e).ker ≃+
      (Froberg.prefixMultiplication (basisFormFamily Q b) e).ker := by
  let T := tensorTransportEquiv (R := R) (V := Q) b φ F hF (coefficientFormsAddEquiv φ n e)
    (coefficientFormsAddEquiv_smul (n := n) (d := e) φ)
  exact submoduleAddEquiv T _ (fun h => by
    simp only [LinearMap.mem_ker]
    change _ = 0 ↔ Froberg.prefixMultiplication (basisFormFamily Q b) e
      (tensorTransport (R := R) (V := Q) b F (coefficientFormsAddEquiv φ n e) h) = 0
    rw [prefixMultiplication_tensorTransport Q b φ F hF hFval]
    exact (map_eq_zero_iff (coefficientFormsAddEquiv φ n (d+e))
      (coefficientFormsAddEquiv φ n (d+e)).injective).symm)

@[simp] theorem tensorSyzygyAddEquiv_apply
    (Q : Submodule R (Forms R n d)) (b : Basis (Fin r) R Q)
    (φ : R ≃+* R) (F : Q ≃+ Q)
    (hF : ∀ a q, F (a • q) = φ a • F q)
    (hFval : ∀ q, (F q).val = coefficientFormsAddEquiv φ n d q.val)
    (z : (Froberg.prefixMultiplication (basisFormFamily Q b) e).ker) :
    (tensorSyzygyAddEquiv Q b φ F hF hFval e z).val =
      tensorTransport (R := R) (V := Q) b F (coefficientFormsAddEquiv φ n e) z.val := rfl

end ESCtoFroberg
