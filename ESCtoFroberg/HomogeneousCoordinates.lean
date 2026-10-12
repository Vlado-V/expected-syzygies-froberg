module

public import Froberg.Graded
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open MvPolynomial Module
variable (K : Type*) [Field K] (n d : ℕ)

private theorem basis_transport_val {M ι : Type*} [AddCommGroup M] [Module K M]
    {P Q : Submodule K M} (h : P = Q) (b : Basis ι K Q) (i : ι) :
    (Eq.mpr (congrArg (fun W : Submodule K M => Basis ι K W) h) b i).val = (b i).val := by
  subst P
  rfl

/-- The homogeneous monomial basis has coefficient one and the indicated exponent. -/
theorem formsBasis_val_monomial (s : Sym (Fin n) d) :
    (Froberg.formsBasis K n d s).val = monomial (Froberg.exponentEquiv n d s).val 1 := by
  let b := (MvPolynomial.basisRestrictSupport K {e : Fin n →₀ ℕ | e.degree = d}).reindex
    (Froberg.exponentEquiv n d).symm
  have h : Froberg.Forms K n d = MvPolynomial.restrictSupport K {e : Fin n →₀ ℕ | e.degree = d} :=
    homogeneousSubmodule_eq_finsupp_supported (Fin n) K d
  have hval : (Froberg.formsBasis K n d s).val = (b s).val :=
    basis_transport_val K h b s
  rw [hval]
  simp only [b,Basis.reindex_apply,Equiv.symm_symm]
  change ((AddMonoidAlgebra.supportedEquivFinsupp {e : Fin n →₀ ℕ | e.degree = d}).symm
    (Finsupp.single (Froberg.exponentEquiv n d s) 1)).val = _
  simp [AddMonoidAlgebra.supportedEquivFinsupp]
  rfl

/-- A homogeneous basis coordinate is its actual polynomial monomial coefficient. -/
theorem formsBasis_equivFun_eq_coeff (f : Froberg.Forms K n d) (s : Sym (Fin n) d) :
    (Froberg.formsBasis K n d).equivFun f s = f.val.coeff (Froberg.exponentEquiv n d s).val := by
  classical
  let l : Froberg.Forms K n d →ₗ[K] K :=
    (MvPolynomial.lcoeff K (Froberg.exponentEquiv n d s).val).comp (Froberg.Forms K n d).subtype
  have hl : (Froberg.formsBasis K n d).coord s = l := by
    apply (Froberg.formsBasis K n d).ext
    intro t
    have he : (Froberg.exponentEquiv n d t).val = (Froberg.exponentEquiv n d s).val ↔ t = s := by
      constructor
      · intro h
        exact (Froberg.exponentEquiv n d).injective (Subtype.ext h)
      · rintro rfl
        rfl
    simp [l,Basis.coord_apply,Finsupp.single_apply,formsBasis_val_monomial,he]
  rw [Basis.equivFun_apply]
  change (Froberg.formsBasis K n d).coord s f = _
  exact LinearMap.congr_fun hl f

end ESCtoFroberg
