module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Actual polynomial spaces and endpoint quotients

The basic monomial-basis construction is adapted from the user's earlier
`Quartic/Homogeneous.lean` and generalized to arbitrary degrees. None of the
geometric assertions of the manuscript is assumed by this file.
-/

noncomputable section
namespace Froberg
open MvPolynomial Module

variable (K : Type*) [Field K] (n d : ℕ)

abbrev Poly := MvPolynomial (Fin n) K
abbrev Forms := MvPolynomial.homogeneousSubmodule (Fin n) K d

/-- The dimension function, with the zero-variable, degree-zero case correct. -/
def numMonomials (n d : ℕ) : ℕ := Nat.multichoose n d

/-- Monomials of degree `d` correspond to multisets of `d` variables. -/
def exponentEquiv : Sym (Fin n) d ≃ {e : Fin n →₀ ℕ // e.degree = d} :=
  Sym.equivNatSum (Fin n) d

/-- A basis of the actual homogeneous polynomial subspace. -/
def formsBasis : Basis (Sym (Fin n) d) K (Forms K n d) := by
  rw [Forms, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact (MvPolynomial.basisRestrictSupport K {e : Fin n →₀ ℕ | e.degree = d}).reindex
    (exponentEquiv n d).symm

instance formsFinite : Module.Finite K (Forms K n d) :=
  Module.Finite.of_basis (formsBasis K n d)

/-- Stars and bars in the positive-variable range of the manuscript. -/
theorem finrank_forms (_hn : 0 < n) :
    finrank K (Forms K n d) = (n + d - 1).choose d := by
  rw [Module.finrank_eq_card_basis (formsBasis K n d), Sym.card_sym_eq_choose]
  simp

/-- Actual multiplication spans every homogeneous component. -/
theorem forms_mul_forms (a b : ℕ) :
    Forms K n a * Forms K n b = Forms K n (a + b) := by
  calc
    Forms K n a * Forms K n b = Forms K n 1 ^ a * Forms K n 1 ^ b := by
      simp only [Forms, MvPolynomial.homogeneousSubmodule_one_pow]
    _ = Forms K n 1 ^ (a + b) := (pow_add _ a b).symm
    _ = Forms K n (a + b) := MvPolynomial.homogeneousSubmodule_one_pow K (a + b)

/-- Products by degree-`d` coefficients, viewed inside degree `2*d`. -/
def endpointProducts (W : Submodule K (Poly K n)) : Submodule K (Forms K n (2 * d)) :=
  (W * Forms K n d).comap (Forms K n (2 * d)).subtype

abbrev EndpointQuotient (W : Submodule K (Poly K n)) :=
  (Forms K n (2 * d)) ⧸ endpointProducts K n d W

/-- The signed endpoint Euler characteristic, not its positive truncation. -/
def euler (r : ℕ) : ℤ :=
  ((n + 2 * d - 1).choose (2 * d) : ℤ) -
    (r : ℤ) * (n + d - 1).choose d + (r.choose 2 : ℤ)

/-- The expected endpoint dimension when no earlier truncation intervenes. -/
def expectedEndpoint (r : ℕ) : ℕ := (euler n d r).toNat

variable {K n d}

theorem endpoint_products_homogeneous (W : Submodule K (Poly K n))
    (hW : W ≤ Forms K n d) : W * Forms K n d ≤ Forms K n (2 * d) := by
  simpa only [two_mul] using
    (mul_le_mul_left hW (Forms K n d)).trans (MvPolynomial.homogeneousSubmodule_mul d d)

theorem endpointProducts_mono {W W' : Submodule K (Poly K n)} (h : W ≤ W') :
    endpointProducts K n d W ≤ endpointProducts K n d W' :=
  Submodule.comap_mono (mul_le_mul_left h _)

@[simp] theorem endpointProducts_bot : endpointProducts K n d ⊥ = ⊥ := by
  simp [endpointProducts]

@[simp] theorem endpointProducts_all : endpointProducts K n d (Forms K n d) = ⊤ := by
  simp [endpointProducts, forms_mul_forms, two_mul]

theorem endpointProducts_eq_top_of_le {W W' : Submodule K (Poly K n)}
    (h : W ≤ W') (hW : endpointProducts K n d W = ⊤) :
    endpointProducts K n d W' = ⊤ := by
  apply top_unique
  rw [← hW]
  exact endpointProducts_mono h

/-- The quotient at zero generators is the whole endpoint polynomial space. -/
theorem endpoint_zero_generators (hn : 0 < n) :
    finrank K (EndpointQuotient K n d ⊥) = expectedEndpoint n d 0 := by
  change finrank K ((Forms K n (2 * d)) ⧸ endpointProducts K n d ⊥) = _
  rw [endpointProducts_bot]
  rw [(Submodule.quotEquivOfEqBot (⊥ : Submodule K (Forms K n (2 * d))) rfl).finrank_eq]
  simp [expectedEndpoint, euler, finrank_forms K n (2 * d) hn]

/-- Once all degree-`d` forms are generated, the endpoint quotient vanishes. -/
theorem endpoint_all_generators :
    finrank K (EndpointQuotient K n d (Forms K n d)) = 0 := by
  change finrank K ((Forms K n (2 * d)) ⧸ endpointProducts K n d (Forms K n d)) = 0
  rw [endpointProducts_all]
  exact finrank_zero_of_subsingleton

/-- Multiplication by a genuine degree-`d` form. -/
def mulForm (f : Forms K n d) : Forms K n d →ₗ[K] Forms K n (2 * d) where
  toFun a := ⟨f.val * a.val, by simpa only [Forms, MvPolynomial.mem_homogeneousSubmodule, two_mul] using f.property.mul a.property⟩
  map_add' a b := Subtype.ext (mul_add f.val a.val b.val)
  map_smul' k a := Subtype.ext (mul_smul_comm k f.val a.val)

theorem mulForm_injective (f : Forms K n d) (hf : f.val ≠ 0) :
    Function.Injective (mulForm f) := by
  intro a b hab
  apply Subtype.ext
  exact mul_left_cancel₀ hf (congrArg Subtype.val hab)

theorem range_mulForm (f : Forms K n d) :
    LinearMap.range (mulForm f) = endpointProducts K n d (Submodule.span K {f.val}) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact Submodule.mem_span_singleton_mul.mpr ⟨a.val, a.property, rfl⟩
  · intro hz
    obtain ⟨a, ha, hfa⟩ := Submodule.mem_span_singleton_mul.mp hz
    exact ⟨⟨a, ha⟩, Subtype.ext hfa⟩

/-- Every nonzero form has the expected endpoint quotient for one generator. -/
theorem endpoint_single_generator (hn : 0 < n) (f : Forms K n d) (hf : f.val ≠ 0) :
    finrank K (EndpointQuotient K n d (Submodule.span K {f.val})) =
      expectedEndpoint n d 1 := by
  have hdim : finrank K (endpointProducts K n d (Submodule.span K {f.val})) =
      (n + d - 1).choose d := by
    rw [← range_mulForm]
    exact (LinearMap.finrank_range_of_inj (mulForm_injective f hf)).trans
      (finrank_forms K n d hn)
  have h := (endpointProducts K n d (Submodule.span K {f.val})).finrank_quotient_add_finrank
  rw [hdim, finrank_forms K n (2 * d) hn] at h
  change finrank K ((Forms K n (2 * d)) ⧸ endpointProducts K n d _) = _
  simp only [expectedEndpoint, euler, Nat.choose_eq_zero_of_lt (by omega : 1 < 2),
    Nat.cast_zero, Nat.cast_one, one_mul, add_zero]
  omega

end Froberg
