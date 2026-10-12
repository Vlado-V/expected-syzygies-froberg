module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Algebra.CharZero.Infinite

@[expose] public section

/-! An independent formulation of the manuscript's implication. This module
imports Mathlib only. Its dimensions are homogeneous images in actual ideal
quotient rings, and its parameter spaces contain every ordered form tuple. -/
noncomputable section
namespace ESCtoFroberg.Independent
open MvPolynomial Module

abbrev PolynomialRing (K : Type*) [Field K] (n : ℕ) := MvPolynomial (Fin n) K
abbrev DegreeForms (K : Type*) [Field K] (n d : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin n) K d

variable (K : Type*) [Field K]

def degreeBasis (n d : ℕ) : Basis (Sym (Fin n) d) K (DegreeForms K n d) := by
  rw [DegreeForms, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact (MvPolynomial.basisRestrictSupport K {e : Fin n →₀ ℕ | e.degree = d}).reindex
    (Sym.equivNatSum (Fin n) d).symm

abbrev Coefficients (n d r : ℕ) := Fin r × Sym (Fin n) d

def generator (n d r : ℕ) (a : Coefficients n d r → K) (i : Fin r) :
    DegreeForms K n d := (degreeBasis K n d).equivFun.symm (fun monomial => a (i, monomial))

/-- The coefficient parameter space represents every ordered homogeneous form tuple. -/
theorem every_form_tuple_has_coordinates (n d r : ℕ) (q : Fin r → DegreeForms K n d) :
    ∃ a : Coefficients n d r → K, ∀ i, generator K n d r a i = q i := by
  refine ⟨fun pair => (degreeBasis K n d).equivFun (q pair.1) pair.2, ?_⟩
  intro i
  exact (degreeBasis K n d).equivFun.symm_apply_apply (q i)

def generatorIdeal (n d r : ℕ) (a : Coefficients n d r → K) :
    Ideal (PolynomialRing K n) :=
  Ideal.span (Set.range (fun i => (generator K n d r a i).val))

/-- The degree-`t` piece of `K[x₁,…,xₙ]/I` is its homogeneous image. -/
def quotientDegreeMap {n : ℕ} (I : Ideal (PolynomialRing K n)) (t : ℕ) :
    DegreeForms K n t →ₗ[K] PolynomialRing K n ⧸ I :=
  (Ideal.Quotient.mkₐ K I).toLinearMap.comp (DegreeForms K n t).subtype

def quotientHilbertFunction {n : ℕ} (I : Ideal (PolynomialRing K n)) (t : ℕ) : ℕ :=
  finrank K (quotientDegreeMap K I t).range

/-- The power series `(1-u^d)^r/(1-u)^n`, with integer coefficients. -/
def rawSeries (n d r : ℕ) : PowerSeries ℤ :=
  (1 - PowerSeries.X ^ d) ^ r * (PowerSeries.invOneSubPow ℤ n).val

def rawCoefficient (n d r t : ℕ) : ℤ := PowerSeries.coeff t (rawSeries n d r)

def positivelyTruncated (n d r t : ℕ) : ℕ := by
  classical
  exact if ∀ j ≤ t, 0 < rawCoefficient n d r j
    then (rawCoefficient n d r t).toNat else 0

/-- The conclusion uses one nonempty principal open for all degrees through `2d`. -/
def GeneralFormsThrough2d : Prop :=
  ∀ n d : ℕ, 1 ≤ n → 1 ≤ d → ∀ r : ℕ,
    ∃ D : MvPolynomial (Coefficients n d r) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 → ∀ t ≤ 2 * d,
        quotientHilbertFunction K (generatorIdeal K n d r a) t =
          positivelyTruncated n d r t

abbrev PointParameters (m p : ℕ) := Fin p × Fin m → K

def representative {m p : ℕ} (a : PointParameters K m p) (i : Fin p) :
    Fin (m + 1) → K := Fin.lastCases 1 (fun j => a (i, j))

def distinct {m p : ℕ} (a : PointParameters K m p) : Prop :=
  Function.Injective (fun i => fun j => a (i, j))

/-- These are all homogeneous degree-`d` polynomials vanishing at the points. -/
def pointEquations {m p : ℕ} (a : PointParameters K m p) (d : ℕ) :
    Set (PolynomialRing K (m + 1)) :=
  {f | f.IsHomogeneous d ∧ ∀ i, eval (representative K a i) f = 0}

def pointChop {m p : ℕ} (a : PointParameters K m p) (d : ℕ) :
    Ideal (PolynomialRing K (m + 1)) := Ideal.span (pointEquations K a d)

def monomialCount (n t : ℕ) : ℕ := (n + t - 1).choose t

def leastInterpolationDegree (n p d : ℕ) : Prop :=
  p ≤ monomialCount n d ∧ ∀ j < d, monomialCount n j < p

/-- No threshold through `e` means precisely that `e` precedes `e₀`; when no
threshold exists this remains true in every finite degree. -/
def beforePlateau (n p d e : ℕ) : Prop :=
  ∀ i ≤ e, 1 ≤ i → (p : ℤ) < rawCoefficient n d (monomialCount n d - p) (d + i)

def expectedChopDimension (n p d e : ℕ) : ℕ := by
  classical
  exact if beforePlateau n p d e
    then (rawCoefficient n d (monomialCount n d - p) (d + e)).toNat else p

/-- Conjecture 2.2, with projective dimension `m` and `m+1` variables. -/
def ExpectedSyzygies : Prop :=
  ∀ m p d : ℕ, 1 ≤ m → 1 ≤ p → 1 ≤ d →
    leastInterpolationDegree (m + 1) p d →
    ∃ D : MvPolynomial (Fin p × Fin m) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        distinct K a ∧ ∀ e : ℕ,
          quotientHilbertFunction K (pointChop K a d) (d + e) =
            expectedChopDimension (m + 1) p d e

/-- The manuscript's characteristic-zero implication for every number of
variables, positive degree, and number of generators. -/
def Theorem11 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K], ExpectedSyzygies K → GeneralFormsThrough2d K

end ESCtoFroberg.Independent
