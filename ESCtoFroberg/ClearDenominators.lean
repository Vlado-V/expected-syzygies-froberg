module

public import ESCtoFroberg.GenericRename
public import Mathlib.RingTheory.Localization.Integer

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open MvPolynomial

/-- A finite homogeneous family over a fraction field can be represented by
homogeneous polynomials over the original domain after one common scaling. -/
theorem homogeneous_family_clear_denominators
    {A R ι σ : Type*} [CommRing A] [IsDomain A] [Field R]
    [Algebra A R] [IsFractionRing A R] [Fintype ι]
    (d : ℕ) (q : ι → MvPolynomial σ R)
    (hq : ∀ i, (q i).IsHomogeneous d) :
    ∃ D : A, D ≠ 0 ∧ ∃ Q : ι → MvPolynomial σ A,
      (∀ i, (Q i).IsHomogeneous d) ∧
      ∀ i, MvPolynomial.map (algebraMap A R) (Q i) =
        C (algebraMap A R D) * q i := by
  classical
  let s : Finset (ι × (σ →₀ ℕ)) :=
    Finset.univ.biUnion fun i => (q i).support.image fun e => (i, e)
  have hs (i : ι) (e : σ →₀ ℕ) (he : e ∈ (q i).support) : (i, e) ∈ s := by
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
  obtain ⟨D, hD⟩ := IsLocalization.exist_integer_multiples
    (nonZeroDivisors A) s (fun ie => (q ie.1).coeff ie.2)
  have hc : ∀ i e, e ∈ (q i).support → ∃ c : A,
      algebraMap A R c = (D : A) • (q i).coeff e := by
    intro i e he
    exact hD (i,e) (hs i e he)
  let c : ι → (σ →₀ ℕ) → A := fun i e =>
    if he : e ∈ (q i).support then (hc i e he).choose else 0
  have hce (i : ι) (e : σ →₀ ℕ) (he : e ∈ (q i).support) :
      algebraMap A R (c i e) = (D : A) • (q i).coeff e := by
    simp only [c, dite_eq_left he]
    exact (hc i e he).choose_spec
  let Q : ι → MvPolynomial σ A := fun i =>
    ∑ e ∈ (q i).support, monomial e (c i e)
  refine ⟨D, nonZeroDivisors.coe_ne_zero D, Q, ?_, ?_⟩
  · intro i
    apply IsHomogeneous.sum
    intro e he
    exact isHomogeneous_monomial _ (by
      simpa only [Finsupp.degree_apply] using
        ((hq i).degree_eq_sum_deg_support he).symm)
  · intro i
    change MvPolynomial.map (algebraMap A R)
      (∑ e ∈ (q i).support, monomial e (c i e)) = _
    rw [map_sum]
    calc
      _ = ∑ e ∈ (q i).support,
          monomial e (algebraMap A R D * (q i).coeff e) := by
        apply Finset.sum_congr rfl
        intro e he
        rw [map_monomial, hce i e he, Algebra.smul_def]
      _ = C (algebraMap A R D) * q i := by
        conv_rhs => rw [(q i).as_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        rw [C_mul_monomial]

section GenericPoints
variable {K : Type*} [Field K] {m p d : ℕ}

/-- Normalized points with polynomial coordinates before passage to the fraction field. -/
def pointRingChart (K : Type*) [Field K] (m p : ℕ) (i : Fin p) :
    Fin (m+1) → GenericPointRing K m p :=
  Fin.lastCases 1 (fun j => X (i,j))

theorem generic_chartPoint_eq_map (i : Fin p) :
    chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) i =
      fun j => algebraMap (GenericPointRing K m p) (GenericPointField K m p)
        (pointRingChart K m p i j) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j <;>
    simp [pointRingChart, chartPoint, genericPointCoordinates]

theorem eval_generic_map (Q : MvPolynomial (Fin (m+1)) (GenericPointRing K m p))
    (i : Fin p) :
    eval (chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) i)
      (MvPolynomial.map
        (algebraMap (GenericPointRing K m p) (GenericPointField K m p)) Q) =
    algebraMap (GenericPointRing K m p) (GenericPointField K m p)
      (eval (pointRingChart K m p i) Q) := by
  rw [generic_chartPoint_eq_map]
  rw [eval_map]
  exact (eval₂_comp
    (algebraMap (GenericPointRing K m p) (GenericPointField K m p))
    (pointRingChart K m p i) Q).symm

theorem eval_specialized_map
    (Q : MvPolynomial (Fin (m+1)) (GenericPointRing K m p))
    (a : PointCoordinates K m p) (i : Fin p) :
    eval (chartPoint K a i) (MvPolynomial.map (eval a) Q) =
      eval a (eval (pointRingChart K m p i) Q) := by
  rw [eval_map]
  have hc : chartPoint K a i = (eval a) ∘ pointRingChart K m p i := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j <;> simp [pointRingChart, chartPoint]
  rw [hc]
  exact (eval₂_comp (eval a) (pointRingChart K m p i) Q).symm

/-- An equation at universal points is a polynomial identity, so every actual
configuration satisfies the specialized equation. -/
theorem universal_point_equation_specializes
    (Q : MvPolynomial (Fin (m+1)) (GenericPointRing K m p))
    (hQ : ∀ i : Fin p,
      eval (chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) i)
        (MvPolynomial.map
          (algebraMap (GenericPointRing K m p) (GenericPointField K m p)) Q) = 0)
    (a : PointCoordinates K m p) (i : Fin p) :
    eval (chartPoint K a i) (MvPolynomial.map (eval a) Q) = 0 := by
  rw [eval_specialized_map]
  have h := hQ i
  rw [eval_generic_map] at h
  have hz : eval (pointRingChart K m p i) Q = 0 :=
    IsFractionRing.injective (GenericPointRing K m p) (GenericPointField K m p)
      (h.trans (map_zero _).symm)
  rw [hz, map_zero]

/-- Specialization preserves the degree of a homogeneous polynomial family. -/
def specializedForms {ι : Type*}
    (Q : ι → MvPolynomial (Fin (m+1)) (GenericPointRing K m p))
    (hQ : ∀ i, (Q i).IsHomogeneous d) (a : PointCoordinates K m p) :
    ι → Forms K (m+1) d :=
  fun i => ⟨MvPolynomial.map (eval a) (Q i), (hQ i).map (eval a)⟩

/-- Clear a family of universal vanishing forms by one denominator.  Every
specialization still consists of equations of its actual point configuration. -/
theorem generic_vanishing_family_clear_denominators {ι : Type*} [Fintype ι]
    (q : ι → Forms (GenericPointField K m p) (m+1) d)
    (hq : ∀ i j,
      eval (chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) j)
        (q i).val = 0) :
    ∃ D : GenericPointRing K m p, D ≠ 0 ∧
      ∃ Q : ι → MvPolynomial (Fin (m+1)) (GenericPointRing K m p),
      ∃ hQ : ∀ i, (Q i).IsHomogeneous d,
        (∀ i, MvPolynomial.map
          (algebraMap (GenericPointRing K m p) (GenericPointField K m p)) (Q i) =
            C (algebraMap (GenericPointRing K m p) (GenericPointField K m p) D) * (q i).val) ∧
        ∀ a i, specializedForms Q hQ a i ∈ pointDegreePiece K a d := by
  obtain ⟨D,hD,Q,hQ,hmap⟩ := homogeneous_family_clear_denominators
    (A := GenericPointRing K m p) d (fun i => (q i).val) (fun i => (q i).property)
  refine ⟨D,hD,Q,hQ,hmap,?_⟩
  intro a i
  change pointEvaluation K a d (specializedForms Q hQ a i) = 0
  funext j
  apply universal_point_equation_specializes (Q i) ?_ a j
  intro k
  rw [hmap i, map_mul, hq i k, mul_zero]

end GenericPoints

end ESCtoFroberg
