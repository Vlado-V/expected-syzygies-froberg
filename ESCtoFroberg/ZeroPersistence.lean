module

public import ESCtoFroberg.Truncation
public import Froberg.GenericHilbertDimension

@[expose] public section

/-! Actual quotient components remain zero in all later degrees.  This bridges
raw coefficient dimensions and the positive truncation in Fröberg's formula. -/
noncomputable section
namespace ESCtoFroberg
open Module MvPolynomial Froberg

variable {K : Type*} [Field K] {n d r : ℕ}

/-- A zero-dimensional homogeneous quotient component has zero quotient map. -/
theorem formToRingQuotient_eq_zero_of_hilbertFunction_zero
    (W : Submodule K (Poly K n)) (j : ℕ) (hj : hilbertFunction W j = 0) :
    formToRingQuotient j W = 0 := by
  apply LinearMap.range_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  exact hj

/-- Every degree-`j` polynomial belongs to the generated ideal once that
homogeneous quotient component vanishes. -/
theorem form_mem_ideal_of_hilbertFunction_zero
    (W : Submodule K (Poly K n)) (j : ℕ) (hj : hilbertFunction W j = 0)
    (p : Forms K n j) : p.val ∈ Ideal.span (W : Set (Poly K n)) := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := formToRingQuotient_eq_zero_of_hilbertFunction_zero W j hj
  exact LinearMap.congr_fun h p

/-- Vanishing persists in every later actual quotient component.  The result
holds for every generated ideal, without a homogeneity premise on `W`. -/
theorem hilbertFunction_zero_persistence
    (W : Submodule K (Poly K n)) {j k : ℕ} (hjk : j ≤ k)
    (hj : hilbertFunction W j = 0) : hilbertFunction W k = 0 := by
  have hzero : formToRingQuotient k W = 0 := by
    ext p
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change p.val ∈ Ideal.span (W : Set (Poly K n))
    have hp : p.val ∈ Forms K n j * Forms K n (k - j) := by
      rw [forms_mul_forms, Nat.add_sub_of_le hjk]
      exact p.property
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro f hf a _
      exact Ideal.mul_mem_right _ _
        (form_mem_ideal_of_hilbertFunction_zero W j hj ⟨f, hf⟩)
    · intro f g hf hg
      exact Ideal.add_mem _ hf hg
  simp [hilbertFunction, hzero]

variable (K) (n d r)

/-- Raw coefficient dimension on a nonempty principal open of actual tuples. -/
def GenericRawHilbertAt (j : ℕ) : Prop :=
  ∃ D : MvPolynomial (CoefficientIndex n d r) K,
    (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
      hilbertFunction (coefficientSpace K n d r a) j =
        (predictionCoefficient n d r j).toNat

/-- One common open where the actual dimensions agree with the positive parts
of all raw coefficients through the prescribed bound. -/
def GenericRawThrough (bound : ℕ) : Prop :=
  ∃ D : MvPolynomial (CoefficientIndex n d r) K,
    (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 → ∀ j ≤ bound,
      hilbertFunction (coefficientSpace K n d r a) j =
        (predictionCoefficient n d r j).toNat

variable {K n d r}

/-- Finitely many generic degree conditions have a common nonempty open. -/
theorem genericRawThrough_iff [Infinite K] (bound : ℕ) :
    GenericRawThrough K n d r bound ↔ ∀ j ≤ bound, GenericRawHilbertAt K n d r j := by
  constructor
  · rintro ⟨D, hD, hprop⟩ j hj
    exact ⟨D, hD, fun a ha => hprop a ha j hj⟩
  · intro h
    obtain ⟨D, hD, hprop⟩ := finite_principal_open_intersection (Finset.range (bound + 1))
      (fun j a => hilbertFunction (coefficientSpace K n d r a) j =
        (predictionCoefficient n d r j).toNat)
      (fun j hj => h j (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj))
    exact ⟨D, hD, fun a ha j hj => hprop a ha j (Finset.mem_range.mpr (by omega))⟩

/-- The raw open condition is exactly equality with the actual generic minimum. -/
theorem genericRawHilbertAt_iff_genericHilbertDimension [Infinite K]
    (hn : 0 < n) (j : ℕ) :
    GenericRawHilbertAt K n d r j ↔
      genericHilbertDimension K n d r j = (predictionCoefficient n d r j).toNat := by
  constructor
  · rintro ⟨D, hD, hprop⟩
    obtain ⟨E, hE, hmin⟩ := genericHilbertDimension_principal_open K n d r hn j
    obtain ⟨a, haD, haE⟩ := principal_opens_intersect hD hE
    exact (hmin a haE).symm.trans (hprop a haD)
  · intro h
    obtain ⟨D, hD, hprop⟩ := genericHilbertDimension_principal_open K n d r hn j
    exact ⟨D, hD, fun a ha => (hprop a ha).trans h⟩

theorem genericRawThrough_iff_genericHilbertDimension [Infinite K]
    (hn : 0 < n) (bound : ℕ) :
    GenericRawThrough K n d r bound ↔ ∀ j ≤ bound,
      genericHilbertDimension K n d r j = (predictionCoefficient n d r j).toNat := by
  rw [genericRawThrough_iff]
  exact forall_congr' fun j => forall_congr' fun _ =>
    genericRawHilbertAt_iff_genericHilbertDimension hn j

/-- Attainment of a proved universal lower bound supplies the generic raw value. -/
theorem genericRawHilbertAt_of_witness [Infinite K] (hn : 0 < n) (j : ℕ)
    (hlow : ∀ a : CoefficientIndex n d r → K,
      (predictionCoefficient n d r j).toNat ≤ hilbertFunction (coefficientSpace K n d r a) j)
    (a₀ : CoefficientIndex n d r → K)
    (ha₀ : hilbertFunction (coefficientSpace K n d r a₀) j =
      (predictionCoefficient n d r j).toNat) : GenericRawHilbertAt K n d r j := by
  apply (genericRawHilbertAt_iff_genericHilbertDimension hn j).mpr
  obtain ⟨a, ha⟩ := genericHilbertDimension_attained K n d r j
  have h₁ := genericHilbertDimension_le K n d r j a₀
  have h₂ := hlow a
  omega

/-- Actual zero persistence converts the raw coefficient dimensions into the
positive truncation on the very same nonempty open. -/
theorem genericHilbertThrough_of_genericRawThrough (bound : ℕ)
    (h : GenericRawThrough K n d r bound) : GenericHilbertThrough K n d r bound := by
  obtain ⟨D, hD, hprop⟩ := h
  refine ⟨D, hD, fun a ha => ?_⟩
  exact raw_dimensions_eq_positiveTruncation
    (predictionCoefficient n d r) (hilbertFunction (coefficientSpace K n d r a)) bound
    (hprop a ha) (fun i j hij _ hi =>
      hilbertFunction_zero_persistence (coefficientSpace K n d r a) hij hi)

end ESCtoFroberg
