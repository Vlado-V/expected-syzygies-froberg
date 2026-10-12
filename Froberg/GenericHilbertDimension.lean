module

public import Froberg.Prefix

@[expose] public section

/-! Actual generic Hilbert dimensions in every degree, with a proved common
nonempty principal open for any finite collection of degrees. -/
noncomputable section
namespace Froberg
open Module MvPolynomial

variable (K : Type*) [Field K] (n d r : ℕ)

theorem hilbert_value_exists (j : ℕ) :
    ∃ c, ∃ a : CoefficientIndex n d r → K,
      hilbertFunction (coefficientSpace K n d r a) j = c :=
  ⟨_, (fun _ => 0), rfl⟩

/-- The least actual quotient dimension among all ordered degree-`d` tuples. -/
def genericHilbertDimension (j : ℕ) : ℕ := by
  classical
  exact Nat.find (hilbert_value_exists K n d r j)

theorem genericHilbertDimension_attained (j : ℕ) :
    ∃ a : CoefficientIndex n d r → K,
      hilbertFunction (coefficientSpace K n d r a) j = genericHilbertDimension K n d r j := by
  classical
  exact Nat.find_spec (hilbert_value_exists K n d r j)

theorem genericHilbertDimension_le (j : ℕ) (a : CoefficientIndex n d r → K) :
    genericHilbertDimension K n d r j ≤ hilbertFunction (coefficientSpace K n d r a) j := by
  classical
  exact Nat.find_min' (hilbert_value_exists K n d r j) ⟨a, rfl⟩

/-- Rank minors make the minimum constant on a nonempty principal open. -/
theorem genericHilbertDimension_principal_open (hn : 0 < n) (j : ℕ) :
    ∃ D : MvPolynomial (CoefficientIndex n d r) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        hilbertFunction (coefficientSpace K n d r a) j = genericHilbertDimension K n d r j := by
  classical
  obtain ⟨a₀, ha₀⟩ := genericHilbertDimension_attained K n d r j
  by_cases hj : j < d
  · refine ⟨1, ⟨a₀, by simp⟩, fun a _ => ?_⟩
    have h₀ := hilbertFunction_below_degree hn j hj _
      (coefficientSpace_homogeneous K n d r a₀)
    have h₁ := hilbertFunction_below_degree hn j hj _
      (coefficientSpace_homogeneous K n d r a)
    omega
  · let e := j - d
    have he : d + e = j := Nat.add_sub_of_le (by omega)
    obtain ⟨D, hD, hprop⟩ := rank_principal_open
      (coefficientPrefixMultiplication (K := K) (n := n) (d := d) (r := r) e) a₀
    refine ⟨D, ⟨a₀, hD⟩, fun a ha => ?_⟩
    have h₀ := prefix_hilbert_add_rank (e := e) hn (coefficientForms K n d r a₀)
    have h₁ := prefix_hilbert_add_rank (e := e) hn (coefficientForms K n d r a)
    change hilbertFunction (coefficientSpace K n d r a₀) (d + e) + _ = _ at h₀
    change hilbertFunction (coefficientSpace K n d r a) (d + e) + _ = _ at h₁
    have ha₀' : hilbertFunction (coefficientSpace K n d r a₀) (d + e) =
        genericHilbertDimension K n d r j := by simpa only [he] using ha₀
    have ha' : hilbertFunction (coefficientSpace K n d r a) (d + e) =
        hilbertFunction (coefficientSpace K n d r a) j := congrArg _ he
    rw [ha₀'] at h₀
    rw [ha'] at h₁
    have hmin := genericHilbertDimension_le K n d r j a
    have hr := hprop a ha
    change finrank K (prefixMultiplication (coefficientForms K n d r a₀) e).range ≤
      finrank K (prefixMultiplication (coefficientForms K n d r a) e).range at hr
    omega

/-- All these generic values occur on the same nonempty principal open. -/
theorem genericHilbertDimension_through_principal_open [Infinite K]
    (hn : 0 < n) (bound : ℕ) :
    ∃ D : MvPolynomial (CoefficientIndex n d r) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 → ∀ j ≤ bound,
        hilbertFunction (coefficientSpace K n d r a) j = genericHilbertDimension K n d r j := by
  obtain ⟨D, hD, hprop⟩ := finite_principal_open_intersection (Finset.range (bound + 1))
    (fun j a => hilbertFunction (coefficientSpace K n d r a) j =
      genericHilbertDimension K n d r j)
    (fun j _ => genericHilbertDimension_principal_open K n d r hn j)
  exact ⟨D, hD, fun a ha j hj => hprop a ha j (Finset.mem_range.mpr (by omega))⟩

variable {K n d r}

/-- The open-set formulation and the numerical generic dimension agree. -/
theorem genericHilbertAt_iff_genericHilbertDimension [Infinite K]
    (hn : 0 < n) (j : ℕ) :
    GenericHilbertAt K n d r j ↔
      genericHilbertDimension K n d r j = predictedHilbertFunction n d r j := by
  constructor
  · rintro ⟨D, hD, hprop⟩
    obtain ⟨E, hE, hmin⟩ := genericHilbertDimension_principal_open K n d r hn j
    obtain ⟨a, haD, haE⟩ := principal_opens_intersect hD hE
    exact (hmin a haE).symm.trans (hprop a haD)
  · intro h
    obtain ⟨D, hD, hprop⟩ := genericHilbertDimension_principal_open K n d r hn j
    exact ⟨D, hD, fun a ha => (hprop a ha).trans h⟩

theorem genericHilbertThrough_iff_genericHilbertDimension [Infinite K]
    (hn : 0 < n) (bound : ℕ) :
    GenericHilbertThrough K n d r bound ↔ ∀ j ≤ bound,
      genericHilbertDimension K n d r j = predictedHilbertFunction n d r j := by
  rw [genericHilbertThrough_iff]
  exact forall_congr' fun j => forall_congr' fun _ =>
    genericHilbertAt_iff_genericHilbertDimension hn j

/-- At the endpoint this general minimum is the original cokernel minimum. -/
theorem genericHilbertDimension_endpoint :
    genericHilbertDimension K n d r (2 * d) = genericCokernel K n d r := by
  obtain ⟨a, ha⟩ := genericHilbertDimension_attained K n d r (2 * d)
  obtain ⟨b, hb⟩ := genericCokernel_attained K n d r
  have h₁ := genericHilbertDimension_le K n d r (2 * d) b
  have h₂ := genericCokernel_le K n d r a
  unfold coefficientCokernel at hb h₂
  rw [endpoint_finrank_eq_hilbertFunction _ (coefficientSpace_homogeneous K n d r b)] at hb
  rw [endpoint_finrank_eq_hilbertFunction _ (coefficientSpace_homogeneous K n d r a)] at h₂
  omega

end Froberg
