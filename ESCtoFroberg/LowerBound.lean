module

public import ESCtoFroberg.ZeroPersistence

@[expose] public section

/-! Universal raw coefficient lower bounds through `2*d`, first for actual
independent forms and then for the actual generic quotient dimensions. -/
noncomputable section
namespace ESCtoFroberg
open Module MvPolynomial Froberg

variable {K : Type*} [Field K] {n d r : ℕ}

/-- Independent degree-`d` forms have at least the positive part of the raw
Koszul coefficient in every degree through twice the generating degree. -/
theorem hilbertFunction_raw_lower_bound (hn : 0 < n) (hd : 0 < d)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (t : ℕ) (ht : t ≤ 2 * d) :
    (predictionCoefficient n d r t).toNat ≤ hilbertFunction (familySpace q) t := by
  by_cases htd : t < d
  · rw [predictionCoefficient_below_degree n d r t hn htd]
    rw [hilbertFunction_below_degree hn t htd _ (familySpace_homogeneous q)]
    simp
  · by_cases hte : t < 2 * d
    · rw [predictionCoefficient_before_endpoint n d r t hn (by omega) hte]
      have hlow := prefix_hilbert_lower_bound (e := t - d) hn q
      have he : d + (t - d) = t := Nat.add_sub_of_le (by omega)
      rw [he] at hlow
      rw [← Int.natCast_mul]
      omega
    · have he : t = 2 * d := by omega
      subst t
      rw [predictionCoefficient_at_endpoint n d r hn hd]
      have hlow := endpoint_quotient_lower_bound hn q hq
      change expectedEndpoint n d r ≤ finrank K (EndpointQuotient K n d (familySpace q)) at hlow
      rw [endpoint_finrank_eq_hilbertFunction _ (familySpace_homogeneous q)] at hlow
      exact hlow

/-- Any one-degree generic minimum can be attained by an independent tuple,
by intersecting its rank open with the generator-independence open. -/
theorem independent_genericHilbertDimension_attained [Infinite K]
    (hn : 0 < n) (hr : r ≤ (n + d - 1).choose d) (t : ℕ) :
    ∃ a : CoefficientIndex n d r → K,
      LinearIndependent K (coefficientForms K n d r a) ∧
      hilbertFunction (coefficientSpace K n d r a) t =
        genericHilbertDimension K n d r t := by
  obtain ⟨D, hD, hmin⟩ := genericHilbertDimension_principal_open K n d r hn t
  obtain ⟨E, hE, hind⟩ := coefficient_independence_principal_open (K := K) hn hr
  obtain ⟨a, haD, haE⟩ := principal_opens_intersect hD hE
  exact ⟨a, hind a haE, hmin a haD⟩

/-- The actual generic quotient dimension satisfies the same raw lower bound. -/
theorem genericHilbertDimension_raw_lower_bound [Infinite K]
    (hn : 0 < n) (hd : 0 < d) (hr : r ≤ (n + d - 1).choose d)
    (t : ℕ) (ht : t ≤ 2 * d) :
    (predictionCoefficient n d r t).toNat ≤ genericHilbertDimension K n d r t := by
  obtain ⟨a, ha, hmin⟩ := independent_genericHilbertDimension_attained (K := K) hn hr t
  have h := hilbertFunction_raw_lower_bound hn hd (coefficientForms K n d r a) ha t ht
  change (predictionCoefficient n d r t).toNat ≤
    hilbertFunction (coefficientSpace K n d r a) t at h
  rwa [hmin] at h

/-- Every coefficient tuple has at least the generic minimum, so the raw lower
bound extends to dependent tuples when there is room for `r` independent forms. -/
theorem coefficientHilbertFunction_raw_lower_bound [Infinite K]
    (hn : 0 < n) (hd : 0 < d) (hr : r ≤ (n + d - 1).choose d)
    (t : ℕ) (ht : t ≤ 2 * d) (a : CoefficientIndex n d r → K) :
    (predictionCoefficient n d r t).toNat ≤ hilbertFunction (coefficientSpace K n d r a) t :=
  (genericHilbertDimension_raw_lower_bound (K := K) hn hd hr t ht).trans
    (genericHilbertDimension_le K n d r t a)

/-- An actual tuple reaching the raw value gives the generic raw value;
its independence is unnecessary because the minimum has the proved lower bound. -/
theorem genericRawHilbertAt_of_coefficient_witness [Infinite K]
    (hn : 0 < n) (hd : 0 < d) (hr : r ≤ (n + d - 1).choose d)
    (t : ℕ) (ht : t ≤ 2 * d) (a₀ : CoefficientIndex n d r → K)
    (ha₀ : hilbertFunction (coefficientSpace K n d r a₀) t =
      (predictionCoefficient n d r t).toNat) : GenericRawHilbertAt K n d r t := by
  apply (genericRawHilbertAt_iff_genericHilbertDimension hn t).mpr
  have hlow := genericHilbertDimension_raw_lower_bound (K := K) hn hd hr t ht
  have hupp := genericHilbertDimension_le K n d r t a₀
  omega

/-- The corresponding witness conversion in homogeneous family coordinates. -/
theorem genericRawHilbertAt_of_family_witness [Infinite K]
    (hn : 0 < n) (hd : 0 < d) (hr : r ≤ (n + d - 1).choose d)
    (t : ℕ) (ht : t ≤ 2 * d) (q : Fin r → Forms K n d)
    (hq : hilbertFunction (familySpace q) t = (predictionCoefficient n d r t).toNat) :
    GenericRawHilbertAt K n d r t := by
  have hq' : coefficientForms K n d r (coefficientCoordinates q) = q :=
    coefficientCoordinates.symm_apply_apply q
  apply genericRawHilbertAt_of_coefficient_witness hn hd hr t ht (coefficientCoordinates q)
  change hilbertFunction (familySpace (coefficientForms K n d r (coefficientCoordinates q))) t = _
  rwa [hq']

end ESCtoFroberg
