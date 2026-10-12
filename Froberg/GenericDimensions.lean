module

public import Froberg.Generic
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

/-! Generic dimensions are minima of actual quotient dimensions.  Their rank
opens are proved nonempty; no generic-rank assertion is part of the definition. -/
noncomputable section
namespace Froberg
open Module MvPolynomial

variable (K : Type*) [Field K] (n d r : ℕ)

def coefficientCokernel (a : CoefficientIndex n d r → K) : ℕ :=
  finrank K (EndpointQuotient K n d (coefficientSpace K n d r a))

theorem cokernel_value_exists :
    ∃ c, ∃ a : CoefficientIndex n d r → K, coefficientCokernel K n d r a = c :=
  ⟨_, (fun _ => 0), rfl⟩

/-- The generic endpoint quotient dimension, defined without any rank hypothesis. -/
def genericCokernel : ℕ := by
  classical
  exact Nat.find (cokernel_value_exists K n d r)

theorem genericCokernel_attained :
    ∃ a : CoefficientIndex n d r → K,
      coefficientCokernel K n d r a = genericCokernel K n d r := by
  classical
  exact Nat.find_spec (cokernel_value_exists K n d r)

theorem genericCokernel_le (a : CoefficientIndex n d r → K) :
    genericCokernel K n d r ≤ coefficientCokernel K n d r a := by
  classical
  exact Nat.find_min' (cokernel_value_exists K n d r) ⟨a, rfl⟩

/-- The minimum is the value throughout a nonempty principal open. -/
theorem genericCokernel_principal_open (hn : 0 < n) :
    ∃ D : MvPolynomial (CoefficientIndex n d r) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        coefficientCokernel K n d r a = genericCokernel K n d r := by
  classical
  obtain ⟨a₀, ha₀⟩ := genericCokernel_attained K n d r
  obtain ⟨D, hD, hDprop⟩ := rank_principal_open
    (coefficientMultiplicationLinear (K := K) (n := n) (d := d) (r := r)) a₀
  refine ⟨D, ⟨a₀, hD⟩, fun a ha => ?_⟩
  have hmin := genericCokernel_le K n d r a
  have hrank := hDprop a ha
  have hbefore := endpoint_quotient_add_rank hn (coefficientForms K n d r a₀)
  have hafter := endpoint_quotient_add_rank hn (coefficientForms K n d r a)
  change coefficientCokernel K n d r a₀ + _ = _ at hbefore
  change coefficientCokernel K n d r a + _ = _ at hafter
  change finrank K (endpointMultiplication (coefficientForms K n d r a₀)).range ≤
    finrank K (endpointMultiplication (coefficientForms K n d r a)).range at hrank
  omega

variable {K n d r}

theorem principal_opens_intersect [Infinite K] {ι : Type*}
    {D E : MvPolynomial ι K}
    (hD : ∃ a, eval a D ≠ 0) (hE : ∃ a, eval a E ≠ 0) :
    ∃ a, eval a D ≠ 0 ∧ eval a E ≠ 0 := by
  classical
  have hD0 : D ≠ 0 := by rintro rfl; simp at hD
  have hE0 : E ≠ 0 := by rintro rfl; simp at hE
  by_contra h
  apply mul_ne_zero hD0 hE0
  apply MvPolynomial.funext
  intro a
  simp only [map_mul, map_zero]
  by_cases ha : eval a D = 0
  · simp [ha]
  · have hb : eval a E = 0 := by
      by_contra hb
      exact h ⟨a, ha, hb⟩
    simp [hb]

theorem coefficient_independence_principal_open (hn : 0 < n)
    (hr : r ≤ (n + d - 1).choose d) :
    ∃ D : MvPolynomial (CoefficientIndex n d r) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        LinearIndependent K (coefficientForms K n d r a) := by
  classical
  have hdim : r ≤ finrank K (Forms K n d) := by rwa [finrank_forms K n d hn]
  obtain ⟨q, hq⟩ := exists_linearIndependent_of_le_finrank hdim
  let a₀ := coefficientCoordinates (K := K) (n := n) (d := d) (r := r) q
  have ha₀ : coefficientForms K n d r a₀ = q :=
    coefficientCoordinates.symm_apply_apply q
  let family : Fin r → (CoefficientIndex n d r → K) →ₗ[K] Forms K n d := fun i =>
    (formsBasis K n d).equivFun.symm.toLinearMap.comp
      (LinearMap.funLeft K K (fun m => (i, m)))
  obtain ⟨D, hD, hprop⟩ := independent_principal_open family a₀ (by
    change LinearIndependent K (coefficientForms K n d r a₀)
    rwa [ha₀])
  exact ⟨D, ⟨a₀, hD⟩, hprop⟩

/-- The generic quotient minimum can always be attained by independent generators. -/
theorem independent_genericCokernel_attained [Infinite K] (hn : 0 < n)
    (hr : r ≤ (n + d - 1).choose d) :
    ∃ a : CoefficientIndex n d r → K,
      LinearIndependent K (coefficientForms K n d r a) ∧
      coefficientCokernel K n d r a = genericCokernel K n d r := by
  obtain ⟨D, hD, hDprop⟩ := genericCokernel_principal_open K n d r hn
  obtain ⟨E, hE, hEprop⟩ := coefficient_independence_principal_open (K := K) hn hr
  obtain ⟨a, haD, haE⟩ := principal_opens_intersect hD hE
  exact ⟨a, hEprop a haE, hDprop a haD⟩

/-- The generic homology dimension, computed from the Euler characteristic. -/
def genericHomology (K : Type*) [Field K] (n d r : ℕ) : ℕ :=
  ((genericCokernel K n d r : ℤ) - euler n d r).toNat

theorem generic_euler [Infinite K] (hn : 0 < n)
    (hr : r ≤ (n + d - 1).choose d) :
    (genericCokernel K n d r : ℤ) - genericHomology K n d r = euler n d r := by
  obtain ⟨a, hi, ha⟩ := independent_genericCokernel_attained (K := K) hn hr
  have he := endpoint_euler_identity hn (coefficientForms K n d r a) hi
  change (coefficientCokernel K n d r a : ℤ) - _ = _ at he
  rw [ha] at he
  unfold genericHomology
  omega

theorem genericHomology_eq_at_generic (hn : 0 < n)
    (a : CoefficientIndex n d r → K)
    (hi : LinearIndependent K (coefficientForms K n d r a))
    (ha : coefficientCokernel K n d r a = genericCokernel K n d r) :
    genericHomology K n d r =
      finrank K (EndpointHomology (coefficientForms K n d r a)) := by
  have he := endpoint_euler_identity hn (coefficientForms K n d r a) hi
  change (coefficientCokernel K n d r a : ℤ) - _ = _ at he
  rw [ha] at he
  unfold genericHomology
  omega

theorem genericHomology_le (hn : 0 < n)
    (a : CoefficientIndex n d r → K)
    (hi : LinearIndependent K (coefficientForms K n d r a)) :
    genericHomology K n d r ≤
      finrank K (EndpointHomology (coefficientForms K n d r a)) := by
  have he := endpoint_euler_identity hn (coefficientForms K n d r a) hi
  change (coefficientCokernel K n d r a : ℤ) - _ = _ at he
  have hle := genericCokernel_le K n d r a
  unfold genericHomology
  omega

theorem genericEndpoint_iff_genericCokernel [Infinite K] (hn : 0 < n)
    (hr : r ≤ (n + d - 1).choose d) :
    GenericEndpoint K n d r ↔ genericCokernel K n d r = expectedEndpoint n d r := by
  constructor
  · rintro ⟨D, ⟨a, ha⟩, h⟩
    obtain ⟨hi, he⟩ := h a ha
    rw [← endpoint_finrank_eq_hilbertFunction _ (coefficientSpace_homogeneous K n d r a)] at he
    have hle := genericCokernel_le K n d r a
    obtain ⟨b, hb, hg⟩ := independent_genericCokernel_attained (K := K) hn hr
    have hlow := endpoint_quotient_lower_bound hn (coefficientForms K n d r b) hb
    change expectedEndpoint n d r ≤ coefficientCokernel K n d r b at hlow
    change coefficientCokernel K n d r a = expectedEndpoint n d r at he
    omega
  · intro he
    obtain ⟨a, hi, ha⟩ := independent_genericCokernel_attained (K := K) hn hr
    exact genericEndpoint_of_coefficient_witness hn a hi (ha.trans he)

theorem genericCokernel_le_family (q : Fin r → Forms K n d) :
    genericCokernel K n d r ≤ finrank K (EndpointQuotient K n d
      (Submodule.span K (Set.range (fun i => (q i).val)))) := by
  have h := genericCokernel_le K n d r (coefficientCoordinates q)
  have ha : coefficientForms K n d r (coefficientCoordinates q) = q :=
    coefficientCoordinates.symm_apply_apply q
  unfold coefficientCokernel coefficientSpace at h
  rw [ha] at h
  exact h

/-- Adding a generator cannot increase the generic quotient dimension. -/
theorem genericCokernel_succ_le :
    genericCokernel K n d (r + 1) ≤ genericCokernel K n d r := by
  classical
  obtain ⟨a, ha⟩ := genericCokernel_attained K n d r
  let q := coefficientForms K n d r a
  let q' : Fin (r + 1) → Forms K n d := Fin.snoc q 0
  have hspan : Submodule.span K (Set.range (fun i => (q' i).val)) =
      coefficientSpace K n d r a := by
    have hrange : Set.range (fun i => (q' i).val) =
        insert 0 (Set.range (fun i => (q i).val)) := by
      have hf : (fun i => (q' i).val) = Fin.snoc (fun i => (q i).val) 0 := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [q']
      rw [hf, Fin.range_snoc]
    rw [hrange, Submodule.span_insert_zero]
    rfl
  have h := genericCokernel_le_family q'
  rw [hspan] at h
  exact h.trans (le_of_eq ha)

theorem genericCokernel_antitone : Antitone (genericCokernel K n d) := by
  apply antitone_nat_of_succ_le
  intro r
  exact genericCokernel_succ_le

end Froberg
