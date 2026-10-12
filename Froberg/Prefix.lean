module

public import Froberg.Statement

@[expose] public section

/-!
# Multiplication and incidence fibers before the endpoint

The linear-algebraic part of Boij–Dannetun–Lundqvist,
"Independence of generic forms and the Fröberg conjecture", §2
(https://arxiv.org/html/2605.03872v1), for arbitrary generating and multiplier
degrees. Every space here consists of actual homogeneous polynomials.

The incidence-fiber identity below is unconditional. It does not assume the
Macaulay growth estimate or the existence of a maximal-rank tuple.
-/

noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type*} [Field K] {n d e r : ℕ}

/-- The ambient polynomial span of an ordered homogeneous family. -/
def familySpace (q : Fin r → Forms K n d) : Submodule K (Poly K n) :=
  Submodule.span K (Set.range (fun i => (q i).val))

theorem familySpace_homogeneous (q : Fin r → Forms K n d) :
    familySpace q ≤ Forms K n d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact (q i).property

/-- Homogeneous multiplication, bilinear in the two factors. -/
def gradedMultiplication : Forms K n d →ₗ[K] Forms K n e →ₗ[K] Forms K n (d + e) where
  toFun f :=
    { toFun := fun g => ⟨f.val * g.val, f.property.mul g.property⟩
      map_add' := fun g h => Subtype.ext (mul_add _ _ _)
      map_smul' := fun c g => Subtype.ext (mul_smul_comm _ _ _) }
  map_add' f g := by
    apply LinearMap.ext
    intro h
    exact Subtype.ext (add_mul _ _ _)
  map_smul' c f := by
    apply LinearMap.ext
    intro g
    exact Subtype.ext (smul_mul_assoc _ _ _)

/-- Degree-`e` relations among a tuple of degree-`d` generators. -/
def prefixMultiplication (q : Fin r → Forms K n d) (e : ℕ) :
    (Fin r → Forms K n e) →ₗ[K] Forms K n (d + e) :=
  ∑ i, (gradedMultiplication (q i)).comp (LinearMap.proj i)

@[simp] theorem prefixMultiplication_val (q : Fin r → Forms K n d)
    (a : Fin r → Forms K n e) :
    (prefixMultiplication q e a).val = ∑ i, (q i).val * (a i).val := by
  simp [prefixMultiplication, gradedMultiplication]

/-- The range is the degree-`d+e` product submodule in the polynomial ring. -/
theorem range_ambient_prefixMultiplication (q : Fin r → Forms K n d) :
    LinearMap.range ((Forms K n (d + e)).subtype.comp (prefixMultiplication q e)) =
      familySpace q * Forms K n e := by
  apply le_antisymm
  · rintro p ⟨a, rfl⟩
    change (prefixMultiplication q e a).val ∈ _
    rw [prefixMultiplication_val]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i, rfl⟩) (a i).property
  · apply Submodule.mul_le.mpr
    intro f hf a ha
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
    refine ⟨fun i => c i • (⟨a, ha⟩ : Forms K n e), ?_⟩
    change (prefixMultiplication q e (fun i => c i • (⟨a, ha⟩ : Forms K n e))).val = _
    simp [prefixMultiplication_val, Finset.sum_mul]

/-- The multiplication image is precisely the kernel of the map to the actual
homogeneous piece of the quotient ring. -/
theorem range_prefixMultiplication (q : Fin r → Forms K n d) :
    LinearMap.range (prefixMultiplication q e) =
      LinearMap.ker (formToRingQuotient (d + e) (familySpace q)) := by
  have h := congrArg (fun P : Submodule K (Poly K n) =>
      P.comap (Forms K n (d + e)).subtype) (range_ambient_prefixMultiplication (e := e) q)
  rw [LinearMap.range_comp,
    Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)] at h
  rw [h]
  ext p
  change p.val ∈ familySpace q * Forms K n e ↔
    Ideal.Quotient.mk (Ideal.span (familySpace q : Set (Poly K n))) p.val = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact (form_mem_ideal_iff e (familySpace q) (familySpace_homogeneous q) p).symm

/-- The Hilbert function is the codimension of actual homogeneous multiplication. -/
theorem prefix_hilbert_add_rank (hn : 0 < n) (q : Fin r → Forms K n d) :
    hilbertFunction (familySpace q) (d + e) +
      finrank K (LinearMap.range (prefixMultiplication q e)) =
        (n + (d + e) - 1).choose (d + e) := by
  rw [range_prefixMultiplication]
  exact (formToRingQuotient (d + e) (familySpace q)).finrank_range_add_finrank_ker |>.trans
    (finrank_forms K n (d + e) hn)

/-- Exact Euler identity at any degree. Below `2*d` no Koszul boundary is subtracted. -/
theorem prefix_euler_identity (hn : 0 < n) (q : Fin r → Forms K n d) :
    hilbertFunction (familySpace q) (d + e) + r * (n + e - 1).choose e =
      (n + (d + e) - 1).choose (d + e) +
        finrank K (LinearMap.ker (prefixMultiplication q e)) := by
  have h₁ := prefix_hilbert_add_rank (e := e) hn q
  have h₂ := (prefixMultiplication q e).finrank_range_add_finrank_ker
  rw [Module.finrank_pi_fintype, finrank_forms K n e hn] at h₂
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h₂
  norm_num only [Nat.cast_id] at h₂
  omega

/-- Universal dimension lower bound; this statement makes no genericity assumption. -/
theorem prefix_hilbert_lower_bound (hn : 0 < n) (q : Fin r → Forms K n d) :
    (n + (d + e) - 1).choose (d + e) - r * (n + e - 1).choose e ≤
      hilbertFunction (familySpace q) (d + e) := by
  have h := prefix_euler_identity (e := e) hn q
  omega

theorem prefix_hilbert_of_injective (hn : 0 < n) (q : Fin r → Forms K n d)
    (hq : Function.Injective (prefixMultiplication q e)) :
    hilbertFunction (familySpace q) (d + e) =
      (n + (d + e) - 1).choose (d + e) - r * (n + e - 1).choose e := by
  have h := prefix_euler_identity (e := e) hn q
  rw [LinearMap.ker_eq_bot.mpr hq] at h
  simp only [finrank_bot, add_zero] at h
  omega

theorem prefix_hilbert_of_surjective (hn : 0 < n) (q : Fin r → Forms K n d)
    (hq : Function.Surjective (prefixMultiplication q e)) :
    hilbertFunction (familySpace q) (d + e) = 0 := by
  have h := prefix_hilbert_add_rank (e := e) hn q
  rw [LinearMap.range_eq_top.mpr hq, finrank_top, finrank_forms K n (d + e) hn] at h
  omega

/-- The coefficient-space map for a fixed relation tuple. Its kernel is the
incidence fiber over that tuple in Boij–Dannetun–Lundqvist §2. -/
def prefixIncidenceFiber (a : Fin r → Forms K n e) :
    (Fin r → Forms K n d) →ₗ[K] Forms K n (d + e) where
  toFun q := prefixMultiplication q e a
  map_add' q q' := by
    apply Subtype.ext
    simp [prefixMultiplication_val, add_mul, Finset.sum_add_distrib]
  map_smul' c q := by
    apply Subtype.ext
    simp [prefixMultiplication_val, Finset.smul_sum]

@[simp] theorem prefixIncidenceFiber_val (a : Fin r → Forms K n e)
    (q : Fin r → Forms K n d) :
    (prefixIncidenceFiber a q).val = ∑ i, (q i).val * (a i).val :=
  prefixMultiplication_val q a

/-- Exact dimension of the incidence fiber, expressed without truncated
subtraction: fiber dimension + target dimension = parameter dimension +
the Hilbert function of the coefficient ideal. -/
theorem prefix_incidence_fiber_dimension (hn : 0 < n) (a : Fin r → Forms K n e) :
    finrank K (LinearMap.ker (prefixIncidenceFiber (d := d) a)) +
      (n + (d + e) - 1).choose (d + e) =
        r * (n + d - 1).choose d + hilbertFunction (familySpace a) (d + e) := by
  have hker : LinearMap.ker (prefixIncidenceFiber (d := d) a) =
      LinearMap.ker (prefixMultiplication a d) := by
    ext q
    simp only [LinearMap.mem_ker]
    constructor <;> intro h
    · apply Subtype.ext
      have he := congrArg Subtype.val h
      simpa [prefixIncidenceFiber_val, prefixMultiplication_val, mul_comm] using he
    · apply Subtype.ext
      have he := congrArg Subtype.val h
      simpa [prefixIncidenceFiber_val, prefixMultiplication_val, mul_comm] using he
  rw [hker]
  have h := prefix_euler_identity (e := d) hn a
  have hc : e + d = d + e := Nat.add_comm _ _
  have hh : hilbertFunction (familySpace a) (e + d) =
      hilbertFunction (familySpace a) (d + e) := congrArg _ hc
  have hm : (n + (e + d) - 1).choose (e + d) =
      (n + (d + e) - 1).choose (d + e) := by rw [hc]
  omega

/-- The coefficient dependence is linear, so the existing determinant-open
rank argument applies uniformly in every degree. -/
def coefficientPrefixMultiplication (e : ℕ) : (CoefficientIndex n d r → K) →ₗ[K]
    ((Fin r → Forms K n e) →ₗ[K] Forms K n (d + e)) :=
  { toFun := fun a => prefixMultiplication (coefficientForms K n d r a) e
    map_add' := by
      intro a b
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      simp [prefixMultiplication_val, coefficientForms, add_smul, add_mul, Finset.sum_add_distrib]
    map_smul' := by
      intro c a
      apply LinearMap.ext
      intro f
      apply Subtype.ext
      simp [prefixMultiplication_val, coefficientForms, mul_smul, ← Finset.smul_sum] }

/-- A witness for the universal dimension lower bound supplies a nonempty
principal open with exactly that Hilbert function. -/
theorem prefix_lower_bound_principal_open (hn : 0 < n)
    (a₀ : CoefficientIndex n d r → K)
    (ha₀ : hilbertFunction (coefficientSpace K n d r a₀) (d + e) =
      (n + (d + e) - 1).choose (d + e) - r * (n + e - 1).choose e) :
    ∃ D : MvPolynomial (CoefficientIndex n d r) K,
      eval a₀ D ≠ 0 ∧ ∀ a, eval a D ≠ 0 →
        hilbertFunction (coefficientSpace K n d r a) (d + e) =
          (n + (d + e) - 1).choose (d + e) - r * (n + e - 1).choose e := by
  obtain ⟨D, hD, hprop⟩ := rank_principal_open
    (coefficientPrefixMultiplication (K := K) (n := n) (d := d) (r := r) e) a₀
  refine ⟨D, hD, ?_⟩
  intro a ha
  have h₀ := prefix_hilbert_add_rank (e := e) hn (coefficientForms K n d r a₀)
  have h₁ := prefix_hilbert_add_rank (e := e) hn (coefficientForms K n d r a)
  have h₂ := prefix_hilbert_lower_bound (e := e) hn (coefficientForms K n d r a)
  change hilbertFunction (coefficientSpace K n d r a₀) (d + e) + _ = _ at h₀
  change hilbertFunction (coefficientSpace K n d r a) (d + e) + _ = _ at h₁
  change _ ≤ hilbertFunction (coefficientSpace K n d r a) (d + e) at h₂
  have hr := hprop a ha
  change finrank K (prefixMultiplication (coefficientForms K n d r a₀) e).range ≤
    finrank K (prefixMultiplication (coefficientForms K n d r a) e).range at hr
  omega

/-- Degree zero multipliers recover the span of the original generators. -/
theorem prefix_zero_rank (q : Fin r → Forms K n d) :
    finrank K (prefixMultiplication q 0).range = finrank K (familySpace q) := by
  have h := range_ambient_prefixMultiplication (e := 0) q
  simp only [Forms, homogeneousSubmodule_zero, mul_one] at h
  rw [LinearMap.range_comp] at h
  have hh := congrArg (fun S : Submodule K (Poly K n) => finrank K S) h
  rw [Submodule.finrank_map_subtype_eq] at hh
  exact hh

/-- Independent degree-`d` generators remove exactly `r` dimensions in that degree. -/
theorem hilbertFunction_generating_degree (hn : 0 < n)
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    hilbertFunction (familySpace q) d = (n + d - 1).choose d - r := by
  have hspan : finrank K (familySpace q) = r := by
    have hli : LinearIndependent K (fun i => (q i).val) := hq.map' (Forms K n d).subtype
      (LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _))
    rw [familySpace, finrank_span_eq_card hli, Fintype.card_fin]
  have h := prefix_hilbert_add_rank (e := 0) hn q
  rw [prefix_zero_rank, hspan] at h
  simp only [Nat.add_zero] at h
  omega

theorem predictedHilbertFunction_generating_degree (hn : 0 < n) (hd : 0 < d) :
    predictedHilbertFunction n d r d = (n + d - 1).choose d - r := by
  by_cases hr : r < (n + d - 1).choose d
  · unfold predictedHilbertFunction
    rw [positiveTruncation_eq_of_positive]
    · rw [predictionCoefficient_before_endpoint n d r d hn le_rfl (by omega)]
      simp only [Nat.sub_self, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      omega
    · intro i hi
      by_cases hdi : i < d
      · rw [predictionCoefficient_below_degree n d r i hn hdi]
        exact_mod_cast monomial_count_pos hn i
      · have he : i = d := by omega
        subst i
        rw [predictionCoefficient_before_endpoint n d r d hn le_rfl (by omega)]
        simp only [Nat.sub_self, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
        omega
  · rw [predictedHilbertFunction_zero_of_many_generators hn hd (by omega) le_rfl]
    omega

/-- Exact generic Hilbert function in the generating degree over every field. -/
theorem genericHilbertAt_generating_degree (hn : 0 < n) (hd : 0 < d)
    (hr : r ≤ (n + d - 1).choose d) : GenericHilbertAt K n d r d := by
  obtain ⟨D, hD, hprop⟩ := coefficient_independence_principal_open (K := K) hn hr
  refine ⟨D, hD, ?_⟩
  intro a ha
  rw [predictedHilbertFunction_generating_degree hn hd]
  exact hilbertFunction_generating_degree hn (coefficientForms K n d r a) (hprop a ha)

end Froberg
