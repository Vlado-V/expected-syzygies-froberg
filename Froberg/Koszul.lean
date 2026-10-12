module

public import Froberg.Graded
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Data.Fintype.Prod

@[expose] public section

noncomputable section

namespace Froberg

open Module

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {r : ℕ}

abbrev GeneratorPair (r : ℕ) := {p : Fin r × Fin r // p.1 < p.2}

theorem card_generatorPair : Fintype.card (GeneratorPair r) = r.choose 2 := by
  simpa [GeneratorPair, Fintype.card_subtype] using
    (Fintype.card_product_filter_lt (α := Fin r))

/-- Independent vectors admit simultaneous coordinate functionals. -/
theorem exists_coordinate_functionals (q : Fin r → V) (hq : LinearIndependent K q) :
    ∃ dual : Fin r → V →ₗ[K] K, ∀ i j, dual i (q j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ := (Finsupp.linearCombination K q).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hq)
  refine ⟨fun i => (Finsupp.lapply i).comp g, ?_⟩
  intro i j
  have h := LinearMap.congr_fun hg (Finsupp.single j 1)
  have hj : g (q j) = Finsupp.single j 1 := by simpa using h
  simp [hj, Finsupp.single_apply, eq_comm]

/-- A constant incoming Koszul relation on a pair of generators. -/
def koszulVector (q : Fin r → V) (p : GeneratorPair r) : Fin r → V :=
  fun i => (if i = p.val.1 then q p.val.2 else 0) -
    (if i = p.val.2 then q p.val.1 else 0)

set_option maxRecDepth 2048 in
theorem koszulVector_coordinate (q : Fin r → V)
    (dual : Fin r → V →ₗ[K] K)
    (hdual : ∀ i j, dual i (q j) = if i = j then 1 else 0)
    (p t : GeneratorPair r) :
    dual p.val.2 (koszulVector q t p.val.1) = if p = t then 1 else 0 := by
  classical
  simp only [koszulVector, map_sub, apply_ite, map_zero, hdual]
  have hp := p.property
  have ht := t.property
  by_cases heq : p = t
  · subst t
    simp [ne_of_lt hp]
  · have hneq : ¬(p.val.1 = t.val.1 ∧ p.val.2 = t.val.2) := by
      intro h
      exact heq (Subtype.ext (Prod.ext h.1 h.2))
    simp only [heq, ite_false]
    split_ifs <;> simp_all
    all_goals omega

/-- The forced pairwise relations are independent whenever the generators are. -/
theorem koszulVector_linearIndependent (q : Fin r → V) (hq : LinearIndependent K q) :
    LinearIndependent K (koszulVector q) := by
  classical
  obtain ⟨dual, hdual⟩ := exists_coordinate_functionals q hq
  apply Fintype.linearIndependent_iff.mpr
  intro a ha p
  have h := congrArg (fun z : Fin r → V => dual p.val.2 (z p.val.1)) ha
  simpa only [Finset.sum_apply, map_sum, Pi.smul_apply, map_smul,
    koszulVector_coordinate q dual hdual, Pi.zero_apply, map_zero,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    Finset.sum_ite_eq, ite_true] using h

variable {n d : ℕ}

/-- Multiplication for an ordered family of degree-`d` forms. -/
def endpointMultiplication (q : Fin r → Forms K n d) :
    (Fin r → Forms K n d) →ₗ[K] Forms K n (2 * d) :=
  ∑ i, (mulForm (q i)).comp (LinearMap.proj i)

theorem endpointMultiplication_koszul (q : Fin r → Forms K n d) (p : GeneratorPair r) :
    endpointMultiplication q (koszulVector q p) = 0 := by
  classical
  apply Subtype.ext
  simp only [endpointMultiplication, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, Submodule.coe_sum]
  change (∑ i, (q i).val * (koszulVector q p i).val) = 0
  have hcoe (i j : Fin r) (a : Forms K n d) :
      ((if i = j then a else 0) : Forms K n d).val = if i = j then a.val else 0 := by
    split_ifs <;> rfl
  simp only [koszulVector, Submodule.coe_sub, hcoe,
    mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact sub_eq_zero.mpr (mul_comm (q p.val.1).val (q p.val.2).val)

theorem kernel_contains_koszul (q : Fin r → Forms K n d) :
    Submodule.span K (Set.range (koszulVector q)) ≤ LinearMap.ker (endpointMultiplication q) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, rfl⟩
  exact endpointMultiplication_koszul q p

/-- The kernel has at least one independent commutativity relation per generator pair. -/
theorem koszul_kernel_lower_bound (q : Fin r → Forms K n d)
    (hq : LinearIndependent K q) :
    r.choose 2 ≤ finrank K (LinearMap.ker (endpointMultiplication q)) := by
  have h := Submodule.finrank_mono (kernel_contains_koszul q)
  rw [finrank_span_eq_card (koszulVector_linearIndependent q hq), card_generatorPair] at h
  exact h

/-- Universal degree-`2*d` rank bound including the full Koszul correction. -/
theorem endpoint_rank_add_pairs_le (hn : 0 < n) (q : Fin r → Forms K n d)
    (hq : LinearIndependent K q) :
    finrank K (LinearMap.range (endpointMultiplication q)) + r.choose 2 ≤
      r * (n + d - 1).choose d := by
  have h := (endpointMultiplication q).finrank_range_add_finrank_ker
  have hk := koszul_kernel_lower_bound q hq
  have hdim : finrank K (Fin r → Forms K n d) = r * (n + d - 1).choose d := by
    simp [Module.finrank_pi_fintype, finrank_forms K n d hn]
  rw [hdim] at h
  exact (Nat.add_le_add_left hk _).trans_eq h

/-- The incoming degree-`2*d` Koszul map in the ordered pair basis. -/
def koszulBoundary (q : Fin r → V) :
    (GeneratorPair r →₀ K) →ₗ[K] (Fin r → V) :=
  Finsupp.linearCombination K (koszulVector q)

/-- Constant Koszul boundaries inject for every independent family. -/
theorem koszulBoundary_injective (q : Fin r → V) (hq : LinearIndependent K q) :
    Function.Injective (koszulBoundary (K := K) q) :=
  koszulVector_linearIndependent q hq

/-- Commutativity makes the actual polynomial multiplication and boundary a complex. -/
theorem endpointMultiplication_comp_koszulBoundary (q : Fin r → Forms K n d) :
    (endpointMultiplication q).comp (koszulBoundary q) = 0 := by
  apply LinearMap.range_le_ker_iff.mp
  simpa only [koszulBoundary, Finsupp.range_linearCombination] using kernel_contains_koszul q

/-- Multiplication in ambient polynomial coordinates. -/
theorem endpointMultiplication_val (q : Fin r → Forms K n d)
    (a : Fin r → Forms K n d) :
    (endpointMultiplication q a).val = ∑ i, (q i).val * (a i).val := by
  simp [endpointMultiplication, mulForm]

/-- The multiplication range in the polynomial ring is the product submodule. -/
theorem range_ambient_endpointMultiplication (q : Fin r → Forms K n d) :
    LinearMap.range ((Forms K n (2 * d)).subtype.comp (endpointMultiplication q)) =
      Submodule.span K (Set.range (fun i => (q i).val)) * Forms K n d := by
  apply le_antisymm
  · rintro p ⟨a, rfl⟩
    change (endpointMultiplication q a).val ∈ _
    rw [endpointMultiplication_val]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.mul_mem_mul (Submodule.subset_span ⟨i, rfl⟩) (a i).property
  · apply Submodule.mul_le.mpr
    intro f hf a ha
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
    refine ⟨fun i => c i • (⟨a, ha⟩ : Forms K n d), ?_⟩
    change (endpointMultiplication q (fun i => c i • (⟨a, ha⟩ : Forms K n d))).val = _
    simp [endpointMultiplication_val, Finset.sum_mul]

/-- The coordinate range agrees with the intrinsic endpoint product subspace. -/
theorem range_endpointMultiplication (q : Fin r → Forms K n d) :
    LinearMap.range (endpointMultiplication q) =
      endpointProducts K n d (Submodule.span K (Set.range (fun i => (q i).val))) := by
  have h := congrArg (fun P : Submodule K (Poly K n) =>
      P.comap (Forms K n (2 * d)).subtype) (range_ambient_endpointMultiplication q)
  rw [LinearMap.range_comp,
    Submodule.comap_map_eq_of_injective (Submodule.injective_subtype _)] at h
  exact h

/-- The endpoint quotient dimension is the codimension of the multiplication range. -/
theorem endpoint_quotient_add_rank (hn : 0 < n) (q : Fin r → Forms K n d) :
    finrank K (EndpointQuotient K n d
      (Submodule.span K (Set.range (fun i => (q i).val)))) +
      finrank K (LinearMap.range (endpointMultiplication q)) =
        (n + 2 * d - 1).choose (2 * d) := by
  rw [range_endpointMultiplication q]
  exact ((endpointProducts K n d
    (Submodule.span K (Set.range (fun i => (q i).val)))).finrank_quotient_add_finrank).trans
      (finrank_forms K n (2 * d) hn)

section GeneralKernelQuotient
variable {E T : Type*} [AddCommGroup E] [Module K E] [AddCommGroup T] [Module K T]

/-- Boundaries, viewed as a subspace of the cycle space. -/
def kernelBoundary (f : E →ₗ[K] T) (B : Submodule K E) : Submodule K f.ker :=
  B.comap f.ker.subtype

abbrev KernelModulo (f : E →ₗ[K] T) (B : Submodule K E) :=
  f.ker ⧸ kernelBoundary f B

theorem finrank_kernelModulo_add [FiniteDimensional K E]
    (f : E →ₗ[K] T) (B : Submodule K E) :
    finrank K (KernelModulo f B) + finrank K (kernelBoundary f B) =
      finrank K f.ker := by
  exact (kernelBoundary f B).finrank_quotient_add_finrank
end GeneralKernelQuotient

/-- The actual constant Koszul boundary subspace. -/
def koszulSpace (q : Fin r → Forms K n d) : Submodule K (Fin r → Forms K n d) :=
  Submodule.span K (Set.range (koszulVector q))

abbrev incomingInKernel (q : Fin r → Forms K n d) :=
  kernelBoundary (endpointMultiplication q) (koszulSpace q)

/-- First Koszul homology at the endpoint, in ordered generator coordinates. -/
abbrev EndpointHomology (q : Fin r → Forms K n d) :=
  KernelModulo (endpointMultiplication q) (koszulSpace q)

theorem finrank_incomingInKernel (q : Fin r → Forms K n d)
    (hq : LinearIndependent K q) : finrank K (incomingInKernel q) = r.choose 2 := by
  unfold incomingInKernel kernelBoundary koszulSpace
  rw [(Submodule.comapSubtypeEquivOfLe (kernel_contains_koszul q)).finrank_eq]
  exact (finrank_span_eq_card (koszulVector_linearIndependent q hq)).trans card_generatorPair

theorem homology_add_pairs (q : Fin r → Forms K n d)
    (hq : LinearIndependent K q) :
    finrank K (EndpointHomology q) + r.choose 2 =
      finrank K (LinearMap.ker (endpointMultiplication q)) := by
  have h := finrank_kernelModulo_add (endpointMultiplication q) (koszulSpace q)
  rwa [finrank_incomingInKernel q hq] at h

/-- Euler characteristic of the actual degree-`2*d` multiplication complex. -/
theorem endpoint_euler_identity (hn : 0 < n) (q : Fin r → Forms K n d)
    (hq : LinearIndependent K q) :
    (finrank K (EndpointQuotient K n d
      (Submodule.span K (Set.range (fun i => (q i).val)))) : ℤ) -
      (finrank K (EndpointHomology q) : ℤ) = euler n d r := by
  have hhom := homology_add_pairs q hq
  have hcoker := endpoint_quotient_add_rank hn q
  have hrank := (endpointMultiplication q).finrank_range_add_finrank_ker
  have hdim : finrank K (Fin r → Forms K n d) = r * (n + d - 1).choose d := by
    simp [Module.finrank_pi_fintype, finrank_forms K n d hn]
  rw [hdim] at hrank
  unfold euler
  zify at hhom hcoker hrank
  omega

/-- Every independent family has at least the predicted untruncated endpoint dimension. -/
theorem endpoint_quotient_lower_bound (hn : 0 < n) (q : Fin r → Forms K n d)
    (hq : LinearIndependent K q) :
    expectedEndpoint n d r ≤ finrank K (EndpointQuotient K n d
      (Submodule.span K (Set.range (fun i => (q i).val)))) := by
  have h := endpoint_euler_identity hn q hq
  unfold expectedEndpoint
  omega

/-- The expected endpoint dimension is attained exactly when homology or cokernel vanishes. -/
theorem expected_quotient_iff_homology_or_quotient_zero
    (hn : 0 < n) (q : Fin r → Forms K n d) (hq : LinearIndependent K q) :
    finrank K (EndpointQuotient K n d
      (Submodule.span K (Set.range (fun i => (q i).val)))) = expectedEndpoint n d r ↔
    finrank K (EndpointHomology q) = 0 ∨
      finrank K (EndpointQuotient K n d
        (Submodule.span K (Set.range (fun i => (q i).val)))) = 0 := by
  have h := endpoint_euler_identity hn q hq
  change _ = (euler n d r).toNat ↔ _
  omega

end Froberg
