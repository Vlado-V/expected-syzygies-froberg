module

public import Froberg.GenericDimensions
public import Froberg.CoordinateFoundation.VariableProjection

@[expose] public section

/-! The linear-degree endpoint, by an actual polynomial change of coordinates.
The coordinate calculation adapts the earlier cubic calculation to quadratics. -/
noncomputable section
namespace Froberg.LinearEndpoint
open MvPolynomial Module Froberg.CoordinateFoundation.LinearCoordinates Froberg.CoordinateFoundation.VariableProjection
variable {K σ ι τ : Type*} [Field K]

/-- The quadratic products of an ambient subspace of linear polynomials. -/
def products (D : Submodule K (MvPolynomial σ K)) : Submodule K (H K σ 2) :=
  (D * H K σ 1).comap (H K σ 2).subtype

theorem component_two_mul_linear (f p : MvPolynomial σ K) (hf : f.IsHomogeneous 1) :
    homogeneousComponent 2 (f * p) = f * homogeneousComponent 1 p := by
  induction p using MvPolynomial.induction_on' with
  | monomial e a =>
      have he : (monomial e a : MvPolynomial σ K).IsHomogeneous e.degree :=
        isHomogeneous_monomial a rfl
      rw [homogeneousComponent_of_mem (hf.mul he), homogeneousComponent_of_mem he]
      by_cases h : e.degree = 1
      · simp [h]
      · have h3 : ¬2 = 1 + e.degree := by omega
        simp [Ne.symm h, h3]
  | add p q hp hq => simp only [mul_add, map_add, hp, hq]

theorem quadratic_mem_ideal_iff (D : Submodule K (MvPolynomial σ K)) (hD : D ≤ H K σ 1)
    (p : H K σ 2) : p.val ∈ Ideal.span (D : Set (MvPolynomial σ K)) ↔
      p ∈ products D := by
  constructor
  · intro hp
    have hall : ∀ a : MvPolynomial σ K,
        homogeneousComponent 2 (a * p.val) ∈ D * H K σ 1 := by
      generalize hval : p.val = f at hp ⊢
      clear hval
      induction hp using Submodule.span_induction with
      | mem f hf =>
          intro a
          rw [mul_comm a f, component_two_mul_linear f a (hD hf)]
          exact Submodule.mul_mem_mul hf (homogeneousComponent_mem 1 a)
      | zero => intro a; simp
      | add f g hf hg ihf ihg =>
          intro a
          rw [mul_add, map_add]
          exact (D * H K σ 1).add_mem (ihf a) (ihg a)
      | smul b f hf ih =>
          intro a
          change homogeneousComponent 2 (a * (b * f)) ∈ D * H K σ 1
          rw [← mul_assoc]
          exact ih (a * b)
    have hz := hall 1
    change p.val ∈ D * H K σ 1
    simpa only [one_mul, homogeneousComponent_eq_self p.property] using hz
  · intro hp
    change p.val ∈ D * H K σ 1 at hp
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro f hf a ha
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span hf)
    · intro f g hf hg
      exact Ideal.add_mem _ hf hg

/-- The coordinate projection on the actual quadratic component. -/
def dropQuadratic : H K (ι ⊕ τ) 2 →ₗ[K] H K τ 2 :=
  ((dropLeft (K := K)).toLinearMap.comp (H K (ι ⊕ τ) 2).subtype).codRestrict _
    (fun p => dropLeft_homogeneous p.val p.property)

theorem dropQuadratic_surjective : Function.Surjective (dropQuadratic (K := K) (ι := ι) (τ := τ)) := by
  intro p
  refine ⟨⟨rename Sum.inr p.val, p.property.rename_isHomogeneous⟩, ?_⟩
  apply Subtype.ext
  exact dropLeft_rename p.val

theorem ker_dropQuadratic : LinearMap.ker (dropQuadratic (K := K) (ι := ι) (τ := τ)) =
    products (leftSpace K ι τ) := by
  ext p
  change dropQuadratic p = 0 ↔ p ∈ products (leftSpace K ι τ)
  rw [← Subtype.val_inj]
  change dropLeft p.val = 0 ↔ p ∈ products (leftSpace K ι τ)
  rw [dropLeft_zero_iff_ideal, quadratic_mem_ideal_iff _ leftSpace_homogeneous]

/-- Exact dimension of the coordinate quadratic product space. -/
theorem finrank_coordinate_products [Fintype ι] [Fintype τ] :
    finrank K (products (leftSpace K ι τ)) =
      (Fintype.card ι + Fintype.card τ + 1).choose 2 - (Fintype.card τ + 1).choose 2 := by
  have h := (dropQuadratic (K := K) (ι := ι) (τ := τ)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr dropQuadratic_surjective, finrank_top,
    ker_dropQuadratic, finrank_homogeneous, finrank_homogeneous] at h
  simp only [Fintype.card_sum] at h
  have h₁ : Fintype.card τ + 2 - 1 = Fintype.card τ + 1 := by omega
  have h₂ : Fintype.card ι + Fintype.card τ + 2 - 1 =
      Fintype.card ι + Fintype.card τ + 1 := by omega
  rw [h₁, h₂] at h
  omega
/-- Quadratics obtained by multiplying a member of `D` by an arbitrary linear form. -/
def quadraticProducts (D : Submodule K (H K σ 1)) : Submodule K (H K σ 2) :=
  products (D.map (H K σ 1).subtype)

private theorem finrank_products_ambient (D : Submodule K (MvPolynomial σ K))
    (hD : D ≤ H K σ 1) : finrank K (products D) = finrank K (D * H K σ 1) := by
  have he : (products D).map (H K σ 2).subtype = D * H K σ 1 := by
    apply Submodule.map_comap_eq_self
    rw [Submodule.range_subtype]
    exact (mul_le_mul_left hD _).trans (homogeneousSubmodule_mul 1 1)
  rw [← he, Submodule.finrank_map_subtype_eq]

private theorem finrank_products_change_basis (b : Basis ι K (H K σ 1))
    (D : Submodule K (MvPolynomial ι K)) (hD : D ≤ H K ι 1) :
    finrank K (products (D.map (polynomialEquiv b).toLinearMap)) =
      finrank K (products D) := by
  have hmap : D.map (polynomialEquiv b).toLinearMap ≤ H K σ 1 := by
    rw [← map_homogeneous b 1]
    exact Submodule.map_mono hD
  rw [finrank_products_ambient _ hmap, finrank_products_ambient _ hD]
  have hmul : (D * H K ι 1).map (polynomialEquiv b).toLinearMap =
      D.map (polynomialEquiv b).toLinearMap * H K σ 1 := by
    calc
      _ = D.map (polynomialEquiv b).toLinearMap *
          (H K ι 1).map (polynomialEquiv b).toLinearMap :=
        Submodule.map_mul D (H K ι 1) (polynomialEquiv b).toAlgHom
      _ = _ := by rw [map_homogeneous]
  rw [← hmul]
  exact (polynomialEquiv b).toLinearEquiv.finrank_map_eq _

private theorem span_basis_values {V J : Type*} [AddCommGroup V] [Module K V]
    (D : Submodule K V) (b : Basis J K D) :
    Submodule.span K (Set.range (fun i => (b i).val)) = D := by
  change Submodule.span K (Set.range (D.subtype ∘ b)) = D
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_top, D.range_subtype]

private def submoduleBasis {V : Type*} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (D : Submodule K V) : Basis (Fin (finrank K D)) K D :=
  Module.finBasis K D

/-- The exact quadratic image dimension, for every linear subspace and every field. -/
theorem finrank_quadraticProducts (m : ℕ) (D : Submodule K (Forms K m 1)) :
    finrank K (quadraticProducts D) =
      (m + 1).choose 2 - (m - finrank K D + 1).choose 2 := by
  classical
  obtain ⟨E, hE⟩ := D.exists_isCompl
  let bD := submoduleBasis D
  let bE := submoduleBasis E
  let b : Basis (Fin (finrank K D) ⊕ Fin (finrank K E)) K (Forms K m 1) :=
    (bD.prod bE).map (Submodule.prodEquivOfIsCompl D E hE)
  have hb (i : Fin (finrank K D)) : (b (Sum.inl i)).val = (bD i).val.val := by
    simp [b, Basis.prod_apply, Submodule.coe_prodEquivOfIsCompl']
  have hmap : (leftSpace K (Fin (finrank K D)) (Fin (finrank K E))).map
      (polynomialEquiv b).toLinearMap = D.map (Forms K m 1).subtype := by
    rw [leftSpace, Submodule.map_span, ← Set.range_comp]
    have he : ((polynomialEquiv b).toLinearMap ∘
        (fun i : Fin (finrank K D) => (X (Sum.inl i) :
          MvPolynomial (Fin (finrank K D) ⊕ Fin (finrank K E)) K))) =
        fun i => (bD i).val.val := by
      funext i
      exact (polynomialEquiv_X b (Sum.inl i)).trans (hb i)
    rw [he]
    have hv := congrArg (fun S => S.map (Forms K m 1).subtype) (span_basis_values D bD)
    simpa only [Submodule.map_span, ← Set.range_comp, Function.comp_def,
      Submodule.subtype_apply] using hv
  have hdim : finrank K D + finrank K E = m := by
    have h := Submodule.finrank_add_eq_of_isCompl hE
    have hm : finrank K (Forms K m 1) = m := by
      rw [Module.finrank_eq_card_basis (formsBasis K m 1), Sym.card_sym_eq_choose]
      simp
    simpa only [hm] using h
  have hr := finrank_products_change_basis b
    (leftSpace K (Fin (finrank K D)) (Fin (finrank K E))) leftSpace_homogeneous
  rw [hmap, finrank_coordinate_products] at hr
  simp only [Fintype.card_fin] at hr
  rw [hdim, show finrank K E = m - finrank K D by omega] at hr
  exact hr


end Froberg.LinearEndpoint

namespace Froberg
open Module
variable {K : Type*} [Field K] {n r : ℕ}

theorem euler_linear (hr : r ≤ n) :
    euler n 1 r = ((n - r + 1).choose 2 : ℤ) := by
  have hcalc : (((n + 1).choose 2 : ℕ) : ℝ) - (r : ℝ) * n + r.choose 2 =
      ((n - r + 1).choose 2 : ℝ) := by
    rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
    push_cast
    rw [Nat.cast_sub hr]
    ring
  have he : (euler n 1 r : ℝ) = ((n - r + 1).choose 2 : ℝ) := by
    simpa only [euler, Nat.mul_one, show n + 2 - 1 = n + 1 by omega,
      show n + 1 - 1 = n by omega, Nat.choose_one_right,
      Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_natCast] using hcalc
  exact_mod_cast he

/-- Every independent tuple of linear forms has the predicted degree-two quotient. -/
theorem endpoint_quotient_linear (hn : 0 < n) (q : Fin r → Forms K n 1)
    (hq : LinearIndependent K q) :
    finrank K (EndpointQuotient K n 1
      (Submodule.span K (Set.range (fun i => (q i).val)))) = expectedEndpoint n 1 r := by
  let D : Submodule K (Forms K n 1) := Submodule.span K (Set.range q)
  have hdim : finrank K D = r := by simpa [D] using finrank_span_eq_card hq
  have hr : r ≤ n := by
    have hh := Submodule.finrank_le D
    simpa only [hdim, finrank_forms K n 1 hn, Nat.add_sub_cancel,
      Nat.choose_one_right] using hh
  have hspace : D.map (Forms K n 1).subtype =
      Submodule.span K (Set.range (fun i => (q i).val)) := by
    dsimp only [D]
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hp := LinearEndpoint.finrank_quadraticProducts n D
  have hprod : LinearEndpoint.quadraticProducts D = endpointProducts K n 1
      (Submodule.span K (Set.range (fun i => (q i).val))) := by
    unfold LinearEndpoint.quadraticProducts LinearEndpoint.products endpointProducts
    rw [hspace]
  rw [hprod, hdim] at hp
  have hc := (endpointProducts K n 1
    (Submodule.span K (Set.range (fun i => (q i).val)))).finrank_quotient_add_finrank
  rw [hp, finrank_forms K n (2 * 1) hn] at hc
  have hle : (n - r + 1).choose 2 ≤ (n + 1).choose 2 :=
    Nat.choose_le_choose 2 (by omega)
  have he : expectedEndpoint n 1 r = (n - r + 1).choose 2 := by
    simp [expectedEndpoint, euler_linear hr]
  rw [he]
  change finrank K ((Forms K n (2 * 1)) ⧸ endpointProducts K n 1
    (Submodule.span K (Set.range (fun i => (q i).val)))) = _
  have hn2 : n + 2 * 1 - 1 = n + 1 := by omega
  rw [hn2] at hc
  simp only [Nat.mul_one] at hc
  omega

/-- The degree-one endpoint base, in every positive number of variables. -/
theorem genericEndpoint_linear (hn : 0 < n) (hr : r ≤ n) : GenericEndpoint K n 1 r := by
  have hm : r ≤ finrank K (Forms K n 1) := by
    simpa only [finrank_forms K n 1 hn, Nat.add_sub_cancel, Nat.choose_one_right] using hr
  obtain ⟨q, hq⟩ := exists_linearIndependent_of_le_finrank hm
  have ha : coefficientForms K n 1 r (coefficientCoordinates q) = q :=
    coefficientCoordinates.symm_apply_apply q
  apply genericEndpoint_of_coefficient_witness hn (coefficientCoordinates q)
  · rwa [ha]
  · unfold coefficientSpace
    rw [ha]
    exact endpoint_quotient_linear hn q hq

end Froberg
