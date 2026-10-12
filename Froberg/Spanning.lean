module

public import Froberg.Statement

@[expose] public section

/-! Generic spanning and all generator counts at or above the homogeneous dimension. -/
noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type*} [Field K] {n d r : ℕ}

/-- When the number of forms is at least the dimension, a determinant open
consists of tuples spanning the whole homogeneous component. -/
theorem coefficient_spanning_principal_open (hn : 0 < n)
    (hr : (n + d - 1).choose d ≤ r) :
    ∃ D : MvPolynomial (CoefficientIndex n d r) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
        Forms K n d ≤ coefficientSpace K n d r a := by
  classical
  let m := finrank K (Forms K n d)
  have hm : m ≤ r := by simpa only [m, finrank_forms K n d hn] using hr
  let b := Module.finBasis K (Forms K n d)
  let q : Fin r → Forms K n d := fun j => if hj : j.val < m then b ⟨j.val, hj⟩ else 0
  let a₀ : CoefficientIndex n d r → K := coefficientCoordinates q
  have ha₀ : coefficientForms K n d r a₀ = q := coefficientCoordinates.symm_apply_apply q
  let family : Fin m → (CoefficientIndex n d r → K) →ₗ[K] Forms K n d := fun i =>
    (formsBasis K n d).equivFun.symm.toLinearMap.comp
      (LinearMap.funLeft K K (fun v => (Fin.castLE hm i, v)))
  have hfamily (a : CoefficientIndex n d r → K) (i : Fin m) :
      family i a = coefficientForms K n d r a (Fin.castLE hm i) := rfl
  have hi : LinearIndependent K (fun i => family i a₀) := by
    have heq : (fun i => family i a₀) = b := by
      funext i
      rw [hfamily, ha₀]
      simp [q, i.isLt]
    rw [heq]
    exact b.linearIndependent
  obtain ⟨D, hD, hprop⟩ := independent_principal_open family a₀ hi
  refine ⟨D, ⟨a₀, hD⟩, fun a ha p hp => ?_⟩
  have hspan : Submodule.span K (Set.range (fun i => family i a)) = ⊤ :=
    (hprop a ha).span_eq_top_of_card_eq_finrank' (by simp [m])
  have hle : Submodule.span K (Set.range (fun i => family i a)) ≤
      (coefficientSpace K n d r a).comap (Forms K n d).subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Fin.castLE hm i, rfl⟩
  rw [hspan] at hle
  exact hle (show (⟨p, hp⟩ : Forms K n d) ∈ (⊤ : Submodule K (Forms K n d)) from trivial)

/-- Every generator count at or above `dim S_d` satisfies all degrees of
Fröberg's prediction on one common nonempty principal open. -/
theorem genericHilbertThrough_of_many_generators (hn : 0 < n) (hd : 0 < d)
    (hr : (n + d - 1).choose d ≤ r) (bound : ℕ) :
    GenericHilbertThrough K n d r bound := by
  obtain ⟨D, hD, hprop⟩ := coefficient_spanning_principal_open (K := K) hn hr
  exact ⟨D, hD, fun a ha j _ => hilbertFunction_eq_prediction_of_spanning
    hn hd hr a (hprop a ha) j⟩

end Froberg
