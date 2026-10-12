module

public import ESCtoFroberg.GeneralPoints

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open MvPolynomial Module
variable {K : Type*} [Field K]

def idealDegreeSpace {n : ℕ} (I : Ideal (Poly K n)) (d : ℕ) :
    Submodule K (Poly K n) := Forms K n d ⊓ I.restrictScalars K

@[simp] theorem mem_idealDegreeSpace {n d : ℕ} (I : Ideal (Poly K n)) (f : Poly K n) :
    f ∈ idealDegreeSpace I d ↔ f.IsHomogeneous d ∧ f ∈ I := Iff.rfl

theorem pointDegreeSpace_eq_idealDegreeSpace {m p d : ℕ} (a : PointCoordinates K m p) :
    pointDegreeSpace K a d = idealDegreeSpace (pointIdeal K a) d := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.property, (homogeneous_mem_pointIdeal_iff a g).mpr hg⟩
  · intro hf
    exact ⟨⟨f, hf.1⟩, (homogeneous_mem_pointIdeal_iff a ⟨f, hf.1⟩).mp hf.2, rfl⟩

theorem idealDegreeSpace_mul_forms_le {n d e : ℕ} (I : Ideal (Poly K n)) :
    idealDegreeSpace I d * Forms K n e ≤ idealDegreeSpace I (d + e) := by
  apply Submodule.mul_le.mpr
  intro f hf g hg
  exact ⟨hf.1.mul hg, Ideal.mul_mem_right _ _ hf.2⟩

theorem forms_mul_ideal_le {n d : ℕ} (I : Ideal (Poly K n)) :
    Forms K n d * I.restrictScalars K ≤ I.restrictScalars K := by
  apply Submodule.mul_le.mpr
  intro f hf g hg
  exact Ideal.mul_mem_left _ _ hg

theorem pointEvaluation_surjective_add {m p d : ℕ} (a : PointCoordinates K m p)
    (hsurj : Function.Surjective (pointEvaluation K a d)) (e : ℕ) :
    Function.Surjective (pointEvaluation K a (d + e)) := by
  intro v
  obtain ⟨f, hf⟩ := hsurj v
  refine ⟨⟨f.val * X (Fin.last m) ^ e,
    f.property.mul (isHomogeneous_X_pow (Fin.last m) e)⟩, ?_⟩
  ext i
  simpa [pointEvaluation_apply, map_mul] using congrFun hf i

theorem pointEvaluation_surjective_of_le {m p d t : ℕ} (a : PointCoordinates K m p)
    (hsurj : Function.Surjective (pointEvaluation K a d)) (hdt : d ≤ t) :
    Function.Surjective (pointEvaluation K a t) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hdt
  exact pointEvaluation_surjective_add a hsurj e

/-- Coordinate multiplication from degree d to degree d+1. -/
def coordinateMultiplication (n d : ℕ) :
    (Fin n → Forms K n d) →ₗ[K] Forms K n (1 + d) where
  toFun b := ⟨∑ i, X i * (b i).val, by
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    exact (isHomogeneous_X K i).mul (b i).property⟩
  map_add' b c := by ext; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c b := by ext; simp [Finset.smul_sum]

theorem range_coordinateMultiplication (n d : ℕ) :
    LinearMap.range ((Forms K n (1 + d)).subtype.comp
      (coordinateMultiplication (K := K) n d)) = Forms K n 1 * Forms K n d := by
  apply le_antisymm
  · rintro f ⟨b, rfl⟩
    change (∑ i, X i * (b i).val) ∈ _
    exact Submodule.sum_mem _ (fun i hi =>
      Submodule.mul_mem_mul (isHomogeneous_X K i) (b i).property)
  · apply Submodule.mul_le.mpr
    intro f hf a ha
    change f ∈ MvPolynomial.homogeneousSubmodule (Fin n) K 1 at hf
    rw [homogeneousSubmodule_one_eq_span_X] at hf
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hf
    refine ⟨fun i => c i • (⟨a, ha⟩ : Forms K n d), ?_⟩
    change (∑ i, X i * (c i • a)) = (∑ i, c i • X i) * a
    simp [Finset.sum_mul]

theorem exists_coordinate_decomposition {n : ℕ} (d : ℕ) (f : Forms K n (d + 1)) :
    ∃ b : Fin n → Forms K n d, f.val = ∑ i, X i * (b i).val := by
  have hmem : f.val ∈ LinearMap.range ((Forms K n (1 + d)).subtype.comp
      (coordinateMultiplication (K := K) n d)) := by
    rw [range_coordinateMultiplication, Froberg.forms_mul_forms]
    simp [Nat.add_comm]
  obtain ⟨b, hb⟩ := hmem
  exact ⟨b, hb.symm⟩

/-- Interpolation one degree below the equations forces the coordinate recurrence. -/
theorem pointDegreeSpace_succ_eq {m p t : ℕ} (a : PointCoordinates K m p)
    (hsurj : Function.Surjective (pointEvaluation K a t)) :
    pointDegreeSpace K a (t + 2) =
      Forms K (m + 1) 1 * pointDegreeSpace K a (t + 1) := by
  classical
  apply le_antisymm
  · intro f hf
    obtain ⟨hfhom, hfeval⟩ := (mem_pointDegreeSpace a f).mp hf
    obtain ⟨b, hb⟩ := exists_coordinate_decomposition (t + 1) ⟨f, hfhom⟩
    change f = ∑ i, X i * (b i).val at hb
    choose g hg using fun j : Fin m => hsurj (pointEvaluation K a (t + 1) (b j.castSucc))
    let c : Fin m → Poly K (m + 1) := fun j =>
      (b j.castSucc).val - X (Fin.last m) * (g j).val
    let z : Poly K (m + 1) := (b (Fin.last m)).val + ∑ j : Fin m, X j.castSucc * (g j).val
    have he (j : Fin m) (i : Fin p) : eval (chartPoint K a i) (g j).val =
        eval (chartPoint K a i) (b j.castSucc).val := congrFun (hg j) i
    have hc (j : Fin m) : c j ∈ pointDegreeSpace K a (t + 1) := by
      apply (mem_pointDegreeSpace a (c j)).mpr
      constructor
      · exact (b j.castSucc).property.sub (by simpa [Nat.add_comm] using
          (isHomogeneous_X K (Fin.last m)).mul (g j).property)
      · intro i
        simp [c, he]
    have hz : z ∈ pointDegreeSpace K a (t + 1) := by
      apply (mem_pointDegreeSpace a z).mpr
      constructor
      · apply (b (Fin.last m)).property.add
        apply MvPolynomial.IsHomogeneous.sum
        intro j hj
        simpa [Nat.add_comm] using (isHomogeneous_X K j.castSucc).mul (g j).property
      · intro i
        have h := hfeval i
        rw [hb, Fin.sum_univ_castSucc] at h
        simpa [z, he, add_comm] using h
    have hid : f = (∑ j : Fin m, X j.castSucc * c j) + X (Fin.last m) * z := by
      rw [hb, Fin.sum_univ_castSucc]
      simp only [c, z, mul_sub, Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
      have hsum : (∑ j : Fin m, X j.castSucc * (X (Fin.last m) * (g j).val)) =
          ∑ j : Fin m, X (Fin.last m) * (X j.castSucc * (g j).val) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hsum]
      ring
    rw [hid]
    exact Submodule.add_mem _
      (Submodule.sum_mem _ (fun j hj => Submodule.mul_mem_mul
        (isHomogeneous_X K j.castSucc) (hc j)))
      (Submodule.mul_mem_mul (isHomogeneous_X K (Fin.last m)) hz)
  · rw [pointDegreeSpace_eq_idealDegreeSpace, pointDegreeSpace_eq_idealDegreeSpace, mul_comm]
    simpa [Nat.add_assoc] using
      idealDegreeSpace_mul_forms_le (d := t + 1) (e := 1) (pointIdeal K a)

theorem pointDegreeSpace_recurrence {m p q : ℕ} (a : PointCoordinates K m p)
    (hq : 1 ≤ q) (hsurj : Function.Surjective (pointEvaluation K a (q - 1)))
    (d : ℕ) (hqd : q ≤ d) :
    pointDegreeSpace K a (d + 1) = Forms K (m + 1) 1 * pointDegreeSpace K a d := by
  have hd : 1 ≤ d := hq.trans hqd
  have hs := pointEvaluation_surjective_of_le a hsurj (show q - 1 ≤ d - 1 by omega)
  have hh := pointDegreeSpace_succ_eq a hs
  simpa [show d - 1 + 1 = d by omega, show d - 1 + 2 = d + 1 by omega] using hh

/-- The chopped ideal agrees with the point ideal in every degree at least q. -/
theorem chopped_degree_eq_point_degree {m p q : ℕ} (a : PointCoordinates K m p)
    (hq : 1 ≤ q) (hsurj : Function.Surjective (pointEvaluation K a (q - 1))) :
    ∀ d, q ≤ d → pointDegreeSpace K a d = idealDegreeSpace (choppedIdeal K a q) d := by
  have hcontain : ∀ d, q ≤ d → pointDegreeSpace K a d ≤
      (choppedIdeal K a q).restrictScalars K := by
    intro d hd
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
    induction e with
    | zero =>
      intro f hf
      exact Ideal.subset_span (by simpa using hf)
    | succ e ih =>
      rw [show q + (e + 1) = (q + e) + 1 by omega,
        pointDegreeSpace_recurrence a hq hsurj (q + e) (by omega)]
      exact (mul_le_mul_right (ih (by omega)) _).trans (forms_mul_ideal_le (choppedIdeal K a q))
  intro d hd
  apply le_antisymm
  · exact le_inf (pointDegreeSpace_homogeneous a) (hcontain d hd)
  · rw [pointDegreeSpace_eq_idealDegreeSpace]
    exact inf_le_inf_left _ (choppedIdeal_le_pointIdeal a)

theorem choppedHilbertFunction_eq_point_above {m p q t : ℕ} (a : PointCoordinates K m p)
    (hq : 1 ≤ q) (hsurj : Function.Surjective (pointEvaluation K a (q - 1)))
    (hqt : q ≤ t) : choppedHilbertFunction K a q t = pointHilbertFunction K a t := by
  have hker : LinearMap.ker (Froberg.formToRingQuotient t (pointDegreeSpace K a q)) =
      pointDegreePiece K a t := by
    ext f
    change Ideal.Quotient.mk (choppedIdeal K a q) f.val = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have he := chopped_degree_eq_point_degree a hq hsurj t hqt
    constructor
    · intro hf
      have : f.val ∈ pointDegreeSpace K a t := he.symm ▸ ⟨f.property, hf⟩
      rcases this with ⟨g, hg, hgf⟩
      have : g = f := Subtype.ext hgf
      simpa [this] using hg
    · intro hf
      have : f.val ∈ pointDegreeSpace K a t := ⟨f, hf, rfl⟩
      exact (he ▸ this).2
  change finrank K (LinearMap.range _) = _
  rw [← (Froberg.formToRingQuotient t (pointDegreeSpace K a q)).quotKerEquivRange.finrank_eq,
    hker]
  rfl

theorem choppedHilbertFunction_below_degree {m p q t : ℕ} (a : PointCoordinates K m p)
    (ht : t < q) : choppedHilbertFunction K a q t = (m + t).choose t := by
  have h := Froberg.hilbertFunction_below_degree (n := m + 1) (by omega) t ht
    (pointDegreeSpace K a q) (pointDegreeSpace_homogeneous a)
  simpa only [choppedHilbertFunction, show m + 1 + t - 1 = m + t by omega] using h

/-- All equations in degrees at most q, as a subset of the actual polynomial ring. -/
def pointLowDegreeGenerators {m p : ℕ} (a : PointCoordinates K m p) (q : ℕ) :
    Set (Poly K (m+1)) := {f | ∃ d, d ≤ q ∧ f ∈ pointDegreeSpace K a d}

/-- Interpolation in degree q−1 proves generation of the full point ideal in degrees ≤q. -/
theorem pointIdeal_generated_in_low_degrees {m p q : ℕ} (a : PointCoordinates K m p)
    (hq : 1 ≤ q) (hsurj : Function.Surjective (pointEvaluation K a (q-1))) :
    pointIdeal K a = Ideal.span (pointLowDegreeGenerators a q) := by
  classical
  have hchop : choppedIdeal K a q ≤ Ideal.span (pointLowDegreeGenerators a q) := by
    apply Ideal.span_mono
    intro f hf
    exact ⟨q, le_rfl, hf⟩
  apply le_antisymm
  · intro f hf
    rw [← MvPolynomial.sum_homogeneousComponent f]
    apply Ideal.sum_mem
    intro d hd
    have hdI := homogeneousComponent_mem_of_mem (pointIdeal_homogeneous a) hf d
    have hdspace : homogeneousComponent d f ∈ pointDegreeSpace K a d := by
      rw [pointDegreeSpace_eq_idealDegreeSpace]
      exact ⟨homogeneousComponent_isHomogeneous d f, hdI⟩
    by_cases hdq : d ≤ q
    · exact Ideal.subset_span ⟨d, hdq, hdspace⟩
    · have he := chopped_degree_eq_point_degree a hq hsurj d (by omega)
      exact hchop (he ▸ hdspace).2
  · apply Ideal.span_le.mpr
    rintro f ⟨d, hd, hf⟩
    rw [pointDegreeSpace_eq_idealDegreeSpace] at hf
    exact hf.2

/-- The interpolation and generation lemma on an actual nonempty configuration open. -/
theorem generic_interpolation_generation [CharZero K] (m p q : ℕ)
    (hm : 1 ≤ m) (hq : 1 ≤ q) (hp : p ≤ (m + (q-1)).choose (q-1)) :
    ∃ D : MvPolynomial (Fin p × Fin m) K,
      (∃ a : PointCoordinates K m p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → DistinctPoints K a ∧
        (∀ t, pointHilbertFunction K a t = min ((m+t).choose t) p) ∧
        pointIdeal K a = Ideal.span (pointLowDegreeGenerators a q) ∧
        ∀ t, q ≤ t → choppedHilbertFunction K a q t = p := by
  obtain ⟨D,hD,hgood⟩ := generic_pointHilbertFunction (K := K) m p hm
  refine ⟨D,hD,?_⟩
  intro a ha
  obtain ⟨hdist,hh⟩ := hgood a ha
  have heval : pointHilbertFunction K a (q-1) = p := by
    rw [hh, min_eq_right hp]
  have hsurj := pointEvaluation_surjective_of_hilbert_eq a heval
  refine ⟨hdist,hh,pointIdeal_generated_in_low_degrees a hq hsurj,?_⟩
  intro t ht
  rw [choppedHilbertFunction_eq_point_above a hq hsurj ht]
  exact pointHilbertFunction_constant_above a (by omega) heval

end ESCtoFroberg
