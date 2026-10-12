module

public import Froberg.Graded
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

/-! The smaller real root and the sign change of the endpoint Euler polynomial. -/

namespace Froberg

noncomputable def criticalRoot (D M : ℕ) : ℝ :=
  (D : ℝ) + 1 / 2 - Real.sqrt (((D : ℝ) + 1 / 2) ^ 2 - 2 * M)

noncomputable def eulerPolynomial (D M : ℕ) (r : ℝ) : ℝ :=
  (M : ℝ) - r * D + r * (r - 1) / 2

private theorem root_discriminant_bounds {D M : ℕ}
    (hM : 0 < M) (hbound : M ≤ D * (D + 1) / 2) :
    0 ≤ ((D : ℝ) + 1 / 2) ^ 2 - 2 * M ∧
    1 / 2 ≤ Real.sqrt (((D : ℝ) + 1 / 2) ^ 2 - 2 * M) ∧
    Real.sqrt (((D : ℝ) + 1 / 2) ^ 2 - 2 * M) < (D : ℝ) + 1 / 2 := by
  have hnat : 2 * M ≤ D * (D + 1) := by omega
  have hreal : 2 * (M : ℝ) ≤ (D : ℝ) * (D + 1) := by exact_mod_cast hnat
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hdisc : 0 ≤ ((D : ℝ) + 1 / 2) ^ 2 - 2 * M := by nlinarith
  have hs := Real.sq_sqrt hdisc
  have hs0 := Real.sqrt_nonneg (((D : ℝ) + 1 / 2) ^ 2 - 2 * M)
  have hD0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  exact ⟨hdisc, by nlinarith, by nlinarith⟩

/-- The critical count is positive and does not exceed the number of
available degree-`d` monomials. -/
theorem criticalRoot_bounds {D M : ℕ} (hM : 0 < M)
    (hbound : M ≤ D * (D + 1) / 2) :
    0 < criticalRoot D M ∧ criticalRoot D M ≤ D := by
  obtain ⟨_, hlo, hhi⟩ := root_discriminant_bounds hM hbound
  dsimp [criticalRoot]
  constructor <;> linarith

/-- The explicit radical is a root of the Euler polynomial. -/
theorem eulerPolynomial_criticalRoot {D M : ℕ} (hM : 0 < M)
    (hbound : M ≤ D * (D + 1) / 2) :
    eulerPolynomial D M (criticalRoot D M) = 0 := by
  have hdisc := (root_discriminant_bounds hM hbound).1
  have hs := Real.sq_sqrt hdisc
  dsimp [criticalRoot, eulerPolynomial]
  nlinarith

/-- An exact factorization centered on the critical root. -/
theorem eulerPolynomial_factor {D M : ℕ} (hM : 0 < M)
    (hbound : M ≤ D * (D + 1) / 2) (r : ℝ) :
    2 * eulerPolynomial D M r =
      (criticalRoot D M - r) * (2 * D + 1 - r - criticalRoot D M) := by
  have hz := eulerPolynomial_criticalRoot hM hbound
  dsimp [eulerPolynomial] at hz ⊢
  nlinarith

private theorem root_other_factor_pos {D M : ℕ} (hM : 0 < M)
    (hbound : M ≤ D * (D + 1) / 2) {r : ℝ} (hr : r ≤ D) :
    0 < 2 * (D : ℝ) + 1 - r - criticalRoot D M := by
  have hk := (criticalRoot_bounds hM hbound).2
  linarith

/-- Below the largest admissible count, the Euler polynomial is nonnegative
exactly on the left of its smaller root. -/
theorem eulerPolynomial_nonneg_iff {D M : ℕ} (hM : 0 < M)
    (hbound : M ≤ D * (D + 1) / 2) {r : ℝ} (hr : r ≤ D) :
    0 ≤ eulerPolynomial D M r ↔ r ≤ criticalRoot D M := by
  have hf := eulerPolynomial_factor hM hbound r
  have hp := root_other_factor_pos hM hbound hr
  have hm : 0 ≤ (criticalRoot D M - r) *
      (2 * D + 1 - r - criticalRoot D M) ↔ 0 ≤ criticalRoot D M - r :=
    mul_nonneg_iff_of_pos_right hp
  constructor
  · intro h
    have hmul : 0 ≤ (criticalRoot D M - r) *
        (2 * D + 1 - r - criticalRoot D M) := by linarith
    have := hm.mp hmul
    linarith
  · intro h
    have hmul := hm.mpr (show 0 ≤ criticalRoot D M - r by linarith)
    linarith

/-- The complementary nonpositive sign occurs exactly on the right. -/
theorem eulerPolynomial_nonpos_iff {D M : ℕ} (hM : 0 < M)
    (hbound : M ≤ D * (D + 1) / 2) {r : ℝ} (hr : r ≤ D) :
    eulerPolynomial D M r ≤ 0 ↔ criticalRoot D M ≤ r := by
  have hf := eulerPolynomial_factor hM hbound r
  have hp := root_other_factor_pos hM hbound hr
  have hm : (criticalRoot D M - r) *
      (2 * D + 1 - r - criticalRoot D M) ≤ 0 ↔ criticalRoot D M - r ≤ 0 := by
    simpa using (mul_le_mul_iff_of_pos_right hp :
      (criticalRoot D M - r) * (2 * D + 1 - r - criticalRoot D M) ≤
        0 * (2 * D + 1 - r - criticalRoot D M) ↔ criticalRoot D M - r ≤ 0)
  constructor
  · intro h
    have hmul : (criticalRoot D M - r) *
        (2 * D + 1 - r - criticalRoot D M) ≤ 0 := by linarith
    have := hm.mp hmul
    linarith
  · intro h
    have hmul := hm.mpr (show criticalRoot D M - r ≤ 0 by linarith)
    linarith

/-- Integer Euler characteristics agree with the real Euler polynomial. -/
theorem euler_cast_eq_polynomial (n d r : ℕ) :
    (euler n d r : ℝ) =
      eulerPolynomial ((n + d - 1).choose d)
        ((n + 2 * d - 1).choose (2 * d)) r := by
  simp [euler, eulerPolynomial, Nat.cast_choose_two]

/-- The actual integer endpoint Euler characteristic changes sign at the
explicit critical count. -/
theorem euler_nonneg_iff_criticalRoot (n d r : ℕ)
    (hM : 0 < (n + 2 * d - 1).choose (2 * d))
    (hbound : (n + 2 * d - 1).choose (2 * d) ≤
      (n + d - 1).choose d * ((n + d - 1).choose d + 1) / 2)
    (hr : r ≤ (n + d - 1).choose d) :
    0 ≤ euler n d r ↔ (r : ℝ) ≤
      criticalRoot ((n + d - 1).choose d) ((n + 2 * d - 1).choose (2 * d)) := by
  have h := eulerPolynomial_nonneg_iff hM hbound (r := (r : ℝ)) (by exact_mod_cast hr)
  rw [← euler_cast_eq_polynomial] at h
  exact_mod_cast h

theorem euler_nonpos_iff_criticalRoot (n d r : ℕ)
    (hM : 0 < (n + 2 * d - 1).choose (2 * d))
    (hbound : (n + 2 * d - 1).choose (2 * d) ≤
      (n + d - 1).choose d * ((n + d - 1).choose d + 1) / 2)
    (hr : r ≤ (n + d - 1).choose d) :
    euler n d r ≤ 0 ↔
      criticalRoot ((n + d - 1).choose d) ((n + 2 * d - 1).choose (2 * d)) ≤ (r : ℝ) := by
  have h := eulerPolynomial_nonpos_iff hM hbound (r := (r : ℝ)) (by exact_mod_cast hr)
  rw [← euler_cast_eq_polynomial] at h
  exact_mod_cast h

end Froberg
