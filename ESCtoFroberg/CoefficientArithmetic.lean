module

public import ESCtoFroberg.Statement
public import ESCtoFroberg.LowerBound
public import Froberg.SimpleCases
public import Froberg.LinearBase

@[expose] public section

/-! Monomial counts, raw coefficients, and the unconditional boundary cases
used to assemble the manuscript's implication. -/
noncomputable section
namespace ESCtoFroberg
open Module MvPolynomial Froberg

/-- Monomial counts increase with the degree in every positive-variable ring. -/
theorem N_mono {n : ℕ} (hn : 1 ≤ n) : Monotone (N n) := by
  intro j k hjk
  have hN (t : ℕ) : N n t = (n + t - 1).choose (n - 1) := by
    exact Nat.choose_symm_of_eq_add (show n + t - 1 = t + (n - 1) by omega)
  rw [hN, hN]
  exact Nat.choose_le_choose (n - 1) (by omega)

/-- It suffices to check the two adjacent interpolation bounds. -/
theorem isInterpolationDegree_of_bounds {n d p : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hprev : N n (d - 1) < p) (hp : p ≤ N n d) : IsInterpolationDegree n d p := by
  refine ⟨hp, fun j hj => ?_⟩
  exact lt_of_le_of_lt (N_mono hn (show j ≤ d - 1 by omega)) hprev

/-- The raw coefficient before the endpoint has exactly its two Koszul terms. -/
theorem predictionCoefficient_prefix {n d r e : ℕ} (hn : 1 ≤ n) (he : e < d) :
    predictionCoefficient n d r (d + e) = (N n (d + e) : ℤ) - (r : ℤ) * N n e := by
  simpa only [N, Nat.add_sub_cancel_left] using
    predictionCoefficient_before_endpoint n d r (d + e) (by omega) (by omega) (by omega)

/-- At the endpoint the incoming constant Koszul boundaries add one term. -/
theorem predictionCoefficient_endpoint {n d r : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) :
    predictionCoefficient n d r (2 * d) =
      (N n (2 * d) : ℤ) - (r : ℤ) * N n d + (r.choose 2 : ℤ) := by
  simpa only [N, euler] using predictionCoefficient_at_endpoint n d r (by omega) (by omega)

theorem choppedRawCoefficient_prefix {n d p e : ℕ} (hn : 1 ≤ n) (he : e < d) :
    choppedRawCoefficient n d p e =
      (N n (d + e) : ℤ) - ((N n d - p : ℕ) : ℤ) * N n e :=
  predictionCoefficient_prefix hn he

theorem choppedRawCoefficient_endpoint {n d p : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) :
    choppedRawCoefficient n d p d = (N n (2 * d) : ℤ) -
      ((N n d - p : ℕ) : ℤ) * N n d + ((N n d - p).choose 2 : ℤ) := by
  simpa only [choppedRawCoefficient, ← two_mul] using
    predictionCoefficient_endpoint (r := N n d - p) hn hd

/-- The raw value in the generating degree is ordinary natural subtraction. -/
theorem predictionCoefficient_generating_degree_toNat {n d r : ℕ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) :
    (predictionCoefficient n d r d).toNat = N n d - r := by
  have hc := predictionCoefficient_prefix (r := r) (e := 0) hn (show 0 < d by omega)
  simp only [Nat.add_zero, N, Nat.choose_zero_right, Nat.cast_one, mul_one] at hc
  rw [hc]
  unfold N
  omega

variable {K : Type*} [Field K] {n d r : ℕ}

/-- Every tuple has the raw value below the generating degree. -/
theorem genericRawHilbertAt_below_degree (hn : 1 ≤ n) {j : ℕ} (hj : j < d) :
    GenericRawHilbertAt K n d r j := by
  refine ⟨1, ⟨fun _ => 0, by simp⟩, fun a _ => ?_⟩
  rw [predictionCoefficient_below_degree n d r j (by omega) hj]
  rw [hilbertFunction_below_degree (by omega) j hj _
    (coefficientSpace_homogeneous K n d r a)]
  simp

/-- Independence gives the raw value in the generating degree. -/
theorem genericRawHilbertAt_generating_degree (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hr : r ≤ N n d) : GenericRawHilbertAt K n d r d := by
  obtain ⟨D, hD, hprop⟩ := genericHilbertAt_generating_degree (K := K) (by omega)
    (by omega) hr
  refine ⟨D, hD, fun a ha => ?_⟩
  rw [hprop a ha, predictedHilbertFunction_generating_degree (by omega) (by omega),
    predictionCoefficient_generating_degree_toNat hn hd]
  rfl

/-- Only offsets `1` through `d` remain after the unconditional low degrees. -/
theorem genericRawThrough_of_offsets [Infinite K] (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hr : r ≤ N n d)
    (h : ∀ e : ℕ, 1 ≤ e → e ≤ d → GenericRawHilbertAt K n d r (d + e)) :
    GenericRawThrough K n d r (2 * d) := by
  apply (genericRawThrough_iff (2 * d)).mpr
  intro j hj
  by_cases hlow : j < d
  · exact genericRawHilbertAt_below_degree hn hlow
  · by_cases heq : j = d
    · subst j
      exact genericRawHilbertAt_generating_degree hn hd hr
    · have he : d + (j - d) = j := Nat.add_sub_of_le (by omega)
      simpa only [he] using h (j - d) (by omega) (by omega)

/-- The finite raw offset conclusions assemble into the positive truncation
on a common actual coefficient open. -/
theorem genericHilbertThrough_of_raw_offsets [Infinite K] (hn : 1 ≤ n) (hd : 1 ≤ d)
    (hr : r ≤ N n d)
    (h : ∀ e : ℕ, 1 ≤ e → e ≤ d → GenericRawHilbertAt K n d r (d + e)) :
    GenericHilbertThrough K n d r (2 * d) :=
  genericHilbertThrough_of_genericRawThrough (2 * d)
    (genericRawThrough_of_offsets hn hd hr h)

/-- All boundary cases are unconditional.  The full conclusion reduces to
positive generator counts strictly below the form dimension, with `n,d ≥ 2`. -/
theorem frobergThrough2d_of_inner_range [Infinite K]
    (hinner : ∀ n d : ℕ, 2 ≤ n → 2 ≤ d → ∀ r : ℕ, 1 ≤ r → r < N n d →
      GenericHilbertThrough K n d r (2 * d)) : FrobergThrough2d K := by
  intro n d hn hd r
  by_cases hn1 : n = 1
  · subst n
    exact genericHilbertThrough_one_variable (by omega) r (2 * d)
  · by_cases hd1 : d = 1
    · subst d
      simpa using genericHilbertThrough_linear (by omega) r
    · by_cases hr0 : r = 0
      · subst r
        exact genericHilbertThrough_zero_generators (by omega) (2 * d)
      · by_cases hrmany : N n d ≤ r
        · exact genericHilbertThrough_of_many_generators (by omega) (by omega) hrmany (2 * d)
        · exact hinner n d (by omega) (by omega) r (by omega) (by omega)

/-- A convenient final reduction phrased solely in the nontrivial raw offsets. -/
theorem frobergThrough2d_of_inner_raw_offsets [Infinite K]
    (hinner : ∀ n d : ℕ, 2 ≤ n → 2 ≤ d → ∀ r : ℕ, 1 ≤ r → r < N n d →
      ∀ e : ℕ, 1 ≤ e → e ≤ d → GenericRawHilbertAt K n d r (d + e)) :
    FrobergThrough2d K := by
  apply frobergThrough2d_of_inner_range
  intro n d hn hd r hr hrN
  exact genericHilbertThrough_of_raw_offsets (by omega) (by omega) hrN.le
    (hinner n d hn hd r hr hrN)

end ESCtoFroberg
