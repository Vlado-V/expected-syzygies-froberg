module

public import Froberg.Graded
public import Mathlib.RingTheory.PowerSeries.WellKnown

@[expose] public section

/-! The actual formal power series of Fröberg's prediction and its endpoint coefficients. -/
noncomputable section
namespace Froberg
open PowerSeries

/-- `(1 - t^d)^r / (1 - t)^n`, as a formal power series with integer coefficients. -/
def predictionSeries (n d r : ℕ) : PowerSeries ℤ :=
  (1 - PowerSeries.X ^ d) ^ r * (PowerSeries.invOneSubPow ℤ n).val

def predictionCoefficient (n d r j : ℕ) : ℤ :=
  PowerSeries.coeff j (predictionSeries n d r)

/-- Positive truncation stops at the first nonpositive coefficient, including that coefficient. -/
def positiveTruncation (a : ℕ → ℤ) (j : ℕ) : ℕ := by
  classical
  exact if ∀ i ∈ Finset.range (j + 1), 0 < a i then (a j).toNat else 0

def predictedHilbertFunction (n d r j : ℕ) : ℕ :=
  positiveTruncation (predictionCoefficient n d r) j

theorem predictionCoefficient_zero_generators (n d j : ℕ) (hn : 0 < n) :
    predictionCoefficient n d 0 j = ((n + j - 1).choose j : ℤ) := by
  unfold predictionCoefficient predictionSeries
  rw [pow_zero, one_mul, invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos ℤ n hn, coeff_mk]
  congr 1
  have heq : n - 1 + j = n + j - 1 := by omega
  rw [heq, Nat.choose_symm_of_eq_add (show n + j - 1 = j + (n - 1) by omega)]

theorem predictionSeries_succ (n d r : ℕ) :
    predictionSeries n d (r + 1) = predictionSeries n d r -
      predictionSeries n d r * PowerSeries.X ^ d := by
  unfold predictionSeries
  rw [pow_succ]
  ring

theorem predictionCoefficient_succ (n d r j : ℕ) :
    predictionCoefficient n d (r + 1) j = predictionCoefficient n d r j -
      if d ≤ j then predictionCoefficient n d r (j - d) else 0 := by
  unfold predictionCoefficient
  rw [predictionSeries_succ, map_sub, coeff_mul_X_pow']

theorem predictionCoefficient_below_degree (n d r j : ℕ) (hn : 0 < n) (hj : j < d) :
    predictionCoefficient n d r j = ((n + j - 1).choose j : ℤ) := by
  induction r with
  | zero => exact predictionCoefficient_zero_generators n d j hn
  | succ r ih => rw [predictionCoefficient_succ, ite_eq_right (by omega), sub_zero, ih]

theorem predictionCoefficient_before_endpoint (n d r j : ℕ)
    (hn : 0 < n) (hdj : d ≤ j) (hj : j < 2 * d) :
    predictionCoefficient n d r j = ((n + j - 1).choose j : ℤ) -
      (r : ℤ) * (n + (j - d) - 1).choose (j - d) := by
  induction r with
  | zero => simp [predictionCoefficient_zero_generators n d j hn]
  | succ r ih =>
      rw [predictionCoefficient_succ, ite_eq_left hdj, ih,
        predictionCoefficient_below_degree n d r (j - d) hn (by omega)]
      push_cast
      ring

theorem predictionCoefficient_at_endpoint (n d r : ℕ) (hn : 0 < n) (hd : 0 < d) :
    predictionCoefficient n d r (2 * d) = euler n d r := by
  induction r with
  | zero => simp [predictionCoefficient_zero_generators n d (2 * d) hn, euler]
  | succ r ih =>
      rw [predictionCoefficient_succ, ite_eq_left (by omega : d ≤ 2 * d), ih]
      have hsub : 2 * d - d = d := by omega
      rw [hsub, predictionCoefficient_before_endpoint n d r d hn (by omega) (by omega)]
      have hchoose : (r + 1).choose 2 = r.choose 2 + r := by
        rw [Nat.choose_succ_succ]
        simp [Nat.add_comm]
      simp only [Nat.sub_self, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one,
        mul_one, euler, hchoose, Nat.cast_add, Nat.cast_one]
      ring

/-- If the whole prefix is positive, truncation retains its last coefficient. -/
theorem positiveTruncation_eq_of_positive (a : ℕ → ℤ) (j : ℕ)
    (h : ∀ i ≤ j, 0 < a i) : positiveTruncation a j = (a j).toNat := by
  classical
  unfold positiveTruncation
  apply ite_eq_left
  intro i hi
  exact h i (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi)

/-- Any earlier nonpositive coefficient forces every later truncated coefficient to zero. -/
theorem positiveTruncation_eq_zero (a : ℕ → ℤ) (j i : ℕ)
    (hij : i ≤ j) (hi : a i ≤ 0) : positiveTruncation a j = 0 := by
  classical
  unfold positiveTruncation
  apply ite_eq_right
  intro hall
  have hp := hall i (Finset.mem_range.mpr (by omega))
  omega

end Froberg
