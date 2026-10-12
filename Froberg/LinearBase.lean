module

public import Froberg.LinearEndpoint
public import Froberg.Prefix
public import Froberg.Spanning

@[expose] public section

/-! The complete generating-degree-one base of the manuscript. -/
noncomputable section
namespace Froberg
variable {K : Type*} [Field K] [Infinite K] {n r : ℕ}

theorem predictedHilbertFunction_linear_endpoint (hn : 0 < n) (hr : r < n) :
    predictedHilbertFunction n 1 r 2 = expectedEndpoint n 1 r := by
  unfold predictedHilbertFunction
  rw [positiveTruncation_eq_of_positive]
  · exact congrArg Int.toNat (predictionCoefficient_at_endpoint n 1 r hn (by decide))
  · intro i hi
    interval_cases i
    · rw [predictionCoefficient_below_degree n 1 r 0 hn (by decide)]
      simp
    · rw [predictionCoefficient_before_endpoint n 1 r 1 hn le_rfl (by decide)]
      simp only [Nat.add_sub_cancel, Nat.choose_one_right, Nat.sub_self,
        Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      omega
    · rw [predictionCoefficient_at_endpoint n 1 r hn (by decide), euler_linear hr.le]
      exact_mod_cast Nat.choose_pos (show 2 ≤ n - r + 1 by omega)

/-- Every number of general linear forms satisfies the prediction through
degree two in every positive number of variables. -/
theorem genericHilbertThrough_linear (hn : 0 < n) (r : ℕ) :
    GenericHilbertThrough K n 1 r 2 := by
  by_cases hr : n ≤ r
  · exact genericHilbertThrough_of_many_generators hn (by decide)
      (by simpa using hr) 2
  · have hlt : r < n := by omega
    apply (genericHilbertThrough_iff 2).mpr
    intro j hj
    interval_cases j
    · exact genericHilbertAt_below_degree hn (by decide)
    · exact genericHilbertAt_generating_degree hn (by decide) (by simpa using hlt.le)
    · exact genericHilbertAt_of_genericEndpoint (genericEndpoint_linear hn hlt.le)
        (predictedHilbertFunction_linear_endpoint hn hlt)

theorem degree_one_base :
    ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      ∀ r : ℕ, GenericHilbertThrough K n 1 r (2 * 1) :=
  ⟨1, le_rfl, fun _ hn r => genericHilbertThrough_linear hn r⟩

end Froberg
