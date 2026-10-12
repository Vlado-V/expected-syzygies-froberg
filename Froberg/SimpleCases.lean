module

public import Froberg.GenericHilbertDimension
public import Froberg.Spanning

@[expose] public section

noncomputable section
namespace Froberg
open Module MvPolynomial
variable {K : Type*} [Field K] {n d : ℕ}

@[simp] theorem coefficientSpace_zero_generators (a : CoefficientIndex n d 0 → K) :
    coefficientSpace K n d 0 a = ⊥ := by
  simp [coefficientSpace]

theorem predictedHilbertFunction_zero_generators (hn : 0 < n) (j : ℕ) :
    predictedHilbertFunction n d 0 j = (n + j - 1).choose j := by
  unfold predictedHilbertFunction
  rw [positiveTruncation_eq_of_positive]
  · rw [predictionCoefficient_zero_generators n d j hn]
    simp
  · intro i _
    rw [predictionCoefficient_zero_generators n d i hn]
    exact_mod_cast monomial_count_pos hn i

/-- With no generators the ideal is zero and the prediction holds in every degree. -/
theorem genericHilbertThrough_zero_generators (hn : 0 < n) (bound : ℕ) :
    GenericHilbertThrough K n d 0 bound := by
  refine ⟨1, ⟨fun _ => 0, by simp⟩, fun a _ j _ => ?_⟩
  rw [coefficientSpace_zero_generators, predictedHilbertFunction_zero_generators hn]
  exact hilbertFunction_below_degree (d := j + 1) hn j (by omega) ⊥ bot_le

/-- In one variable, every positive number of generic degree-`d` generators
spans its one-dimensional homogeneous component. -/
theorem genericHilbertThrough_one_variable (hd : 0 < d) (r bound : ℕ) :
    GenericHilbertThrough K 1 d r bound := by
  by_cases hr : r = 0
  · subst r
    exact genericHilbertThrough_zero_generators (by decide) bound
  · apply genericHilbertThrough_of_many_generators (by decide) hd (by simpa using
      (show 1 ≤ r by omega)) bound

end Froberg
