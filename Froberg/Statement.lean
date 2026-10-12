module

public import Froberg.GenericDimensions
public import Froberg.HilbertSeries
public import Froberg.MonomialCounts

@[expose] public section

/-! Precise formulation of the requested theorem in the actual polynomial
quotient ring, and finite intersections of its generic conditions. -/
noncomputable section
namespace Froberg
open MvPolynomial

variable (K : Type*) [Field K] (n d r : ℕ)

/-- The predicted Hilbert function holds in a specified degree on a nonempty
principal open in the space of all ordered degree-`d` generator tuples. -/
def GenericHilbertAt (j : ℕ) : Prop :=
  ∃ D : MvPolynomial (CoefficientIndex n d r) K,
    (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
      hilbertFunction (coefficientSpace K n d r a) j = predictedHilbertFunction n d r j

/-- A single nonempty principal open on which all the required degrees agree. -/
def GenericHilbertThrough (bound : ℕ) : Prop :=
  ∃ D : MvPolynomial (CoefficientIndex n d r) K,
    (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 → ∀ j ≤ bound,
      hilbertFunction (coefficientSpace K n d r a) j = predictedHilbertFunction n d r j

variable {K n d r}

theorem genericHilbertAt_of_genericEndpoint (h : GenericEndpoint K n d r)
    (hpred : predictedHilbertFunction n d r (2 * d) = expectedEndpoint n d r) :
    GenericHilbertAt K n d r (2 * d) := by
  obtain ⟨D, hD, hprop⟩ := h
  exact ⟨D, hD, fun a ha => ((hprop a ha).2).trans hpred.symm⟩

theorem finite_principal_open_intersection [Infinite K] {ι σ : Type*}
    (s : Finset ι) (P : ι → (σ → K) → Prop)
    (h : ∀ i ∈ s, ∃ D : MvPolynomial σ K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 → P i a) :
    ∃ D : MvPolynomial σ K, (∃ a, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → ∀ i ∈ s, P i a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨1, ⟨fun _ => 0, by simp⟩, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨D, hD, hDprop⟩ := h i (Finset.mem_insert_self _ _)
      obtain ⟨E, hE, hEprop⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      obtain ⟨a₀, ha₀D, ha₀E⟩ := principal_opens_intersect hD hE
      refine ⟨D * E, ⟨a₀, by simpa using mul_ne_zero ha₀D ha₀E⟩, ?_⟩
      intro a ha j hj
      have hp : eval a D ≠ 0 ∧ eval a E ≠ 0 := by simpa using ha
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hDprop a hp.1
      · exact hEprop a hp.2 j hj

theorem genericHilbertThrough_iff [Infinite K] (bound : ℕ) :
    GenericHilbertThrough K n d r bound ↔ ∀ j ≤ bound, GenericHilbertAt K n d r j := by
  constructor
  · rintro ⟨D, hD, h⟩ j hj
    exact ⟨D, hD, fun a ha => h a ha j hj⟩
  · intro h
    obtain ⟨D, hD, hprop⟩ := finite_principal_open_intersection (Finset.range (bound + 1))
      (fun j a => hilbertFunction (coefficientSpace K n d r a) j =
        predictedHilbertFunction n d r j)
      (fun j hj => h j (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj))
    exact ⟨D, hD, fun a ha j hj => hprop a ha j (Finset.mem_range.mpr (by omega))⟩

theorem predictedHilbertFunction_below_degree (hn : 0 < n) {j : ℕ} (hj : j < d) :
    predictedHilbertFunction n d r j = (n + j - 1).choose j := by
  unfold predictedHilbertFunction
  rw [positiveTruncation_eq_of_positive]
  · rw [predictionCoefficient_below_degree n d r j hn hj]
    simp
  · intro i hi
    rw [predictionCoefficient_below_degree n d r i hn (by omega)]
    exact_mod_cast monomial_count_pos hn i

/-- Every generator tuple has the predicted Hilbert function below its degree. -/
theorem hilbertFunction_eq_prediction_below_degree (hn : 0 < n) {j : ℕ} (hj : j < d)
    (a : CoefficientIndex n d r → K) :
    hilbertFunction (coefficientSpace K n d r a) j = predictedHilbertFunction n d r j := by
  rw [predictedHilbertFunction_below_degree hn hj]
  exact hilbertFunction_below_degree hn j hj _ (coefficientSpace_homogeneous K n d r a)

theorem genericHilbertAt_below_degree (hn : 0 < n) {j : ℕ} (hj : j < d) :
    GenericHilbertAt K n d r j :=
  ⟨1, ⟨fun _ => 0, by simp⟩, fun a _ => hilbertFunction_eq_prediction_below_degree hn hj a⟩

theorem predictedHilbertFunction_zero_of_many_generators (hn : 0 < n) (hd : 0 < d)
    (hr : (n + d - 1).choose d ≤ r) {j : ℕ} (hj : d ≤ j) :
    predictedHilbertFunction n d r j = 0 := by
  apply positiveTruncation_eq_zero _ j d hj
  rw [predictionCoefficient_before_endpoint n d r d hn le_rfl (by omega)]
  simp only [Nat.sub_self, Nat.add_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
  exact sub_nonpos.mpr (by exact_mod_cast hr)

/-- Spanning the degree-`d` forms suffices for every degree of the prediction. -/
theorem hilbertFunction_eq_prediction_of_spanning (hn : 0 < n) (hd : 0 < d)
    (hr : (n + d - 1).choose d ≤ r)
    (a : CoefficientIndex n d r → K)
    (ha : Forms K n d ≤ coefficientSpace K n d r a) (j : ℕ) :
    hilbertFunction (coefficientSpace K n d r a) j = predictedHilbertFunction n d r j := by
  by_cases hj : j < d
  · exact hilbertFunction_eq_prediction_below_degree hn hj a
  · rw [predictedHilbertFunction_zero_of_many_generators hn hd hr (by omega)]
    exact hilbertFunction_zero_of_forms_le j (by omega) _ ha

end Froberg
