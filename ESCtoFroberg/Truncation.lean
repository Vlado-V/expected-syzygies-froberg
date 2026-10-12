module

public import Froberg.HilbertSeries

@[expose] public section

namespace ESCtoFroberg

/-- A dimension sequence that matches the positive parts of the raw coefficients
and remains zero after its first zero agrees with positive truncation. -/
theorem raw_dimensions_eq_positiveTruncation
    (c : ℕ → ℤ) (h : ℕ → ℕ) (bound : ℕ)
    (hraw : ∀ j ≤ bound, h j = (c j).toNat)
    (hpersist : ∀ i j, i ≤ j → j ≤ bound → h i = 0 → h j = 0) :
    ∀ j ≤ bound, h j = Froberg.positiveTruncation c j := by
  classical
  intro j hj
  by_cases hpos : ∀ i ≤ j, 0 < c i
  · rw [Froberg.positiveTruncation_eq_of_positive c j hpos]
    exact hraw j hj
  · push Not at hpos
    obtain ⟨i, hij, hi⟩ := hpos
    rw [Froberg.positiveTruncation_eq_zero c j i hij hi]
    apply hpersist i j hij hj
    rw [hraw i (hij.trans hj)]
    exact Int.toNat_of_nonpos hi

end ESCtoFroberg
