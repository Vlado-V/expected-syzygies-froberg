module

public import Froberg.Koszul
public import Froberg.RootSigns
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section

/-! Concrete monomial bounds and the two critical generator counts. -/

noncomputable section
namespace Froberg
open Module

/-- Positive-variable polynomial rings have a monomial in every degree. -/
theorem monomial_count_pos {n : ℕ} (hn : 0 < n) (d : ℕ) :
    0 < (n + d - 1).choose d :=
  Nat.choose_pos (by omega)

/-- Polynomial multiplication and its independent constant Koszul relations
bound the degree-`2*d` monomial count by the symmetric-square dimension. -/
theorem monomial_count_symmetric_bound {n : ℕ} (hn : 0 < n) (d : ℕ) :
    (n + 2 * d - 1).choose (2 * d) ≤
      (n + d - 1).choose d * ((n + d - 1).choose d + 1) / 2 := by
  classical
  let b := Module.finBasis ℚ (Forms ℚ n d)
  have hspan : Submodule.span ℚ (Set.range (fun i => (b i).val)) = Forms ℚ n d := by
    calc
      _ = (Submodule.span ℚ (Set.range b)).map (Forms ℚ n d).subtype := by
        rw [Submodule.map_span]
        congr 1
        ext p
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨b i, ⟨i, rfl⟩, rfl⟩
        · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, rfl⟩
      _ = Forms ℚ n d := by
        rw [b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hrange : LinearMap.range (endpointMultiplication b) = ⊤ := by
    rw [range_endpointMultiplication, hspan, endpointProducts_all]
  have hb := endpoint_rank_add_pairs_le hn b b.linearIndependent
  rw [hrange, finrank_top, finrank_forms ℚ n (2 * d) hn,
    finrank_forms ℚ n d hn] at hb
  let D := (n + d - 1).choose d
  let M := (n + 2 * d - 1).choose (2 * d)
  have hreal : (M : ℝ) + (D.choose 2 : ℝ) ≤ (D : ℝ) * D := by
    exact_mod_cast hb
  rw [Nat.cast_choose_two] at hreal
  have htwoReal : 2 * (M : ℝ) ≤ (D : ℝ) * (D + 1) := by nlinarith
  have htwo : 2 * M ≤ D * (D + 1) := by exact_mod_cast htwoReal
  change M ≤ D * (D + 1) / 2
  omega

/-- The critical generator count from the manuscript. -/
def kappa (n d : ℕ) : ℝ :=
  criticalRoot ((n + d - 1).choose d) ((n + 2 * d - 1).choose (2 * d))

/-- The smaller integer generator count adjacent to the critical root. -/
def lowerCount (n d : ℕ) : ℕ := ⌊kappa n d⌋₊

/-- The larger integer generator count adjacent to the critical root. -/
def upperCount (n d : ℕ) : ℕ := ⌈kappa n d⌉₊

theorem kappa_bounds {n : ℕ} (hn : 0 < n) (d : ℕ) :
    0 < kappa n d ∧ kappa n d ≤ (n + d - 1).choose d :=
  criticalRoot_bounds (monomial_count_pos hn (2 * d)) (monomial_count_symmetric_bound hn d)

theorem lowerCount_le_monomial_count {n : ℕ} (hn : 0 < n) (d : ℕ) :
    lowerCount n d ≤ (n + d - 1).choose d :=
  Nat.floor_le_of_le (kappa_bounds hn d).2

theorem upperCount_le_monomial_count {n : ℕ} (hn : 0 < n) (d : ℕ) :
    upperCount n d ≤ (n + d - 1).choose d :=
  Nat.ceil_le.mpr (kappa_bounds hn d).2

theorem lowerCount_le_upperCount (n d : ℕ) : lowerCount n d ≤ upperCount n d :=
  Nat.floor_le_ceil _

theorem upperCount_le_lowerCount_add_one (n d : ℕ) :
    upperCount n d ≤ lowerCount n d + 1 :=
  Nat.ceil_le_floor_add_one _

theorem lowerCount_le_kappa {n : ℕ} (hn : 0 < n) (d : ℕ) :
    (lowerCount n d : ℝ) ≤ kappa n d :=
  Nat.floor_le (kappa_bounds hn d).1.le

theorem kappa_le_upperCount (n d : ℕ) : kappa n d ≤ (upperCount n d : ℝ) :=
  Nat.le_ceil _

theorem euler_nonneg_iff_kappa {n : ℕ} (hn : 0 < n) (d r : ℕ)
    (hr : r ≤ (n + d - 1).choose d) :
    0 ≤ euler n d r ↔ (r : ℝ) ≤ kappa n d :=
  euler_nonneg_iff_criticalRoot n d r (monomial_count_pos hn (2 * d))
    (monomial_count_symmetric_bound hn d) hr

theorem euler_nonpos_iff_kappa {n : ℕ} (hn : 0 < n) (d r : ℕ)
    (hr : r ≤ (n + d - 1).choose d) :
    euler n d r ≤ 0 ↔ kappa n d ≤ (r : ℝ) :=
  euler_nonpos_iff_criticalRoot n d r (monomial_count_pos hn (2 * d))
    (monomial_count_symmetric_bound hn d) hr

/-- The lower critical count is on the nonnegative side of the Euler root. -/
theorem euler_lowerCount_nonneg {n : ℕ} (hn : 0 < n) (d : ℕ) :
    0 ≤ euler n d (lowerCount n d) :=
  (euler_nonneg_iff_kappa hn d _ (lowerCount_le_monomial_count hn d)).mpr
    (lowerCount_le_kappa hn d)

/-- The upper critical count is on the nonpositive side of the Euler root. -/
theorem euler_upperCount_nonpos {n : ℕ} (hn : 0 < n) (d : ℕ) :
    euler n d (upperCount n d) ≤ 0 :=
  (euler_nonpos_iff_kappa hn d _ (upperCount_le_monomial_count hn d)).mpr
    (kappa_le_upperCount n d)

/-- The upper critical count is positive. -/
theorem upperCount_pos {n : ℕ} (hn : 0 < n) (d : ℕ) : 0 < upperCount n d := by
  have h := (kappa_bounds hn d).1.trans_le (kappa_le_upperCount n d)
  exact_mod_cast h

/-- On integer generator counts, the nonnegative range ends at the floor. -/
theorem euler_nonneg_iff_le_lowerCount {n : ℕ} (hn : 0 < n) (d r : ℕ)
    (hr : r ≤ (n + d - 1).choose d) :
    0 ≤ euler n d r ↔ r ≤ lowerCount n d :=
  (euler_nonneg_iff_kappa hn d r hr).trans
    (Nat.le_floor_iff (kappa_bounds hn d).1.le).symm

/-- On integer generator counts, the nonpositive range starts at the ceiling. -/
theorem euler_nonpos_iff_upperCount_le {n : ℕ} (hn : 0 < n) (d r : ℕ)
    (hr : r ≤ (n + d - 1).choose d) :
    euler n d r ≤ 0 ↔ upperCount n d ≤ r :=
  (euler_nonpos_iff_kappa hn d r hr).trans Nat.ceil_le.symm

/-- There is no missing integer count between the two critical counts. -/
theorem le_lowerCount_or_upperCount_le (n d r : ℕ) :
    r ≤ lowerCount n d ∨ upperCount n d ≤ r := by
  have h := upperCount_le_lowerCount_add_one n d
  omega

end Froberg
