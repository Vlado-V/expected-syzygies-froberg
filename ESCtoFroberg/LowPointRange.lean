module

public import ESCtoFroberg.BeforeEndpointMonomial
public import ESCtoFroberg.CoefficientArithmetic

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open Froberg

variable {K : Type*} [Field K] [Infinite K] {n d e p : ℕ}

/-- The explicit monomial family settles the prefix when there are fewer
points than degree-e forms. -/
theorem genericRawHilbertAt_low_point_count (hn : 1 ≤ n) (hd : 1 ≤ d)
    (he : e < d) (hp : p < N n e) :
    GenericRawHilbertAt K n d (N n d - p) (d + e) := by
  have hzero : genericHilbertDimension K n d (N n d - p) (d+e) = 0 :=
    genericHilbertDimension_low_p_eq_zero (by omega) he hp
  have hlow := genericHilbertDimension_raw_lower_bound (K := K)
    (n := n) (d := d) (r := N n d - p)
    (by omega) (by omega) (Nat.sub_le _ _) (d+e) (by omega)
  rw [hzero] at hlow
  apply (genericRawHilbertAt_iff_genericHilbertDimension (by omega) (d+e)).mpr
  omega

end ESCtoFroberg
