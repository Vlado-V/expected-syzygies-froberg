module

public import ESCtoFroberg.GenericTransfer
public import ESCtoFroberg.LowerBound

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open Froberg

/-- A rational-field attaining family descends to an attaining family over the
original field and hence to a nonempty open in its full coefficient space. -/
theorem genericRawHilbertAt_of_rational_family
    {K F σ : Type*} [Field K] [Infinite K] [Field F]
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    {n d r e : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) (hr : r ≤ N n d)
    (he : e ≤ d) (q : Fin r → Forms F n d)
    (hq : hilbertFunction (familySpace q) (d+e) =
      (predictionCoefficient n d r (d+e)).toNat) :
    GenericRawHilbertAt K n d r (d+e) := by
  obtain ⟨qK,hqK⟩ := GenericTransfer.rationalFamily_hilbert_witness
    (K := K) (F := F) (σ := σ) (by omega) q e
  exact genericRawHilbertAt_of_family_witness (by omega) (by omega) hr
    (d+e) (by omega) qK (hqK.trans hq)

end ESCtoFroberg
