module

public import ESCtoFroberg.UniversalInterpolation
public import ESCtoFroberg.GenericSyzygyTransport
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open Module MvPolynomial

def subspaceFinBasis {R V : Type*} [Field R] [AddCommGroup V] [Module R V]
    [Module.Finite R V] (W : Submodule R V) : Basis (Fin (finrank R W)) R W :=
  Module.finBasis R W

variable (K : Type*) [Field K] [Infinite K] (m p d : ℕ)

/-- A basis of the actual generic equations, with its expected number of generators. -/
def genericPointDegreeBasis :
    Basis (Fin ((m+d).choose d - p)) (GenericPointField K m p)
      (pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d) :=
  (subspaceFinBasis
    (pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d)).reindex
      (finCongr (genericPoint_pointDegreePiece_finrank (K := K) m p d))

variable {K m p d} {r : ℕ}

/-- Any prescribed equivalent generator count can index the actual generic basis. -/
theorem genericPoint_exists_fixed_basis (hr : r = (m+d).choose d - p) :
    Nonempty (Basis (Fin r) (GenericPointField K m p)
      (pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d)) := by
  subst r
  exact ⟨genericPointDegreeBasis K m p d⟩

end ESCtoFroberg
