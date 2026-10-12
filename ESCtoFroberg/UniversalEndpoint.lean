module

public import ESCtoFroberg.EndpointBounds
public import ESCtoFroberg.GenericMotion
public import ESCtoFroberg.GenericEndpointSymmetry
public import ESCtoFroberg.UniversalInterpolation
public import ESCtoFroberg.CoefficientArithmetic

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace ESCtoFroberg
open Module MvPolynomial Froberg

/-- Inclusion of a subspace preserves the independence of any of its bases. -/
theorem basisSubtype_linearIndependent {R : Type*} [Field R]
    {V : Type*} [AddCommGroup V] [Module R V] {ι : Type*}
    (Q : Submodule R V) (b : Basis ι R Q) :
    LinearIndependent R (fun i => (b i).val) :=
  b.linearIndependent.map' Q.subtype Q.ker_subtype

/-- Any basis of an actual form subspace is independent in the ambient form space. -/
theorem basisFormFamily_linearIndependent {R : Type*} [Field R] {n d r : ℕ}
    (Q : Submodule R (Forms R n d)) (b : Basis (Fin r) R Q) :
    LinearIndependent R (basisFormFamily Q b) :=
  basisSubtype_linearIndependent Q b

/-- The form family attached to a basis spans exactly its actual subspace. -/
theorem basisFormFamily_span {R : Type*} [Field R] {n d r : ℕ}
    (Q : Submodule R (Forms R n d)) (b : Basis (Fin r) R Q) :
    Submodule.span R (Set.range (basisFormFamily Q b)) = Q := by
  have h := congrArg (fun W : Submodule R Q => W.map Q.subtype) b.span_eq
  rw [Submodule.map_span,Submodule.map_top,Submodule.range_subtype,←Set.range_comp] at h
  exact h

/-- Taking polynomial values of the basis gives the actual ambient equation space. -/
theorem basisFormFamily_familySpace {R : Type*} [Field R] {n d r : ℕ}
    (Q : Submodule R (Forms R n d)) (b : Basis (Fin r) R Q) :
    Froberg.familySpace (basisFormFamily Q b) = Q.map (Forms R n d).subtype := by
  have h := congrArg (fun W : Submodule R (Forms R n d) => W.map (Forms R n d).subtype)
    (basisFormFamily_span Q b)
  rw [Submodule.map_span,←Set.range_comp] at h
  exact h

variable (K : Type*) [Field K] [CharZero K] (m p d r : ℕ)

omit [CharZero K] in
/-- Independence of the universal point equation basis in actual homogeneous forms. -/
theorem genericBasisFamily_linearIndependent
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d)) :
    LinearIndependent (GenericPointField K m p) (genericBasisFamily K m p d r b) :=
  basisFormFamily_linearIndependent _ b

omit [CharZero K] in
/-- The universal basis spans the full actual homogeneous equation kernel. -/
theorem genericBasisFamily_span
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d)) :
    Submodule.span (GenericPointField K m p) (Set.range (genericBasisFamily K m p d r b)) =
      genericDegreePiece K m p d := basisFormFamily_span _ b

omit [CharZero K] in
theorem genericBasisFamily_familySpace
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d)) :
    Froberg.familySpace (genericBasisFamily K m p d r b) =
      pointDegreeSpace (GenericPointField K m p) (genericPointCoordinates K m p) d :=
  basisFormFamily_familySpace _ b

omit [CharZero K] in
/-- Every universal basis equation vanishes at every universal marked point. -/
theorem genericBasisFamily_vanish
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d)) :
    ∀ i j, eval (chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) j)
      (genericBasisFamily K m p d r b i).val = 0 := by
  intro i j
  exact (mem_pointDegreePiece (genericPointCoordinates K m p) (b i).val).mp (b i).property j

omit [CharZero K] in
/-- The endpoint actual quotient of a universal basis is the point chop quotient. -/
theorem genericBasisFamily_endpointQuotient_finrank
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d)) :
    finrank (GenericPointField K m p)
      (EndpointQuotient (GenericPointField K m p) (m+1) d
        (Submodule.span (GenericPointField K m p)
          (Set.range (fun i => (genericBasisFamily K m p d r b i).val)))) =
      choppedHilbertFunction (GenericPointField K m p) (genericPointCoordinates K m p) d (2*d) := by
  change finrank (GenericPointField K m p)
    (EndpointQuotient (GenericPointField K m p) (m+1) d
      (Froberg.familySpace (genericBasisFamily K m p d r b))) = _
  rw [endpoint_finrank_eq_hilbertFunction _ (Froberg.familySpace_homogeneous _)]
  rw [genericBasisFamily_familySpace]
  rfl

/-- In the nonseparated rank range the universal endpoint evaluation kernel
is exactly the constant Koszul boundary space. -/
theorem genericEndpoint_kernel_eq_koszul
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d))
    (hd : 1 ≤ d) (hp : (m+(d-1)).choose (d-1) ≤ p)
    (hτ : finrank (GenericPointField K m p)
      (endpointEvaluationImage (genericBasisFamily K m p d r b)
        (fun j => chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) j)) < p) :
    (endpointSyzygyEvaluation (genericBasisFamily K m p d r b)
      (fun j => chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) j)).ker =
        incomingInKernel (genericBasisFamily K m p d r b) := by
  apply endpoint_kernel_eq_koszul_of_motion
    (genericBasisFamily K m p d r b) (genericBasisFamily_linearIndependent K m p d r b)
    (fun j => chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) j)
    (fun _ => Fin.last m) (by omega)
  · intro a
    simp
  · exact genericBasisFamily_vanish K m p d r b
  · rw [genericBasisFamily_span]
    exact le_rfl
  · exact genericPoint_pointEvaluation_injective m p (d-1) hp
  · exact genericNoSinglePointSupport K m p d r b hτ
  · exact genericPoint_endpointMotionProperty K m p _ (genericBasisFamily_vanish K m p d r b)

/-- At a universal point plateau, a small endpoint evaluation image has its exact Euler dimension. -/
theorem genericEndpoint_evaluation_euler
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d))
    (hd : 1 ≤ d) (hp : (m+(d-1)).choose (d-1) ≤ p)
    (hH : choppedHilbertFunction (GenericPointField K m p)
      (genericPointCoordinates K m p) d (2*d) = p)
    (hτ : finrank (GenericPointField K m p)
      (endpointEvaluationImage (genericBasisFamily K m p d r b)
        (fun j => chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) j)) < p) :
    (finrank (GenericPointField K m p)
      (endpointEvaluationImage (genericBasisFamily K m p d r b)
        (fun j => chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) j)) : ℤ) =
      (p : ℤ) - euler (m+1) d r := by
  apply endpointEvaluationImage_euler _ (genericBasisFamily_linearIndependent K m p d r b)
    (by omega) _ (genericEndpoint_kernel_eq_koszul K m p d r b hd hp hτ)
  rw [genericBasisFamily_endpointQuotient_finrank]
  exact hH

/-- In the injective interpolation range, the endpoint plateau supplies the
full number of deformation rows prescribed by the raw coefficient. -/
theorem genericEndpoint_plateau_row_bound_of_large_p
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d))
    (hd : 1 ≤ d) (hp : (m+(d-1)).choose (d-1) ≤ p)
    (hH : choppedHilbertFunction (GenericPointField K m p)
      (genericPointCoordinates K m p) d (2*d) = p) :
    p - (predictionCoefficient (m+1) d r (2*d)).toNat ≤
      finrank (GenericPointField K m p)
        (endpointEvaluationImage (genericBasisFamily K m p d r b)
          (fun j => chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) j)) := by
  by_cases hlarge : p ≤ finrank (GenericPointField K m p)
      (endpointEvaluationImage (genericBasisFamily K m p d r b)
        (fun j => chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) j))
  · exact (Nat.sub_le _ _).trans hlarge
  · have hτ := lt_of_not_ge hlarge
    have hEuler := genericEndpoint_evaluation_euler K m p d r b hd hp hH hτ
    have hCoefficient : predictionCoefficient (m+1) d r (2*d) = euler (m+1) d r := by
      simpa only [euler, N] using
        (predictionCoefficient_endpoint (r := r) (show 1 ≤ m+1 by omega) hd)
    rw [hCoefficient]
    omega

/-- The actual universal endpoint plateau always supplies the prescribed
number of evaluation rows, including the separator interpolation range. -/
theorem genericEndpoint_plateau_row_bound
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d))
    (hm : 1 ≤ m) (hd : 1 ≤ d)
    (hH : choppedHilbertFunction (GenericPointField K m p)
      (genericPointCoordinates K m p) d (2*d) = p) :
    p - (predictionCoefficient (m+1) d r (2*d)).toNat ≤
      finrank (GenericPointField K m p)
        (endpointEvaluationImage (genericBasisFamily K m p d r b)
          (fun j => chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) j)) := by
  by_cases hp : p < (m+(d-1)).choose (d-1)
  · apply (Nat.sub_le _ _).trans
    exact points_le_endpointEvaluationImage_of_small_p (genericPointCoordinates K m p)
      (genericBasisFamily K m p d r b) hm (by omega)
      (genericBasisFamily_span K m p d r b)
      (genericPoint_pointEvaluation_surjective m p (d-1) (Nat.le_of_lt hp)) hp
  · exact genericEndpoint_plateau_row_bound_of_large_p K m p d r b hd
      (Nat.le_of_not_gt hp) hH

/-- The same endpoint row bound in the coefficient-evaluation convention used
by the first-order deformation construction. -/
theorem genericEndpoint_prefix_plateau_row_bound
    (b : Basis (Fin r) (GenericPointField K m p) (genericDegreePiece K m p d))
    (hm : 1 ≤ m) (hd : 1 ≤ d)
    (hH : choppedHilbertFunction (GenericPointField K m p)
      (genericPointCoordinates K m p) d (2*d) = p) :
    p - (predictionCoefficient (m+1) d r (d+d)).toNat ≤
      finrank (GenericPointField K m p)
        (Deformation.syzygyEvaluation (genericPointCoordinates K m p)
          (genericBasisFamily K m p d r b) d).range := by
  have h := genericEndpoint_plateau_row_bound K m p d r b hm hd hH
  rw [endpointEvaluationImage_finrank_eq_prefix] at h
  simpa only [two_mul] using h

end ESCtoFroberg
