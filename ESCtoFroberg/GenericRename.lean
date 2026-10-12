module

public import ESCtoFroberg.Points
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.Localization.FractionRing

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open MvPolynomial

abbrev GenericPointRing (K : Type*) [Field K] (m p : ℕ) :=
  MvPolynomial (Fin p × Fin m) K

abbrev GenericPointField (K : Type*) [Field K] (m p : ℕ) :=
  FractionRing (GenericPointRing K m p)

def genericPointCoordinates (K : Type*) [Field K] (m p : ℕ) :
    PointCoordinates (GenericPointField K m p) m p :=
  fun ij => algebraMap (GenericPointRing K m p) (GenericPointField K m p) (X ij)

def pointPermutationRingEquiv (K : Type*) [Field K] (m p : ℕ)
    (sigma : Equiv.Perm (Fin p)) : GenericPointRing K m p ≃+* GenericPointRing K m p :=
  (MvPolynomial.renameEquiv K (Equiv.prodCongr sigma (Equiv.refl (Fin m)))).toRingEquiv

def pointPermutationFieldEquiv (K : Type*) [Field K] (m p : ℕ)
    (sigma : Equiv.Perm (Fin p)) : GenericPointField K m p ≃+* GenericPointField K m p :=
  IsFractionRing.ringEquivOfRingEquiv (pointPermutationRingEquiv K m p sigma)

@[simp] theorem pointPermutationFieldEquiv_coordinate (K : Type*) [Field K]
    (m p : ℕ) (sigma : Equiv.Perm (Fin p)) (i : Fin p) (j : Fin m) :
    pointPermutationFieldEquiv K m p sigma (genericPointCoordinates K m p (i,j)) =
      genericPointCoordinates K m p (sigma i,j) := by
  simp [pointPermutationFieldEquiv, genericPointCoordinates,
    pointPermutationRingEquiv]

@[simp] theorem pointPermutationFieldEquiv_symm (K : Type*) [Field K]
    (m p : ℕ) (sigma : Equiv.Perm (Fin p)) :
    (pointPermutationFieldEquiv K m p sigma).symm =
      pointPermutationFieldEquiv K m p sigma.symm := by
  change IsFractionRing.ringEquivOfRingEquiv
      (pointPermutationRingEquiv K m p sigma).symm = _
  congr 1

@[simp] theorem pointPermutationFieldEquiv_chartPoint (K : Type*) [Field K]
    (m p : ℕ) (sigma : Equiv.Perm (Fin p)) (i : Fin p) (j : Fin (m+1)) :
    pointPermutationFieldEquiv K m p sigma
        (chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) i j) =
      chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) (sigma i) j := by
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp
  · simp

/-- Changing coefficients along a field automorphism preserves homogeneous forms. -/
def coefficientFormsEquiv {R S : Type*} [Field R] [Field S] (phi : R ≃+* S)
    (n d : ℕ) :
    letI : RingHomInvPair phi.toRingHom phi.symm.toRingHom := RingHomInvPair.of_ringEquiv phi
    letI : RingHomInvPair phi.symm.toRingHom phi.toRingHom := RingHomInvPair.of_ringEquiv_symm phi
    LinearEquiv (σ' := phi.symm.toRingHom) phi.toRingHom (Forms R n d) (Forms S n d) := by
  letI : RingHomInvPair phi.toRingHom phi.symm.toRingHom := RingHomInvPair.of_ringEquiv phi
  letI : RingHomInvPair phi.symm.toRingHom phi.toRingHom := RingHomInvPair.of_ringEquiv_symm phi
  exact {
    toFun := fun f => ⟨MvPolynomial.map phi.toRingHom f.val, f.property.map phi.toRingHom⟩
    invFun := fun f => ⟨MvPolynomial.map phi.symm.toRingHom f.val,
      f.property.map phi.symm.toRingHom⟩
    left_inv := fun f => Subtype.ext ((MvPolynomial.mapEquiv (Fin n) phi).left_inv f.val)
    right_inv := fun f => Subtype.ext ((MvPolynomial.mapEquiv (Fin n) phi).right_inv f.val)
    map_add' := fun f g => Subtype.ext (map_add _ _ _)
    map_smul' := fun c f => Subtype.ext (by
      change MvPolynomial.map phi.toRingHom (c • f.val) = phi c • MvPolynomial.map phi.toRingHom f.val
      simp [MvPolynomial.smul_eq_C_mul]) }

@[simp] theorem coefficientFormsEquiv_val {R S : Type*} [Field R] [Field S]
    (phi : R ≃+* S) {n d : ℕ} (f : Forms R n d) :
    ((coefficientFormsEquiv phi n d).toFun f).val = MvPolynomial.map phi.toRingHom f.val := rfl

theorem coefficientFormsEquiv_bijective {R S : Type*} [Field R] [Field S]
    (phi : R ≃+* S) (n d : ℕ) :
    Function.Bijective (coefficientFormsEquiv phi n d).toFun := by
  constructor
  · intro f g h
    apply Subtype.ext
    exact (MvPolynomial.mapEquiv (Fin n) phi).injective (congrArg Subtype.val h)
  · intro f
    refine ⟨⟨MvPolynomial.map phi.symm.toRingHom f.val,
      f.property.map phi.symm.toRingHom⟩, ?_⟩
    exact Subtype.ext ((MvPolynomial.mapEquiv (Fin n) phi).right_inv f.val)

def coefficientFormsAddEquiv {R S : Type*} [Field R] [Field S]
    (phi : R ≃+* S) (n d : ℕ) : Forms R n d ≃+ Forms S n d := by
  letI : RingHomInvPair phi.toRingHom phi.symm.toRingHom := RingHomInvPair.of_ringEquiv phi
  letI : RingHomInvPair phi.symm.toRingHom phi.toRingHom := RingHomInvPair.of_ringEquiv_symm phi
  exact (coefficientFormsEquiv phi n d).toAddEquiv

@[simp] theorem coefficientFormsAddEquiv_apply {R S : Type*} [Field R] [Field S]
    (phi : R ≃+* S) {n d : ℕ} (f : Forms R n d) :
    coefficientFormsAddEquiv phi n d f = (coefficientFormsEquiv phi n d).toFun f := rfl

theorem coefficientFormsAddEquiv_smul {R S : Type*} [Field R] [Field S]
    (phi : R ≃+* S) {n d : ℕ} (c : R) (f : Forms R n d) :
    coefficientFormsAddEquiv phi n d (c • f) = phi c • coefficientFormsAddEquiv phi n d f := by
  apply Subtype.ext
  change MvPolynomial.map phi.toRingHom (c • f.val) = phi c • MvPolynomial.map phi.toRingHom f.val
  simp [MvPolynomial.smul_eq_C_mul]

/-- Evaluation commutes with simultaneous transport of coefficients and point coordinates. -/
theorem eval_map_coefficientEquiv {R S : Type*} [Field R] [Field S] {n : ℕ}
    (phi : R ≃+* S) (x : Fin n → R) (f : Poly R n) :
    eval (fun j => phi (x j)) (MvPolynomial.map phi.toRingHom f) = phi (eval x f) := by
  rw [MvPolynomial.eval_map]
  exact (MvPolynomial.eval₂_comp_left phi.toRingHom (RingHom.id R) x f).symm

theorem eval_pointPermutationFormsEquiv (K : Type*) [Field K] (m p d : ℕ)
    (sigma : Equiv.Perm (Fin p)) (f : Forms (GenericPointField K m p) (m+1) d)
    (i : Fin p) :
    eval (chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) (sigma i))
        ((coefficientFormsEquiv (pointPermutationFieldEquiv K m p sigma) (m+1) d).toFun f).val =
      pointPermutationFieldEquiv K m p sigma
        (eval (chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) i) f.val) := by
  rw [coefficientFormsEquiv_val]
  convert eval_map_coefficientEquiv (pointPermutationFieldEquiv K m p sigma)
    (chartPoint (GenericPointField K m p) (genericPointCoordinates K m p) i) f.val using 1
  simp

theorem coefficientFormsEquiv_mul_val {R S : Type*} [Field R] [Field S]
    (phi : R ≃+* S) {n d e : ℕ} (f : Forms R n d) (g : Forms R n e) :
    MvPolynomial.map phi.toRingHom (f.val * g.val) =
      ((coefficientFormsEquiv phi n d).toFun f).val * ((coefficientFormsEquiv phi n e).toFun g).val :=
  map_mul _ _ _

theorem coefficientFormsEquiv_mem_genericPointKernel_iff (K : Type*) [Field K]
    (m p d : ℕ) (sigma : Equiv.Perm (Fin p))
    (f : Forms (GenericPointField K m p) (m+1) d) :
    (coefficientFormsEquiv (pointPermutationFieldEquiv K m p sigma) (m+1) d).toFun f ∈
        pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d ↔
      f ∈ pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d := by
  rw [mem_pointDegreePiece, mem_pointDegreePiece]
  constructor
  · intro h i
    have hi := h (sigma i)
    rw [eval_pointPermutationFormsEquiv] at hi
    exact (pointPermutationFieldEquiv K m p sigma).injective (by simpa using hi)
  · intro h i
    obtain ⟨j, rfl⟩ := sigma.surjective i
    rw [eval_pointPermutationFormsEquiv, h j]
    exact map_zero _

def genericPointKernelAddEquiv (K : Type*) [Field K] (m p d : ℕ)
    (sigma : Equiv.Perm (Fin p)) :
    pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d ≃+
      pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d := by
  let E := coefficientFormsAddEquiv (pointPermutationFieldEquiv K m p sigma) (m+1) d
  have hE (f : Forms (GenericPointField K m p) (m+1) d) :
      E f ∈ pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d ↔
        f ∈ pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d :=
    coefficientFormsEquiv_mem_genericPointKernel_iff K m p d sigma f
  exact {
    toFun := fun f => ⟨E f.val, (hE f.val).mpr f.property⟩
    invFun := fun f => ⟨E.symm f.val, (hE (E.symm f.val)).mp (by simp)⟩
    left_inv := fun f => Subtype.ext (E.symm_apply_apply f.val)
    right_inv := fun f => Subtype.ext (E.apply_symm_apply f.val)
    map_add' := fun f g => Subtype.ext (E.map_add f.val g.val) }

@[simp] theorem genericPointKernelAddEquiv_apply (K : Type*) [Field K]
    (m p d : ℕ) (sigma : Equiv.Perm (Fin p))
    (f : pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d) :
    (genericPointKernelAddEquiv K m p d sigma f).val =
      coefficientFormsAddEquiv (pointPermutationFieldEquiv K m p sigma) (m+1) d f.val := rfl

theorem genericPointKernelAddEquiv_smul (K : Type*) [Field K]
    (m p d : ℕ) (sigma : Equiv.Perm (Fin p)) (c : GenericPointField K m p)
    (f : pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d) :
    genericPointKernelAddEquiv K m p d sigma (c • f) =
      pointPermutationFieldEquiv K m p sigma c • genericPointKernelAddEquiv K m p d sigma f := by
  apply Subtype.ext
  exact coefficientFormsAddEquiv_smul (pointPermutationFieldEquiv K m p sigma) c f.val

end ESCtoFroberg
