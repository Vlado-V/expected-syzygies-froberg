module

public import Mathlib.Tactic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section
noncomputable section
namespace ESCtoFroberg
open Module

section Transfer
variable {R V W ι : Type*} [Field R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [Fintype ι]

/-- Change the coefficients of a tensor from the basis `b` to the basis `c`. -/
def basisTransfer (b c : Basis ι R V) : (ι → W) →ₗ[R] (ι → W) where
  toFun h j := ∑ i, c.repr (b i) j • h i
  map_add' h k := by ext j; simp [Finset.sum_add_distrib, smul_add]
  map_smul' a h := by ext j; simp [smul_smul, mul_comm, Finset.smul_sum]

@[simp] theorem basisTransfer_apply (b c : Basis ι R V) (h : ι → W) (j : ι) :
    basisTransfer b c h j = ∑ i, c.repr (b i) j • h i := rfl

theorem basisTransfer_inverse (b c : Basis ι R V) (h : ι → W) :
    basisTransfer c b (basisTransfer b c h) = h := by
  ext k
  simp only [basisTransfer_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hcoeff (i : ι) : ∑ j, b.repr (c j) k * c.repr (b i) j = b.repr (b i) k := by
    have hh := congrArg (fun v : V => b.repr v k) (c.sum_repr (b i))
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul] at hh
    simpa only [mul_comm] using hh
  simp_rw [← Finset.sum_smul, hcoeff]
  simp

/-- Tensor coefficient changes preserve the full vector space. -/
def basisTransferEquiv (b c : Basis ι R V) : (ι → W) ≃ₗ[R] (ι → W) where
  __ := basisTransfer b c
  invFun := basisTransfer c b
  left_inv := basisTransfer_inverse b c
  right_inv := basisTransfer_inverse c b

@[simp] theorem basisTransferEquiv_apply (b c : Basis ι R V) (h : ι → W) (j : ι) :
    basisTransferEquiv b c h j = ∑ i, c.repr (b i) j • h i := rfl

end Transfer

/-- Semilinear additive equivalences preserve dimension over a field automorphism. -/
theorem semilinear_finrank_eq {R V W : Type*} [Field R] [AddCommGroup V]
    [Module R V] [AddCommGroup W] [Module R W]
    (φ : R ≃+* R) (f : V ≃+ W)
    (hf : ∀ a v, f (a • v) = φ a • f v) :
    finrank R V = finrank R W := by
  simpa only [Module.finrank, Cardinal.toNat_lift] using
    congrArg Cardinal.toNat (lift_rank_eq_of_equiv_equiv φ f φ.bijective hf)

section TensorTransport
variable {R V W ι : Type*} [Field R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W] [Fintype ι]

theorem semilinear_symm_smul (φ : R ≃+* R) (F : V ≃+ V)
    (hF : ∀ a v, F (a • v) = φ a • F v) (a : R) (v : V) :
    F.symm (a • v) = φ.symm a • F.symm v := by
  apply F.injective
  simp [hF]

/-- The tensor product action, expressed in an arbitrary basis of its first factor. -/
def tensorTransport (b : Basis ι R V) (F : V ≃+ V) (G : W ≃+ W) :
    (ι → W) →+ (ι → W) where
  toFun h j := ∑ i, b.repr (F (b i)) j • G (h i)
  map_zero' := by ext j; simp
  map_add' h k := by ext j; simp [smul_add, Finset.sum_add_distrib]

@[simp] theorem tensorTransport_apply (b : Basis ι R V) (F : V ≃+ V)
    (G : W ≃+ W) (h : ι → W) (j : ι) :
    tensorTransport b F G h j = ∑ i, b.repr (F (b i)) j • G (h i) := rfl

theorem tensorTransport_inverse (b : Basis ι R V) (φ : R ≃+* R)
    (F : V ≃+ V) (hF : ∀ a v, F (a • v) = φ a • F v)
    (G : W ≃+ W) (hG : ∀ a v, G (a • v) = φ a • G v) (h : ι → W) :
    tensorTransport b F.symm G.symm (tensorTransport b F G h) = h := by
  ext k
  simp only [tensorTransport_apply, map_sum, semilinear_symm_smul φ G hG,
    AddEquiv.symm_apply_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hcoeff (i : ι) : ∑ j, b.repr (F.symm (b j)) k *
      φ.symm (b.repr (F (b i)) j) = b.repr (b i) k := by
    have hh := congrArg (fun v : V => b.repr (F.symm v) k) (b.sum_repr (F (b i)))
    simp only [map_sum, semilinear_symm_smul φ F hF, map_smul,
      Finsupp.finsetSum_apply, Finsupp.smul_apply, AddEquiv.symm_apply_apply, smul_eq_mul] at hh
    simpa only [mul_comm] using hh
  simp_rw [← Finset.sum_smul, hcoeff]
  simp

/-- A simultaneous semilinear action on the two tensor factors is invertible. -/
def tensorTransportEquiv (b : Basis ι R V) (φ : R ≃+* R)
    (F : V ≃+ V) (hF : ∀ a v, F (a • v) = φ a • F v)
    (G : W ≃+ W) (hG : ∀ a v, G (a • v) = φ a • G v) :
    (ι → W) ≃+ (ι → W) where
  __ := tensorTransport b F G
  invFun := tensorTransport b F.symm G.symm
  left_inv := tensorTransport_inverse b φ F hF G hG
  right_inv := tensorTransport_inverse b φ.symm F.symm (semilinear_symm_smul φ F hF)
    G.symm (semilinear_symm_smul φ G hG)

theorem tensorTransport_smul (b : Basis ι R V) (φ : R ≃+* R)
    (F : V ≃+ V) (G : W ≃+ W) (hG : ∀ a v, G (a • v) = φ a • G v)
    (a : R) (h : ι → W) :
    tensorTransport b F G (a • h) = φ a • tensorTransport b F G h := by
  ext j
  simp [tensorTransport_apply, hG, Finset.smul_sum, smul_smul, mul_comm]

end TensorTransport

end ESCtoFroberg
