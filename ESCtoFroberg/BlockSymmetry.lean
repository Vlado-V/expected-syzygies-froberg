module

public import ESCtoFroberg.BasisTransfer
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section
noncomputable section
namespace ESCtoFroberg
open Module

/-- Restrict an additive automorphism to an invariant linear subspace. -/
def submoduleAddEquiv {R V : Type*} [Field R] [AddCommGroup V] [Module R V]
    (F : V ≃+ V) (Q : Submodule R V) (hQ : ∀ x, x ∈ Q ↔ F x ∈ Q) : Q ≃+ Q where
  toFun x := ⟨F x.val, (hQ x.val).mp x.property⟩
  invFun x := ⟨F.symm x.val, (hQ (F.symm x.val)).mpr (by simp)⟩
  left_inv x := Subtype.ext (F.symm_apply_apply x.val)
  right_inv x := Subtype.ext (F.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (map_add F x.val y.val)

/-- A semilinear change of coordinates identifies the ranges of intertwining maps. -/
def semilinearRangeEquiv {R H H' W W' : Type*} [Field R]
    [AddCommGroup H] [Module R H] [AddCommGroup H'] [Module R H']
    [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (A : H →ₗ[R] W) (A' : H' →ₗ[R] W') (F : H ≃+ H') (B : W ≃+ W')
    (h : ∀ x, A' (F x) = B (A x)) : A.range ≃+ A'.range where
  toFun y := ⟨B y.val, by
    obtain ⟨x, hx⟩ := y.property
    exact ⟨F x, by rw [h, hx]⟩⟩
  invFun y := ⟨B.symm y.val, by
    obtain ⟨x, hx⟩ := y.property
    refine ⟨F.symm x, ?_⟩
    apply B.injective
    rw [← h, F.apply_symm_apply, hx, B.apply_symm_apply]⟩
  left_inv y := Subtype.ext (B.symm_apply_apply y.val)
  right_inv y := Subtype.ext (B.apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add B x.val y.val)

theorem finrank_range_eq_of_semilinear {R H H' W W' : Type*} [Field R]
    [AddCommGroup H] [Module R H] [AddCommGroup H'] [Module R H']
    [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module R W']
    (A : H →ₗ[R] W) (A' : H' →ₗ[R] W') (φ : R ≃+* R)
    (F : H ≃+ H') (B : W ≃+ W')
    (hB : ∀ a w, B (a • w) = φ a • B w)
    (h : ∀ x, A' (F x) = B (A x)) : finrank R A.range = finrank R A'.range := by
  exact semilinear_finrank_eq φ (semilinearRangeEquiv A A' F B h)
    (fun a y => Subtype.ext (hB a y.val))

/-- Reindex blocks while applying the same additive coordinate change to each block. -/
def blocksAddEquiv {α β W W' : Type*} [AddCommGroup W] [AddCommGroup W']
    (e : α ≃ β) (B : W ≃+ W') : (α → W) ≃+ (β → W') where
  toFun y j := B (y (e.symm j))
  invFun y i := B.symm (y (e i))
  left_inv y := by ext i; simp
  right_inv y := by ext j; simp
  map_add' x y := by ext j; exact map_add B _ _

@[simp] theorem blocksAddEquiv_apply {α β W W' : Type*}
    [AddCommGroup W] [AddCommGroup W'] (e : α ≃ β) (B : W ≃+ W')
    (y : α → W) (j : β) : blocksAddEquiv e B y j = B (y (e.symm j)) := rfl

/-- A semilinear permutation action on actual evaluation blocks preserves every
projection rank when the selected labels are permuted. -/
theorem blockProjectionRank_permutation {R H W ι : Type*} [Field R]
    [AddCommGroup H] [Module R H] [AddCommGroup W] [Module R W]
    [Fintype ι] [DecidableEq ι]
    (E : ι → H →ₗ[R] W) (S T : Finset ι) (σ : Equiv.Perm ι)
    (e : S ≃ T) (he : ∀ i : S, (e i).val = σ i.val)
    (φ : R ≃+* R) (F : H ≃+ H) (B : W ≃+ W)
    (hB : ∀ a w, B (a • w) = φ a • B w)
    (hE : ∀ i x, E (σ i) (F x) = B (E i x)) :
    finrank R (LinearMap.pi (fun i : S => E i.val)).range =
      finrank R (LinearMap.pi (fun i : T => E i.val)).range := by
  apply finrank_range_eq_of_semilinear _ _ φ F (blocksAddEquiv e B)
  · intro a y
    ext j
    exact hB a (y (e.symm j))
  · intro x
    ext j
    change E j.val (F x) = B (E (e.symm j).val x)
    have hj : j.val = σ (e.symm j).val := by
      simpa using he (e.symm j)
    rw [hj, hE]

/-- An actual action for every permutation implies that projection ranks depend
only on the cardinality of the selected set. -/
theorem blockProjectionRank_cardinality {R H W ι : Type*} [Field R]
    [AddCommGroup H] [Module R H] [AddCommGroup W] [Module R W]
    [Fintype ι] [DecidableEq ι] (E : ι → H →ₗ[R] W)
    (hAction : ∀ σ : Equiv.Perm ι, ∃ (φ : R ≃+* R) (F : H ≃+ H) (B : W ≃+ W),
      (∀ a w, B (a • w) = φ a • B w) ∧
      ∀ i x, E (σ i) (F x) = B (E i x))
    (S T : Finset ι) (hST : S.card = T.card) :
    finrank R (LinearMap.pi (fun i : S => E i.val)).range =
      finrank R (LinearMap.pi (fun i : T => E i.val)).range := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq S T hST
  let e : S ≃ T := Equiv.subtypeEquiv σ (by
    intro i
    rw [← hσ]
    simp)
  obtain ⟨φ, F, B, hB, hE⟩ := hAction σ
  exact blockProjectionRank_permutation E S T σ e (fun _ => rfl) φ F B hB hE

end ESCtoFroberg
