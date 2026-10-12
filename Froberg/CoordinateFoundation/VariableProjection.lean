module

public import Froberg.CoordinateFoundation.LinearCoordinates
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

noncomputable section
namespace Froberg.CoordinateFoundation.VariableProjection
open MvPolynomial Module LinearCoordinates
variable {K σ ι τ : Type*} [Field K]

/-- The span of the variables to be killed. -/
def leftSpace (K ι τ : Type*) [Field K] : Submodule K (MvPolynomial (ι ⊕ τ) K) :=
  Submodule.span K (Set.range (fun i : ι => (X (Sum.inl i) : MvPolynomial (ι ⊕ τ) K)))

theorem leftSpace_homogeneous : leftSpace K ι τ ≤ H K (ι ⊕ τ) 1 := by
  apply Submodule.span_le.mpr
  rintro p ⟨i, rfl⟩
  exact isHomogeneous_X K (Sum.inl i)

/-- Set all left variables to zero, retaining each right variable. -/
def dropLeft : MvPolynomial (ι ⊕ τ) K →ₐ[K] MvPolynomial τ K :=
  aeval (Sum.elim (fun _ => 0) X)

@[simp] theorem dropLeft_X_left (i : ι) : dropLeft (K := K) (τ := τ) (X (Sum.inl i)) = 0 := by
  simp [dropLeft]

@[simp] theorem dropLeft_X_right (i : τ) : dropLeft (K := K) (ι := ι) (X (Sum.inr i)) = X i := by
  simp [dropLeft]

@[simp] theorem dropLeft_rename (p : MvPolynomial τ K) :
    dropLeft (ι := ι) (rename Sum.inr p) = p := by
  have he : (dropLeft (K := K) (ι := ι) (τ := τ)).comp (rename Sum.inr) = AlgHom.id K _ := by
    ext i
    simp
  exact AlgHom.congr_fun he p

theorem dropLeft_eq_zero_of_mem {p : MvPolynomial (ι ⊕ τ) K}
    (hp : p ∈ leftSpace K ι τ) : dropLeft p = 0 := by
  have he : leftSpace K ι τ ≤ LinearMap.ker (dropLeft (K := K)).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro p ⟨i, rfl⟩
    simp
  exact he hp

private theorem sub_section_mem_ideal (p : MvPolynomial (ι ⊕ τ) K) :
    p - rename Sum.inr (dropLeft p) ∈ Ideal.span (leftSpace K ι τ : Set _) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [dropLeft]
  | add p q hp hq =>
      convert (Ideal.span (leftSpace K ι τ : Set _)).add_mem hp hq using 1
      simp only [map_add]
      ring
  | mul_X p i hp =>
      cases i with
      | inl i =>
          simpa using Ideal.mul_mem_left (Ideal.span (leftSpace K ι τ : Set _)) p
            (Ideal.subset_span (Submodule.subset_span (Set.mem_range_self i)))
      | inr i =>
          convert Ideal.mul_mem_right (X (Sum.inr i)) _ hp using 1
          simp only [map_mul, dropLeft_X_right, rename_X]
          ring

theorem dropLeft_zero_iff_ideal (p : MvPolynomial (ι ⊕ τ) K) :
    dropLeft p = 0 ↔ p ∈ Ideal.span (leftSpace K ι τ : Set _) := by
  constructor
  · intro h
    simpa only [h, map_zero, sub_zero] using sub_section_mem_ideal p
  · intro hp
    have hI : Ideal.span (leftSpace K ι τ : Set (MvPolynomial (ι ⊕ τ) K)) ≤
        RingHom.ker (dropLeft (K := K) (ι := ι) (τ := τ)).toRingHom := by
      apply Ideal.span_le.mpr
      intro f hf
      exact dropLeft_eq_zero_of_mem hf
    exact hI hp

theorem dropLeft_homogeneous {d : ℕ} (p : MvPolynomial (ι ⊕ τ) K) (hp : p.IsHomogeneous d) :
    (dropLeft p).IsHomogeneous d := by
  have hg : ∀ i : ι ⊕ τ,
      ((Sum.elim (fun _ : ι => 0) X i) : MvPolynomial τ K).IsHomogeneous 1 := by
    intro i
    cases i with
    | inl i => exact (H K τ 1).zero_mem
    | inr i => exact isHomogeneous_X K i
  simpa [dropLeft] using hp.aeval _ hg


end Froberg.CoordinateFoundation.VariableProjection
