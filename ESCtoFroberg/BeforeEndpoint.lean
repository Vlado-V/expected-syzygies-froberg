module

public import ESCtoFroberg.GeneralPoints
public import ESCtoFroberg.SyzygyEvaluation

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open Module MvPolynomial
variable {K : Type*} [Field K]

/-- Full-dimensional evaluation has zero kernel. -/
theorem pointEvaluation_injective_of_hilbert_eq {m p e : ℕ}
    (a : PointCoordinates K m p) (h : pointHilbertFunction K a e = (m+e).choose e) :
    Function.Injective (pointEvaluation K a e) := by
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.finrank_eq_zero.mp
  change finrank K (pointDegreePiece K a e) = 0
  rw [pointDegreePiece_finrank, h, Nat.sub_self]

/-- A point configuration with full interpolation in degree d has exactly
N_d−p independent degree-d equations generating its chop. -/
theorem exists_degree_generators_of_hilbert_eq {m p d : ℕ}
    (a : PointCoordinates K m p) (h : pointHilbertFunction K a d = p) :
    ∃ q : Fin ((m+d).choose d - p) → Forms K (m+1) d,
      LinearIndependent K q ∧ Froberg.familySpace q = pointDegreeSpace K a d := by
  have hdim : finrank K (pointDegreePiece K a d) = (m+d).choose d - p := by
    rw [pointDegreePiece_finrank,h]
  obtain ⟨q,hli,hspan⟩ := exists_degree_generators a d
  let E : Fin ((m+d).choose d-p) ≃ Fin (finrank K (pointDegreePiece K a d)) :=
    finCongr hdim.symm
  refine ⟨q ∘ E, hli.comp E E.injective, ?_⟩
  have heq : Set.range (fun i => (q (E i)).val) = Set.range (fun i => (q i).val) := by
    rw [←Function.comp_def (f := fun i => (q i).val) (g := E),Set.range_comp,
      E.surjective.range_eq,Set.image_univ]
  simpa only [Froberg.familySpace,Function.comp_apply,heq] using hspan

namespace Deformation
variable {m p d e r : ℕ}

/-- All coefficient evaluations of an actual syzygy, grouped by marked point. -/
def syzygyEvaluation (a : PointCoordinates K m p) (q : Fin r → Forms K (m+1) d)
    (e : ℕ) : (Froberg.prefixMultiplication q e).ker →ₗ[K] (Fin p → Fin r → K) :=
  LinearMap.pi (fun j => syzygyBlockEvaluation a q e j)

@[simp] theorem syzygyEvaluation_apply (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m+1) d) (z : (Froberg.prefixMultiplication q e).ker)
    (j : Fin p) (i : Fin r) :
    syzygyEvaluation a q e z j i = pointEvaluation K a e (z.val i) j := rfl

/-- If degree-e point evaluation is injective, no nonzero coefficient syzygy
can vanish at every point. -/
theorem syzygyEvaluation_injective (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m+1) d)
    (heval : Function.Injective (pointEvaluation K a e)) :
    Function.Injective (syzygyEvaluation a q e) := by
  intro z w hzw
  apply Subtype.ext
  funext i
  apply heval
  funext j
  exact congrFun (congrFun hzw j) i

/-- The full coefficient-evaluation rank equals the actual syzygy dimension. -/
theorem syzygyEvaluation_finrank_range (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m+1) d)
    (heval : Function.Injective (pointEvaluation K a e)) :
    finrank K (syzygyEvaluation a q e).range =
      finrank K (Froberg.prefixMultiplication q e).ker :=
  LinearMap.finrank_range_of_inj (syzygyEvaluation_injective a q heval)

/-- The maximal point Hilbert function supplies the injectivity hypothesis
needed by the coefficient deformation argument. -/
theorem syzygyEvaluation_injective_of_hilbert_eq (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m+1) d)
    (heval : pointHilbertFunction K a e = (m+e).choose e) :
    Function.Injective (syzygyEvaluation a q e) :=
  syzygyEvaluation_injective a q (pointEvaluation_injective_of_hilbert_eq a heval)

/-- When the chop quotient has exactly the point count, multiplication fills
all degree-(d+e) equations of the actual point ideal. -/
theorem prefixMultiplication_range_eq_pointKernel (a : PointCoordinates K m p)
    (q : Fin r → Forms K (m+1) d)
    (hspace : Froberg.familySpace q = pointDegreeSpace K a d)
    (heval : Function.Surjective (pointEvaluation K a (d+e)))
    (hH : choppedHilbertFunction K a d (d+e) = p) :
    (Froberg.prefixMultiplication q e).range = (pointEvaluation K a (d+e)).ker := by
  have hvan (i : Fin r) (j : Fin p) : eval (chartPoint K a j) (q i).val = 0 := by
    have hmem : (q i).val ∈ pointDegreeSpace K a d :=
      hspace ▸ Submodule.subset_span ⟨i,rfl⟩
    exact ((mem_pointDegreeSpace a _).mp hmem).2 j
  have hle : (Froberg.prefixMultiplication q e).range ≤ (pointEvaluation K a (d+e)).ker := by
    rintro f ⟨b,rfl⟩
    apply LinearMap.mem_ker.mpr
    funext j
    simp [pointEvaluation_apply, Froberg.prefixMultiplication_val, hvan]
  apply Submodule.eq_of_le_of_finrank_eq hle
  have h₁ := Froberg.prefix_hilbert_add_rank (e := e) (show 0 < m+1 by omega) q
  have hh : Froberg.hilbertFunction (Froberg.familySpace q) (d+e) = p := by
    rw [hspace]
    exact hH
  rw [hh, show m+1+(d+e)-1 = m+(d+e) by omega] at h₁
  have h₂ := (pointEvaluation K a (d+e)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr heval,finrank_top,Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin, finrank_forms] at h₂
  exact Nat.add_left_cancel (h₁.trans h₂.symm)

end Deformation
end ESCtoFroberg
