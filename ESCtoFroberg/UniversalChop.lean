module

public import ESCtoFroberg.GenericTransfer

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open Module MvPolynomial
open GenericTransfer

private theorem span_family_smul_eq {F V ι : Type*} [Field F]
    [AddCommGroup V] [Module F V] (q : ι → V) (c : F) (hc : c ≠ 0) :
    Submodule.span F (Set.range (c • q)) = Submodule.span F (Set.range q) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have h := Submodule.smul_mem (Submodule.span F (Set.range (c • q))) c⁻¹
      (Submodule.subset_span (s := Set.range (c • q)) ⟨i, rfl⟩)
    simpa [inv_smul_smul₀ hc] using h

private theorem familySpace_eq_pointDegreeSpace {F : Type*} [Field F]
    {m p d r : ℕ} (a : PointCoordinates F m p) (q : Fin r → Forms F (m + 1) d)
    (hspan : Submodule.span F (Set.range q) = pointDegreePiece F a d) :
    Froberg.familySpace q = pointDegreeSpace F a d := by
  have h := congrArg (fun W : Submodule F (Forms F (m + 1) d) =>
    W.map (Forms F (m + 1) d).subtype) hspan
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h

/-- An actual universal basis of the degree-d vanishing forms specializes to
generators of the actual chop, with its degree-d+e Hilbert value preserved. -/
theorem universal_basis_choppedHilbert_principalOpen
    {K : Type*} [Field K] [Infinite K] {m p d r : ℕ}
    (q : Fin r → Forms (GenericPointField K m p) (m + 1) d)
    (hspan : Submodule.span (GenericPointField K m p) (Set.range q) =
      pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d)
    (e : ℕ) :
    ∃ E : GenericPointRing K m p,
      (∃ a : PointCoordinates K m p, eval a E ≠ 0) ∧
      ∀ a, eval a E ≠ 0 → choppedHilbertFunction K a d (d + e) =
        choppedHilbertFunction (GenericPointField K m p)
          (genericPointCoordinates K m p) d (d + e) := by
  classical
  let R := GenericPointField K m p
  let η := algebraMap (GenericPointRing K m p) R
  have hvanish : ∀ i j, eval (chartPoint R (genericPointCoordinates K m p) j)
      (q i).val = 0 := by
    intro i
    exact (mem_pointDegreePiece _ _).mp (hspan ▸ Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨D, hD, Q, hQ, hmap, hmember⟩ :=
    generic_vanishing_family_clear_denominators q hvanish
  have hDη : η D ≠ 0 := fun hz => hD
    (IsFractionRing.injective (GenericPointRing K m p) R (hz.trans (map_zero η).symm))
  have hfamily : mappedForms Q hQ η = η D • q := by
    funext i
    apply Subtype.ext
    simpa [mappedForms, MvPolynomial.smul_eq_C_mul] using hmap i
  have hspanη : Submodule.span R (Set.range (mappedForms Q hQ η)) =
      pointDegreePiece R (genericPointCoordinates K m p) d := by
    rw [hfamily, span_family_smul_eq q (η D) hDη]
    exact hspan
  obtain ⟨E₁, hE₁, hgen⟩ := polynomialMatrix_rank_principalOpen (F := R)
    (homogeneousCoefficientMatrix (m + 1) d Q)
  obtain ⟨E₂, hE₂, hpoint⟩ := universal_pointHilbert_principalOpen (K := K) m p d
  obtain ⟨E₃, hE₃, hmul⟩ := polynomialMatrix_rank_principalOpen (F := R)
    (homogeneousMultiplicationMatrix (d := d) Q e)
  obtain ⟨a₁₂, ha₁, ha₂⟩ := Froberg.principal_opens_intersect hE₁ hE₂
  have hE₁₂ : ∃ a : PointCoordinates K m p, eval a (E₁ * E₂) ≠ 0 :=
    ⟨a₁₂, by simpa only [map_mul] using mul_ne_zero ha₁ ha₂⟩
  obtain ⟨a₁₂₃, ha₁₂, ha₃⟩ := Froberg.principal_opens_intersect hE₁₂ hE₃
  refine ⟨(E₁ * E₂) * E₃, ⟨a₁₂₃, by
    simpa only [map_mul] using mul_ne_zero ha₁₂ ha₃⟩, ?_⟩
  intro a ha
  have ha' := mul_ne_zero_iff.mp (show eval a (E₁ * E₂) * eval a E₃ ≠ 0 by
    simpa only [map_mul] using ha)
  have ha'' := mul_ne_zero_iff.mp (show eval a E₁ * eval a E₂ ≠ 0 by
    simpa only [map_mul] using ha'.1)
  have hspanK : Submodule.span K (Set.range (mappedForms Q hQ (eval a))) =
      pointDegreePiece K a d := by
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact hmember a i
    · have hrank := hgen a ha''.1
      rw [homogeneousCoefficientMatrix_rank Q hQ (eval a),
        homogeneousCoefficientMatrix_rank Q hQ η, hspanη] at hrank
      rw [hrank, pointDegreePiece_finrank, pointDegreePiece_finrank, hpoint a ha''.2]
  have hspaceK := familySpace_eq_pointDegreeSpace a (mappedForms Q hQ (eval a)) hspanK
  have hspaceR := familySpace_eq_pointDegreeSpace (genericPointCoordinates K m p) q hspan
  have hrank := hmul a ha'.2
  rw [homogeneousMultiplicationMatrix_rank Q hQ e (eval a),
    homogeneousMultiplicationMatrix_rank Q hQ e η, hfamily] at hrank
  have hK := Froberg.prefix_hilbert_add_rank (e := e) (show 0 < m + 1 by omega)
    (mappedForms Q hQ (eval a))
  have hR := Froberg.prefix_hilbert_add_rank (e := e) (show 0 < m + 1 by omega)
    (η D • q)
  rw [familySpace_smul_eq q (η D) hDη, hspaceR] at hR
  rw [hspaceK, hrank] at hK
  exact Nat.add_right_cancel (hK.trans hR.symm)

/-- Every degree of the actual universal chop is the Hilbert value of the
actual K-point chop throughout a nonempty principal open. -/
theorem universal_choppedHilbert_principalOpen
    {K : Type*} [Field K] [Infinite K] (m p d e : ℕ) :
    ∃ D : GenericPointRing K m p,
      (∃ a : PointCoordinates K m p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → choppedHilbertFunction K a d (d + e) =
        choppedHilbertFunction (GenericPointField K m p)
          (genericPointCoordinates K m p) d (d + e) := by
  obtain ⟨q, -, hspan⟩ := exists_subspace_basis
    (pointDegreePiece (GenericPointField K m p) (genericPointCoordinates K m p) d)
  exact universal_basis_choppedHilbert_principalOpen q hspan e

/-- A generic K-point Hilbert equality is therefore an equality at the actual
universal point configuration, without assuming the conjecture over a larger field. -/
theorem genericPoint_choppedHF_transfer
    {K : Type*} [Field K] [Infinite K] {m p d e c : ℕ}
    (h : GenericPointProperty K m p (fun a => choppedHilbertFunction K a d (d + e) = c)) :
    choppedHilbertFunction (GenericPointField K m p)
      (genericPointCoordinates K m p) d (d + e) = c := by
  obtain ⟨D, hD, hgeneric⟩ := universal_choppedHilbert_principalOpen (K := K) m p d e
  obtain ⟨E, hE, hvalue⟩ := h
  obtain ⟨a, haD, haE⟩ := Froberg.principal_opens_intersect hD hE
  exact (hgeneric a haD).symm.trans (hvalue a haE)

end ESCtoFroberg
