module

public import Froberg.GenericHilbertDimension
public import ESCtoFroberg.Statement

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open MvPolynomial Module

variable {K : Type*} [Field K]

abbrev DegreeExponent (n d : ℕ) := {a : Fin n →₀ ℕ // a.degree = d}

instance degreeExponentFintype (n d : ℕ) : Fintype (DegreeExponent n d) :=
  Fintype.ofEquiv (Sym (Fin n) d) (Froberg.exponentEquiv n d)

theorem card_degreeExponent (n d : ℕ) :
    Fintype.card (DegreeExponent n d) = (n + d - 1).choose d := by
  rw [Fintype.card_congr (Froberg.exponentEquiv n d).symm, Sym.card_sym_eq_choose]
  simp

def pureDegreeExponent {n : ℕ} (j : Fin n) (d : ℕ) : DegreeExponent n d :=
  ⟨Finsupp.single j d, by simp⟩

def shiftedDegreeExponent {n d e : ℕ} (j : Fin n) (he : e ≤ d)
    (a : DegreeExponent n e) : DegreeExponent n d :=
  ⟨Finsupp.single j (d - e) + a.val, by
    simp only [map_add, Finsupp.degree_single, a.property, Nat.sub_add_cancel he]⟩

theorem shiftedDegreeExponent_injective {n d e : ℕ} (j : Fin n) (he : e ≤ d) :
    Function.Injective (shiftedDegreeExponent j he) := by
  intro a b h
  apply Subtype.ext
  exact add_left_cancel (congrArg Subtype.val h)

theorem shiftedDegreeExponent_ne_pure {n d e : ℕ} (j : Fin n) (he : e ≤ d)
    (a : DegreeExponent n e) (ha : a ≠ pureDegreeExponent j e) :
    shiftedDegreeExponent j he a ≠ pureDegreeExponent j d := by
  intro h
  apply ha
  apply shiftedDegreeExponent_injective j he
  rw [h]
  apply Subtype.ext
  change Finsupp.single j d = Finsupp.single j (d - e) + Finsupp.single j e
  rw [← Finsupp.single_add, Nat.sub_add_cancel he]

def exponentForm {n d : ℕ} (a : DegreeExponent n d) : Forms K n d :=
  ⟨monomial a.val 1, isHomogeneous_monomial 1 a.property⟩

theorem exponentForm_linearIndependent (n d : ℕ) :
    LinearIndependent K (exponentForm (K := K) (n := n) (d := d)) := by
  apply LinearIndependent.of_comp (Forms K n d).subtype
  change LinearIndependent K (fun a : DegreeExponent n d => (monomial a.val 1 : Poly K n))
  simpa only [MvPolynomial.coe_basisMonomials, Function.comp_def] using
    (MvPolynomial.basisMonomials (Fin n) K).linearIndependent.comp
      (fun a : DegreeExponent n d => a.val) Subtype.val_injective

/-- A divisor can be chosen either pure in the distinguished variable or with
that exponent below `d-e`. Such divisors survive the omitted monomials. -/
theorem exists_good_degree_divisor {n d e : ℕ} (j : Fin n) (he : e < d)
    (a : Fin n →₀ ℕ) (ha : a.degree = d + e) :
    ∃ b c : Fin n →₀ ℕ, b.degree = d ∧ c.degree = e ∧ b + c = a ∧
      (b = Finsupp.single j d ∨ b j < d - e) := by
  classical
  by_cases hj : d ≤ a j
  · let b := Finsupp.single j d
    have hb : b ≤ a := by
      intro i
      by_cases hi : i = j
      · subst i; simpa [b] using hj
      · simp [b, Finsupp.single_eq_of_ne hi]
    let c := a - b
    have heq : b + c = a := add_tsub_cancel_of_le hb
    have hc : c.degree = e := by
      have ht := congrArg Finsupp.degree heq
      simp only [map_add, b, Finsupp.degree_single, ha] at ht
      omega
    exact ⟨b, c, by simp [b], hc, heq, Or.inl rfl⟩
  · by_cases hje : e ≤ a j
    · let c := Finsupp.single j e
      have hc : c ≤ a := by
        intro i
        by_cases hi : i = j
        · subst i; simpa [c] using hje
        · simp [c, Finsupp.single_eq_of_ne hi]
      let b := a - c
      have heq : b + c = a := tsub_add_cancel_of_le hc
      have hb : b.degree = d := by
        have ht := congrArg Finsupp.degree heq
        simp only [map_add] at ht
        simp [c, ha] at ht
        omega
      refine ⟨b, c, hb, by simp [c], heq, Or.inr ?_⟩
      simp only [b, Finsupp.tsub_apply, c, Finsupp.single_eq_same]
      omega
    · have heq0 : Finsupp.single j (a j) + a.erase j = a := by
        ext i
        by_cases hi : i = j
        · subst i; simp
        · simp [hi, Finsupp.single_eq_of_ne hi]
      have hdeg : (a.erase j).degree + a j = d + e := by
        have h := congrArg Finsupp.degree heq0
        simp only [map_add, Finsupp.degree_single, ha] at h
        omega
      obtain ⟨c', hc', hcdeg⟩ := Finsupp.exists_le_degree_eq (a.erase j) (e - a j) (by omega)
      let c := Finsupp.single j (a j) + c'
      have hc : c ≤ a := by
        rw [← heq0]
        change Finsupp.single j (a j) + c' ≤ Finsupp.single j (a j) + a.erase j
        exact add_le_add (le_refl _) hc'
      have hc0 : c' j = 0 := by
        have h := hc' j
        simpa using h
      have hcdeg' : c.degree = e := by
        simp only [c, map_add, Finsupp.degree_single, hcdeg]
        omega
      let b := a - c
      have heq : b + c = a := tsub_add_cancel_of_le hc
      have hb : b.degree = d := by
        have ht := congrArg Finsupp.degree heq
        simp only [map_add, hcdeg', ha] at ht
        omega
      refine ⟨b, c, hb, hcdeg', heq, Or.inr ?_⟩
      simp [b, c, hc0]
      omega

/-- There are enough nonpure degree-`e` monomials to omit any `p<N_e`. -/
theorem exists_omitted_exponents {n d e p : ℕ} (j : Fin n) (he : e ≤ d)
    (hp : p < (n + e - 1).choose e) :
    ∃ omitted : Fin p ↪ DegreeExponent n d,
      ∀ i, (omitted i).val j ≥ d - e ∧ omitted i ≠ pureDegreeExponent j d := by
  classical
  let U := {a : DegreeExponent n e // a ≠ pureDegreeExponent j e}
  have hc : Fintype.card U = (n + e - 1).choose e - 1 := by
    rw [Fintype.card_subtype_compl, card_degreeExponent]
    simp
  obtain ⟨v : Fin p ↪ U⟩ := Function.Embedding.nonempty_of_card_le (α := Fin p) (β := U) (by
    rw [Fintype.card_fin, hc]
    omega)
  let shift : U ↪ DegreeExponent n d :=
    { toFun := fun a => shiftedDegreeExponent j he a.val
      inj' := fun a b h => Subtype.ext (shiftedDegreeExponent_injective j he h) }
  refine ⟨v.trans shift, ?_⟩
  intro i
  constructor
  · change d - e ≤ (Finsupp.single j (d - e) + (v i).val.val) j
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  · exact shiftedDegreeExponent_ne_pure j he (v i).val (v i).property

/-- An independent tuple of the prescribed codimension generates every target
form when `p<N_e`. -/
theorem exists_surjective_prefix_low_p {n d e p : ℕ} (hn : 0 < n) (he : e < d)
    (hp : p < (n + e - 1).choose e) :
    ∃ q : Fin ((n + d - 1).choose d - p) → Forms K n d,
      LinearIndependent K q ∧ Function.Surjective (Froberg.prefixMultiplication q e) := by
  classical
  let j : Fin n := ⟨0, hn⟩
  obtain ⟨omitted, homitted⟩ := exists_omitted_exponents j he.le hp
  let U := {a : DegreeExponent n d // a ∉ Set.range omitted}
  have hc : Fintype.card U = (n + d - 1).choose d - p := by
    rw [Fintype.card_subtype_compl, card_degreeExponent]
    rw [Fintype.card_range omitted, Fintype.card_fin]
  let φ : Fin ((n + d - 1).choose d - p) ≃ U := (Fintype.equivFinOfCardEq hc).symm
  let q : Fin ((n + d - 1).choose d - p) → Forms K n d :=
    fun i => exponentForm (φ i).val
  have hli : LinearIndependent K q :=
    (exponentForm_linearIndependent n d).comp (fun i => (φ i).val)
      (Subtype.val_injective.comp φ.injective)
  refine ⟨q, hli, ?_⟩
  have hmul : Forms K n (d + e) ≤ Froberg.familySpace q * Forms K n e := by
    rw [Forms, Froberg.Forms, homogeneousSubmodule_eq_finsupp_supported]
    change restrictSupport K {a : Fin n →₀ ℕ | a.degree = d + e} ≤ _
    rw [restrictSupport_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, c, hb, hc, heq, hgood⟩ := exists_good_degree_divisor j he a ha
    have hbU : (⟨b, hb⟩ : DegreeExponent n d) ∉ Set.range omitted := by
      rintro ⟨i, hi⟩
      rcases homitted i with ⟨hole, hneq⟩
      rcases hgood with hbpure | hblt
      · apply hneq
        rw [hi]
        exact Subtype.ext hbpure
      · have heval := congrArg (fun v : DegreeExponent n d => v.val j) hi
        change (omitted i).val j = b j at heval
        omega
    obtain ⟨i, hi⟩ := φ.surjective ⟨⟨b, hb⟩, hbU⟩
    have hqb : (q i).val = monomial b 1 := by
      change monomial (φ i).val.val 1 = _
      rw [hi]
    have hbmem : (monomial b 1 : Poly K n) ∈ Froberg.familySpace q := by
      rw [← hqb]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hcmem : (monomial c 1 : Poly K n) ∈ Forms K n e :=
      isHomogeneous_monomial 1 hc
    have hprod := Submodule.mul_mem_mul hbmem hcmem
    rw [monomial_mul_monomial, one_mul, heq] at hprod
    exact hprod
  intro f
  have hf : f.val ∈ Froberg.familySpace q * Forms K n e := hmul f.property
  rw [← Froberg.range_ambient_prefixMultiplication q] at hf
  obtain ⟨a, ha⟩ := hf
  exact ⟨a, Subtype.ext ha⟩

/-- The actual generic Hilbert dimension vanishes in the low-point-count case. -/
theorem genericHilbertDimension_low_p_eq_zero {n d e p : ℕ} (hn : 0 < n) (he : e < d)
    (hp : p < (n + e - 1).choose e) :
    Froberg.genericHilbertDimension K n d ((n + d - 1).choose d - p) (d + e) = 0 := by
  obtain ⟨q, hq, hsurj⟩ := exists_surjective_prefix_low_p (K := K) hn he hp
  let a := Froberg.coefficientCoordinates q
  have hqeq : Froberg.coefficientForms K n d ((n + d - 1).choose d - p) a = q :=
    (Froberg.coefficientCoordinates (K := K) (n := n) (d := d)
      (r := (n + d - 1).choose d - p)).symm_apply_apply q
  have hzero := Froberg.prefix_hilbert_of_surjective hn q hsurj
  have hle := Froberg.genericHilbertDimension_le K n d ((n + d - 1).choose d - p) (d + e) a
  change _ ≤ Froberg.hilbertFunction (Froberg.familySpace
    (Froberg.coefficientForms K n d ((n + d - 1).choose d - p) a)) (d + e) at hle
  rw [hqeq, hzero] at hle
  omega

end ESCtoFroberg
