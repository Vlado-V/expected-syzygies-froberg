module

public import ESCtoFroberg.EndpointCriterion
public import ESCtoFroberg.Points

@[expose] public section

noncomputable section
namespace ESCtoFroberg

open Froberg Module MvPolynomial

variable {K : Type*} [Field K] [CharZero K] {n d r p : ℕ}

omit [CharZero K] in
/-- Removing exactly the constant Koszul kernel identifies evaluation rank with endpoint homology. -/
theorem endpointEvaluationImage_finrank_eq_homology
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q)
    (z : Fin p → Fin n → K)
    (hker : (endpointSyzygyEvaluation q z).ker = incomingInKernel q) :
    finrank K (endpointEvaluationImage q z) = finrank K (EndpointHomology q) := by
  let f : (endpointMultiplication q).ker →ₗ[K] (Fin p → Fin r → K) := endpointSyzygyEvaluation q z
  have hr := LinearMap.finrank_range_add_finrank_ker (K := K) (V := (endpointMultiplication q).ker) (V₂ := Fin p → Fin r → K) f
  change finrank K (endpointEvaluationImage q z) + finrank K (endpointSyzygyEvaluation q z).ker = finrank K (endpointMultiplication q).ker at hr
  rw [hker, finrank_incomingInKernel q hq] at hr
  have hh := homology_add_pairs q hq
  exact Nat.add_right_cancel (hr.trans hh.symm)

omit [CharZero K] in
/-- At a point-ideal plateau, injective homology evaluation gives the exact endpoint image dimension. -/
theorem endpointEvaluationImage_euler
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q) (hn : 0 < n)
    (z : Fin p → Fin n → K)
    (hker : (endpointSyzygyEvaluation q z).ker = incomingInKernel q)
    (hcoker : finrank K (EndpointQuotient K n d
      (Submodule.span K (Set.range (fun i => (q i).val)))) = p) :
    (finrank K (endpointEvaluationImage q z) : ℤ) = (p : ℤ) - euler n d r := by
  have h := endpoint_euler_identity hn q hq
  rw [hcoker, ← endpointEvaluationImage_finrank_eq_homology q hq z hker] at h
  omega

omit [CharZero K] in
/-- The nonpositive endpoint count supplies enough independent point evaluations to deform away the plateau. -/
theorem points_le_endpointEvaluationImage_of_euler_nonpositive
    (q : Fin r → Forms K n d) (hq : LinearIndependent K q) (hn : 0 < n)
    (z : Fin p → Fin n → K)
    (hker : (endpointSyzygyEvaluation q z).ker = incomingInKernel q)
    (hcoker : finrank K (EndpointQuotient K n d
      (Submodule.span K (Set.range (fun i => (q i).val)))) = p)
    (hc : euler n d r ≤ 0) :
    p ≤ finrank K (endpointEvaluationImage q z) := by
  have h := endpointEvaluationImage_euler q hq hn z hker hcoker
  omega

omit [CharZero K] in
/-- Nonzero image vectors supported at distinct points are independent. -/
theorem points_le_endpointEvaluationImage_of_separated_syzygies
    (q : Fin r → Forms K n d) (z : Fin p → Fin n → K)
    (h : ∀ a : Fin p, ∃ b : Fin r → Forms K n d,
      endpointMultiplication q b = 0 ∧
      (∀ c, c ≠ a → ∀ i, MvPolynomial.eval (z c) (b i).val = 0) ∧
      (∃ i, MvPolynomial.eval (z a) (b i).val ≠ 0)) :
    p ≤ finrank K (endpointEvaluationImage q z) := by
  classical
  choose b hb hsupport hnonzero using h
  choose coord hcoord using hnonzero
  let v : Fin p → endpointEvaluationImage q z := fun a =>
    ⟨endpointCoefficientEvaluation z (b a), ⟨⟨b a,hb a⟩,rfl⟩⟩
  have hlin : LinearIndependent K v := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc a
    have hz := congrArg (fun w : endpointEvaluationImage q z => w.val a (coord a)) hc
    have hsum : (∑ j, c j * MvPolynomial.eval (z a) (b j (coord a)).val) =
        c a * MvPolynomial.eval (z a) (b a (coord a)).val := by
      apply Finset.sum_eq_single a
      · intro j hj hja
        rw [hsupport j a (Ne.symm hja) (coord a), mul_zero]
      · simp
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, Submodule.coe_zero, Pi.zero_apply, v, endpointCoefficientEvaluation] at hz
    change (∑ j, c j * MvPolynomial.eval (z a) (b j (coord a)).val) = 0 at hz
    rw [hsum] at hz
    exact (mul_eq_zero.mp hz).resolve_right (hcoord a)
  simpa using hlin.fintype_card_le_finrank

/-- Multiplication by a variable sends degree `d-1` forms into degree `d`. -/
def variableTimesForm (hd : 0 < d) (g : Forms K n (d - 1)) (i : Fin n) : Forms K n d :=
  ⟨X i * g.val, by
    change (X i * g.val).IsHomogeneous d
    have h := (isHomogeneous_X K i).mul g.property
    have hdeg : 1 + (d - 1) = d := by omega
    simpa only [hdeg] using h⟩

/-- The coefficient syzygy of two variable multiples of a lower-degree point equation. -/
def pencilSyzygy (hd : 0 < d) (h : Forms K n (d - 1))
    (i j : Fin n) (ci cj : Fin r → K) : Fin r → Forms K n d :=
  fun a => cj a • variableTimesForm hd h i - ci a • variableTimesForm hd h j

omit [CharZero K] in
theorem pencilSyzygy_is_syzygy
    (q : Fin r → Forms K n d) (hd : 0 < d) (g h : Forms K n (d - 1))
    (i j : Fin n) (ci cj : Fin r → K)
    (hci : (∑ a, ci a • (q a).val) = X i * g.val)
    (hcj : (∑ a, cj a • (q a).val) = X j * g.val) :
    endpointMultiplication q (pencilSyzygy hd h i j ci cj) = 0 := by
  classical
  apply Subtype.ext
  rw [endpointMultiplication_val]
  change (∑ a, (q a).val *
    (cj a • (X i * h.val) - ci a • (X j * h.val))) = 0
  simp only [mul_sub, Finset.sum_sub_distrib]
  have hprod (c : Fin r → K) (f : Poly K n) :
      (∑ a, (q a).val * (c a • f)) = (∑ a, c a • (q a).val) * f := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [mul_smul_comm, smul_mul_assoc]
  rw [hprod, hprod, hci, hcj]
  ring

omit [CharZero K] in
theorem pencilSyzygy_evaluation (hd : 0 < d) (h : Forms K n (d - 1))
    (i j : Fin n) (ci cj : Fin r → K) (z : Fin n → K) (a : Fin r) :
    MvPolynomial.eval z (pencilSyzygy hd h i j ci cj a).val =
      MvPolynomial.eval z h.val * (z i * cj a - z j * ci a) := by
  simp [pencilSyzygy, variableTimesForm]
  ring

omit [CharZero K] in
/-- A normalized separator produces a nonzero syzygy evaluation at its chosen point. -/
theorem pencilSyzygy_evaluation_ne_zero
    (q : Fin r → Forms K n d) (hd : 0 < d) (g h : Forms K n (d - 1))
    (hg : g.val ≠ 0) (i j : Fin n) (hij : i ≠ j) (ci cj : Fin r → K)
    (hci : (∑ a, ci a • (q a).val) = X i * g.val)
    (hcj : (∑ a, cj a • (q a).val) = X j * g.val)
    (z : Fin n → K) (hzi : z i ≠ 0) (hz : MvPolynomial.eval z h.val = 1) :
    ∃ a, MvPolynomial.eval z (pencilSyzygy hd h i j ci cj a).val ≠ 0 := by
  classical
  by_contra hnone
  have ha : ∀ a, z i * cj a = z j * ci a := by
    intro a
    have hae := not_exists.mp hnone a
    have he : MvPolynomial.eval z (pencilSyzygy hd h i j ci cj a).val = 0 :=
      not_ne_iff.mp hae
    rw [pencilSyzygy_evaluation, hz, one_mul] at he
    exact sub_eq_zero.mp he
  have hpoly : (z i : K) • (X j * g.val) = (z j : K) • (X i * g.val) := by
    rw [← hci, ← hcj, Finset.smul_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro a ha'
    rw [smul_smul, smul_smul, ha a]
  have hx : (z i : K) • (X j : Poly K n) = (z j : K) • (X i : Poly K n) := by
    apply mul_right_cancel₀ hg
    simpa only [smul_mul_assoc] using hpoly
  have hc := congrArg (fun f : Poly K n => f.coeff (Finsupp.single j 1)) hx
  have hsingle : Finsupp.single i (1 : ℕ) ≠ Finsupp.single j 1 := by
    exact fun he => hij (Finsupp.single_left_injective one_ne_zero he)
  have hzi0 : z i = 0 := by
    simpa [MvPolynomial.coeff_X, hsingle] using hc
  exact hzi hzi0


omit [CharZero K] in
/-- If lower-degree point evaluation is surjective but its source is larger than
its target, point separators produce independent endpoint evaluations, one for
each point. The degree-`d` family need only span the actual point equations. -/
theorem points_le_endpointEvaluationImage_of_small_p {m : ℕ}
    (a : PointCoordinates K m p) (q : Fin r → Forms K (m + 1) d)
    (hm : 1 ≤ m) (hd : 0 < d)
    (hspan : Submodule.span K (Set.range q) = pointDegreePiece K a d)
    (hsurj : Function.Surjective (pointEvaluation K a (d - 1)))
    (hp : p < (m + (d - 1)).choose (d - 1)) :
    p ≤ finrank K (endpointEvaluationImage q (fun j => chartPoint K a j)) := by
  classical
  have hdim : finrank K (Fin p → K) < finrank K (Forms K (m + 1) (d - 1)) := by
    simpa [Module.finrank_pi_fintype, ESCtoFroberg.finrank_forms] using hp
  have hker : (pointEvaluation K a (d - 1)).ker ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨g, hgmem, hg⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hgval : g.val ≠ 0 := fun hv => hg (Subtype.ext hv)
  have hgzero : ∀ c, MvPolynomial.eval (chartPoint K a c) g.val = 0 :=
    (mem_pointDegreePiece a g).mp hgmem
  have hmult (v : Fin (m + 1)) : variableTimesForm hd g v ∈ pointDegreePiece K a d := by
    apply (mem_pointDegreePiece a _).mpr
    intro c
    simp [variableTimesForm, hgzero c]
  let i : Fin (m + 1) := Fin.last m
  let j : Fin (m + 1) := 0
  have hij : i ≠ j := by
    intro hh
    have hv := congrArg Fin.val hh
    simp only [i, j, Fin.val_last, Fin.val_zero] at hv
    omega
  obtain ⟨ci, hci⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (hspan.symm ▸ hmult i)
  obtain ⟨cj, hcj⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp
    (hspan.symm ▸ hmult j)
  have hciVal : (∑ b, ci b • (q b).val) = X i * g.val := by
    have hv := congrArg Subtype.val hci
    simpa only [Submodule.coe_sum, Submodule.coe_smul, variableTimesForm] using hv
  have hcjVal : (∑ b, cj b • (q b).val) = X j * g.val := by
    have hv := congrArg Subtype.val hcj
    simpa only [Submodule.coe_sum, Submodule.coe_smul, variableTimesForm] using hv
  apply points_le_endpointEvaluationImage_of_separated_syzygies
  intro c
  obtain ⟨h, hh⟩ := hsurj (Pi.single c 1)
  have hchosen : MvPolynomial.eval (chartPoint K a c) h.val = 1 := by
    have he := congrFun hh c
    simpa only [pointEvaluation_apply, Pi.single_eq_same] using he
  have hother : ∀ c', c' ≠ c → MvPolynomial.eval (chartPoint K a c') h.val = 0 := by
    intro c' hc'
    have he := congrFun hh c'
    simpa only [pointEvaluation_apply, Pi.single_eq_of_ne hc'] using he
  refine ⟨pencilSyzygy hd h i j ci cj,
    pencilSyzygy_is_syzygy q hd g h i j ci cj hciVal hcjVal, ?_, ?_⟩
  · intro c' hc' b
    rw [pencilSyzygy_evaluation, hother c' hc', zero_mul]
  · exact pencilSyzygy_evaluation_ne_zero q hd g h hgval i j hij ci cj hciVal hcjVal
      (chartPoint K a c) (by simp [i]) hchosen

end ESCtoFroberg
