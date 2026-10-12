module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.Algebra.TrivSqZeroExt.Basic

@[expose] public section

namespace ESCtoFroberg

variable {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
variable (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
  [Algebra K F] [IsScalarTower K A F]

/-- The first order Taylor map associated with a derivation. -/
def derivationJet (D : Derivation K A A) : A →ₐ[K] TrivSqZeroExt F F where
  toFun a := ⟨algebraMap A F a, algebraMap A F (D a)⟩
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · change algebraMap A F (a + b) = algebraMap A F a + algebraMap A F b
      simp
    · change algebraMap A F (D (a + b)) = algebraMap A F (D a) + algebraMap A F (D b)
      simp
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · change algebraMap A F (a * b) = algebraMap A F a * algebraMap A F b
      simp
    · change algebraMap A F (D (a * b)) =
        algebraMap A F a • algebraMap A F (D b) +
          (MulOpposite.op (algebraMap A F b)) • algebraMap A F (D a)
      simp [D.leibniz, smul_eq_mul, mul_comm]
  commutes' k := by
    apply TrivSqZeroExt.ext
    · simp [IsScalarTower.algebraMap_apply K A F,
        TrivSqZeroExt.algebraMap_eq_inl']
    · simp [TrivSqZeroExt.algebraMap_eq_inl']

omit [IsDomain A] [IsFractionRing A F] in
@[simp] theorem derivationJet_fst (D : Derivation K A A) (a : A) :
    (derivationJet F D a).fst = algebraMap A F a := rfl

omit [IsDomain A] [IsFractionRing A F] in
@[simp] theorem derivationJet_snd (D : Derivation K A A) (a : A) :
    (derivationJet F D a).snd = algebraMap A F (D a) := rfl

omit [IsDomain A] in
theorem derivationJet_unit (D : Derivation K A A) (a : nonZeroDivisors A) :
    IsUnit (derivationJet F D a) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, derivationJet_fst]
  exact IsLocalization.map_units F a

/-- The Taylor map extends uniquely to the fraction field. -/
noncomputable def fractionJet (D : Derivation K A A) : F →ₐ[K] TrivSqZeroExt F F :=
  IsLocalization.liftAlgHom (derivationJet_unit F D)

omit [IsDomain A] in
@[simp] theorem fractionJet_algebraMap (D : Derivation K A A) (a : A) :
    fractionJet F D (algebraMap A F a) = derivationJet F D a := by
  exact IsLocalization.lift_eq (S := F) (derivationJet_unit F D) a

omit [IsDomain A] in
@[simp] theorem fractionJet_fst (D : Derivation K A A) (x : F) :
    (fractionJet F D x).fst = x := by
  have h : (TrivSqZeroExt.fstHom K F F).comp (fractionJet F D) = AlgHom.id K F := by
    apply IsLocalization.algHom_ext (nonZeroDivisors A)
    ext a
    change (fractionJet F D (algebraMap A F a)).fst = algebraMap A F a
    simp
  exact congrArg (fun f : F →ₐ[K] F => f x) h

/-- Extension of a derivation on a domain to its field of fractions. -/
noncomputable def fractionDerivation (D : Derivation K A A) : Derivation K F F where
  toLinearMap := ((TrivSqZeroExt.sndHom F F).restrictScalars K).comp
    (fractionJet F D).toLinearMap
  map_one_eq_zero' := by simp
  leibniz' x y := by
    change (fractionJet F D (x * y)).snd =
      x • (fractionJet F D y).snd + y • (fractionJet F D x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul]
    simp [smul_eq_mul, mul_comm]

@[simp] theorem fractionDerivation_algebraMap (D : Derivation K A A) (a : A) :
    fractionDerivation F D (algebraMap A F a) = algebraMap A F (D a) := by
  change (fractionJet F D (algebraMap A F a)).snd = _
  simp

/-- The quotient rule for the extension. -/
theorem fractionDerivation_div (D : Derivation K A A) (a b : A) :
    fractionDerivation F D (algebraMap A F a / algebraMap A F b) =
      (algebraMap A F b)⁻¹ ^ 2 *
        (algebraMap A F b * algebraMap A F (D a) -
          algebraMap A F a * algebraMap A F (D b)) := by
  rw [(fractionDerivation F D).leibniz_div]
  simp [smul_eq_mul]

/-- A derivation on the fraction field is determined by its values on the domain. -/
theorem fractionDerivation_unique (D : Derivation K A A) (E : Derivation K F F)
    (hE : ∀ a : A, E (algebraMap A F a) = algebraMap A F (D a)) :
    E = fractionDerivation F D := by
  ext x
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A x
  rw [E.leibniz_div, (fractionDerivation F D).leibniz_div]
  simp [hE]

end ESCtoFroberg
