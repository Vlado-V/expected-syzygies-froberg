module

public import ESCtoFroberg.Points
public import Froberg.Statement
public import Mathlib.Algebra.CharZero.Infinite

@[expose] public section

noncomputable section
namespace ESCtoFroberg
open MvPolynomial

/-- The number of monomials in positive-variable polynomial rings. -/
def N (n t : ℕ) : ℕ := (n + t - 1).choose t

/-- The point set has least interpolation degree `d`. -/
def IsInterpolationDegree (n d p : ℕ) : Prop :=
  p ≤ N n d ∧ ∀ j < d, N n j < p

/-- The raw Koszul coefficient at a degree in the chopped range. -/
def choppedRawCoefficient (n d p e : ℕ) : ℤ :=
  Froberg.predictionCoefficient n d (N n d - p) (d + e)

/-- A plateau has occurred by offset `e` precisely when a positive offset no
greater than `e` has raw coefficient at most the number of points. -/
def PlateauReached (n d p e : ℕ) : Prop :=
  ∃ i, 1 ≤ i ∧ i ≤ e ∧ choppedRawCoefficient n d p i ≤ (p : ℤ)

/-- Conjecture 2.2's quotient dimension, including the case of no plateau. -/
def choppedPrediction (n d p e : ℕ) : ℕ := by
  classical
  exact if PlateauReached n d p e then p else (choppedRawCoefficient n d p e).toNat

variable (K : Type*) [Field K]

/-- Generality is a single nonempty principal open in the ordered point chart. -/
def GenericPointProperty (m p : ℕ) (P : PointCoordinates K m p → Prop) : Prop :=
  ∃ D : MvPolynomial (Fin p × Fin m) K,
    (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 → P a

/-- The exact conjectural input of the manuscript: the Hilbert function of
actual degree chops of general point ideals at their least interpolation degree.
The affine chart has dimension `m`, hence the ring has `m+1` variables. -/
def ExpectedSyzygyConjecture : Prop :=
  ∀ m p d : ℕ, 1 ≤ m → 1 ≤ p → 1 ≤ d →
    IsInterpolationDegree (m + 1) d p →
    GenericPointProperty K m p (fun a =>
      DistinctPoints K a ∧ ∀ e : ℕ,
        choppedHilbertFunction K a d (d + e) = choppedPrediction (m + 1) d p e)

/-- Fröberg's predicted quotient dimensions through `2*d`, all on one nonempty
open in the full coefficient space, with all variable and generator counts. -/
def FrobergThrough2d : Prop :=
  ∀ n d : ℕ, 1 ≤ n → 1 ≤ d → ∀ r : ℕ,
    Froberg.GenericHilbertThrough K n d r (2 * d)

/-- Theorem 1.1 is an implication; the Expected Syzygy Conjecture is its sole
mathematical premise beyond a characteristic-zero field. -/
def PaperStatement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    ExpectedSyzygyConjecture K → FrobergThrough2d K

variable {K}

theorem plateauReached_mono {n d p e f : ℕ} (hef : e ≤ f)
    (h : PlateauReached n d p e) : PlateauReached n d p f := by
  obtain ⟨i, hi, hie, hc⟩ := h
  exact ⟨i, hi, hie.trans hef, hc⟩

theorem plateauReached_zero (n d p : ℕ) : ¬PlateauReached n d p 0 := by
  rintro ⟨i, hi, hi0, _⟩
  omega

theorem choppedPrediction_after_plateau {n d p e : ℕ}
    (h : PlateauReached n d p e) : choppedPrediction n d p e = p := by
  simp [choppedPrediction, h]

theorem choppedPrediction_before_plateau {n d p e : ℕ}
    (h : ¬PlateauReached n d p e) :
    choppedPrediction n d p e = (choppedRawCoefficient n d p e).toNat := by
  simp [choppedPrediction, h]

end ESCtoFroberg
