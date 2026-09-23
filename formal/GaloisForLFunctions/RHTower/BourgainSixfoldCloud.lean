/-
# Bourgain's six-fold first-spacing cloud

Section 3 of Bourgain's proof applies the double large sieve after taking the
sixth power of a short exponential sum.  Its frequency cloud is the six-fold
sum of

  `h ↦ (h, h², h^(3/2), h^(1/2))`.

This file gives that construction an exact finite Lean representation.  It
proves the sixth-power expansion, the unit-modulus law for every character,
and the elementary universal bound for the associated near-pair count.  No
spacing or decoupling estimate is assumed.
-/
import GaloisForLFunctions.RHTower.BourgainSpacingExponentArithmetic
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Ambient coordinate space for Bourgain's first-spacing problem. -/
abbrev BourgainPhaseSpace := Fin 4 → ℝ

/-- Dot product written explicitly, to keep the spacing coordinates visible. -/
def bourgainDot (x y : BourgainPhaseSpace) : ℝ :=
  ∑ j : Fin 4, x j * y j

/-- The curve `(h,h²,h^(3/2),h^(1/2))` in Bourgain's equation (3.7). -/
def bourgainMomentCurve (h : ℕ) : BourgainPhaseSpace :=
  ![(h : ℝ), (h : ℝ) ^ (2 : ℕ),
    (h : ℝ) ^ (3 / 2 : ℝ), (h : ℝ) ^ (1 / 2 : ℝ)]

/-- Standard additive character `e(x·y) = exp(2πi x·y)`. -/
def bourgainAdditiveCharacter
    (x y : BourgainPhaseSpace) : ℂ :=
  Complex.exp
    (2 * (Real.pi : ℂ) * Complex.I * (bourgainDot x y : ℂ))

/-- Every phase in Bourgain's finite exponential sums is unimodular. -/
@[simp] theorem norm_bourgainAdditiveCharacter
    (x y : BourgainPhaseSpace) :
    ‖bourgainAdditiveCharacter x y‖ = 1 := by
  rw [bourgainAdditiveCharacter, Complex.norm_exp]
  have hre :
      (2 * (Real.pi : ℂ) * Complex.I *
        (bourgainDot x y : ℂ)).re = 0 := by
    simp
  rw [hre, Real.exp_zero]

/-- Dot product commutes with a finite sum in its second variable. -/
theorem bourgainDot_sum
    {ι : Type*} [Fintype ι] (x : BourgainPhaseSpace)
    (y : ι → BourgainPhaseSpace) :
    bourgainDot x (∑ i, y i) = ∑ i, bourgainDot x (y i) := by
  simp only [bourgainDot, Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Additive character of a finite vector sum is the product of the
characters. -/
theorem bourgainAdditiveCharacter_sum
    {ι : Type*} [Fintype ι] (x : BourgainPhaseSpace)
    (y : ι → BourgainPhaseSpace) :
    bourgainAdditiveCharacter x (∑ i, y i) =
      ∏ i, bourgainAdditiveCharacter x (y i) := by
  rw [bourgainAdditiveCharacter, bourgainDot_sum]
  rw [show
      2 * (Real.pi : ℂ) * Complex.I *
          ((∑ i, bourgainDot x (y i) : ℝ) : ℂ) =
        ∑ i, 2 * (Real.pi : ℂ) * Complex.I *
          (bourgainDot x (y i) : ℂ) by
    push_cast
    rw [Finset.mul_sum]]
  rw [Complex.exp_sum]
  rfl

/-- Positive integer represented by an element of `Fin H`. -/
def bourgainIndex {H : ℕ} (h : Fin H) : ℕ :=
  h.1 + 1

/-- Six-fold frequency vector `y(h)` from Bourgain's equation (3.7). -/
def bourgainSixfoldMoment {H : ℕ}
    (h : Fin 6 → Fin H) : BourgainPhaseSpace :=
  ∑ j : Fin 6, bourgainMomentCurve (bourgainIndex (h j))

/-- Weighted short exponential sum over `1 ≤ h ≤ H`. -/
def bourgainShortCurveSum
    (H : ℕ) (α : Fin H → ℂ) (x : BourgainPhaseSpace) : ℂ :=
  ∑ h : Fin H,
    α h * bourgainAdditiveCharacter x
      (bourgainMomentCurve (bourgainIndex h))

/-- Product weight induced on the sixth convolution. -/
def bourgainSixfoldWeight {H : ℕ}
    (α : Fin H → ℂ) (h : Fin 6 → Fin H) : ℂ :=
  ∏ j : Fin 6, α (h j)

/-- Exact sixth-power convolution identity underlying Bourgain's (3.7). -/
theorem bourgainShortCurveSum_pow_six
    (H : ℕ) (α : Fin H → ℂ) (x : BourgainPhaseSpace) :
    bourgainShortCurveSum H α x ^ (6 : ℕ) =
      ∑ h : Fin 6 → Fin H,
        bourgainSixfoldWeight α h *
          bourgainAdditiveCharacter x (bourgainSixfoldMoment h) := by
  rw [bourgainShortCurveSum, Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro h _
  rw [bourgainSixfoldWeight, bourgainSixfoldMoment,
    bourgainAdditiveCharacter_sum]
  simp only [Finset.prod_mul_distrib]

/-- Twelfth power of the original sum is the squared norm of its six-fold
convolution. -/
theorem norm_bourgainShortCurveSum_pow_twelve
    (H : ℕ) (α : Fin H → ℂ) (x : BourgainPhaseSpace) :
    ‖bourgainShortCurveSum H α x‖ ^ (12 : ℕ) =
      ‖∑ h : Fin 6 → Fin H,
        bourgainSixfoldWeight α h *
          bourgainAdditiveCharacter x (bourgainSixfoldMoment h)‖ ^
            (2 : ℕ) := by
  rw [← bourgainShortCurveSum_pow_six]
  rw [norm_pow]
  ring

/-- Coordinatewise near-pair relation at reciprocal scales `X`. -/
def BourgainNearPair {H : ℕ} (X : BourgainPhaseSpace)
    (h h' : Fin 6 → Fin H) : Prop :=
  ∀ j : Fin 4,
    |bourgainSixfoldMoment h j - bourgainSixfoldMoment h' j| <
      1 / (2 * X j)

/-- First-spacing pair count used in the double-large-sieve step. -/
noncomputable def bourgainFirstSpacingCount
    (H : ℕ) (X : BourgainPhaseSpace) : ℕ := by
  classical
  exact (((Finset.univ : Finset (Fin 6 → Fin H)).product
        (Finset.univ : Finset (Fin 6 → Fin H))).filter
      fun p : (Fin 6 → Fin H) × (Fin 6 → Fin H) =>
        BourgainNearPair X p.1 p.2).card

/-- The near-pair count is bounded by the total number `H^(12 : ℕ)` of ordered
pairs.  This is the unconditional trivial spacing bound and a useful
normalization check for sharper estimates. -/
theorem bourgainFirstSpacingCount_le
    (H : ℕ) (X : BourgainPhaseSpace) :
    bourgainFirstSpacingCount H X ≤ H ^ (12 : ℕ) := by
  classical
  calc
    bourgainFirstSpacingCount H X ≤
        ((Finset.univ : Finset (Fin 6 → Fin H)).product
          (Finset.univ : Finset (Fin 6 → Fin H))).card := by
      exact Finset.card_filter_le _ _
    _ = (H ^ (6 : ℕ)) * (H ^ (6 : ℕ)) := by simp
    _ = H ^ (12 : ℕ) := by
      rw [← pow_add]

end

end RHTower
