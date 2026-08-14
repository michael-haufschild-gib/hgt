import GaloisForLFunctions.RHTower.HedenmalmExteriorSourceNativePrimeWardClock
import GaloisForLFunctions.RHTower.HedenmalmSoninFiniteDivisorAnalyticGaugeFlexibility
import GaloisForLFunctions.RHTower.XiGuinandWeilFiniteHermiteCriterion
import GaloisForLFunctions.RHTower.XiGuinandWeilSpectralRectangle
import GaloisForLFunctions.RHTower.XiWeilCauchyCoreMultiplicity
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.LinearAlgebra.Lagrange

/-!
# Coefficient-faithful prime--Gamma source for the exterior clock packet

The source-native exterior projector uses bounded clocks which are not holomorphic functions of
the centered spectral coordinate.  This prevents inserting them directly as weights in the
Guinand--Weil contour.  On a finite Xi rectangle, however, the complete clocked coefficient data
has a unique degree-bounded Lagrange lift.  The lift is entire and agrees at every distinct Xi zero;
analytic multiplicity then reproduces every divisor copy automatically.

This module applies that observation to all four entries of the oriented exterior determinant.
For every admissible rectangle and every clock-depth triple, the resulting four continued
prime--Gamma contours are exactly the full multiplicity-copy exterior determinant.  No clock,
prime label, feature orientation, or divisor multiplicity is discarded.
-/

open Complex Filter intervalIntegral Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Arbitrary finite coefficient data as an exact source contour -/

/-- Entire polynomial lift of arbitrary coefficient data on a finite centered spectrum. -/
def xiFiniteCoefficientInterpolant
    (S : Finset ℂ) (target : ℂ → ℂ) : Polynomial ℂ :=
  Lagrange.interpolate S id target

theorem analyticOnNhd_xiFiniteCoefficientInterpolant
    (S : Finset ℂ) (target : ℂ → ℂ) :
    AnalyticOnNhd ℂ
      (fun z => (xiFiniteCoefficientInterpolant S target).eval z)
      Set.univ := by
  exact AnalyticOnNhd.eval_polynomial _

@[simp]
theorem xiFiniteCoefficientInterpolant_eval
    {S : Finset ℂ} {target : ℂ → ℂ} {z : ℂ} (hz : z ∈ S) :
    (xiFiniteCoefficientInterpolant S target).eval z = target z := by
  exact Lagrange.eval_interpolate_at_node target
    Function.injective_id.injOn hz

/-- Normalized continued prime--Gamma contour carrying arbitrary finite coefficient data. -/
def normalizedXiFiniteCoefficientSourceContour
    (z₁ z₂ : ℂ) (target : ℂ → ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    rectIntegral
      (fun z =>
        (xiFiniteCoefficientInterpolant
          (xiCClosedRectangleZeros z₁ z₂) target).eval z *
          continuedPrimeArchSourceRelativeTrace z)
      z₁ z₂

/-- **Coefficient-faithful finite source law.**  Every prescribed coefficient on every distinct
Xi zero in an admissible rectangle is recovered exactly by one continued prime--Gamma contour;
the contour residue supplies the analytic multiplicity. -/
theorem normalizedXiFiniteCoefficientSourceContour_eq_zeroSum
    {z₁ z₂ : ℂ} (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (target : ℂ → ℂ) :
    normalizedXiFiniteCoefficientSourceContour z₁ z₂ target =
      ∑ w ∈ xiCClosedRectangleZeros z₁ z₂,
        (xiSpectralMultiplicity w : ℂ) * target w := by
  have hcontour :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum
      (analyticOnNhd_xiFiniteCoefficientInterpolant
        (xiCClosedRectangleZeros z₁ z₂) target)
      hre him hbot htop hright hleft
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [normalizedXiFiniteCoefficientSourceContour, hcontour,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  apply Finset.sum_congr rfl
  intro w hw
  rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat
      (mem_xiCClosedRectangleZeros.mp hw).2,
    xiFiniteCoefficientInterpolant_eval hw]

/-! ## Multiplicity-copy rectangles and support rectangles -/

/-- Distinct Xi divisor support points represented in a centered spectral rectangle. -/
def xiDivisorSupportClosedRectangle (z₁ z₂ : ℂ) : Finset XiDivisorSupport :=
  (xiZeroCopyClosedRectangle z₁ z₂).image Sigma.fst

@[simp]
theorem mem_xiDivisorSupportClosedRectangle
    {z₁ z₂ : ℂ} {rho : XiDivisorSupport} :
    rho ∈ xiDivisorSupportClosedRectangle z₁ z₂ ↔
      xiSpectralPointSupport rho ∈
        (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) := by
  constructor
  · intro hrho
    obtain ⟨q, hq, hqrho⟩ := Finset.mem_image.mp hrho
    have hrect := mem_xiZeroCopyClosedRectangle.mp hq
    simpa only [← hqrho, xiSpectralPoint_eq_support] using hrect
  · intro hrect
    apply Finset.mem_image.mpr
    refine ⟨xiDivisorSupportCanonicalCopy rho, ?_, rfl⟩
    exact mem_xiZeroCopyClosedRectangle.mpr hrect

/-- The copied rectangle is the disjoint union of complete multiplicity fibres over its distinct
support points. -/
theorem xiZeroCopyClosedRectangle_eq_biUnion_supportFibers
    (z₁ z₂ : ℂ) :
    xiZeroCopyClosedRectangle z₁ z₂ =
      (xiDivisorSupportClosedRectangle z₁ z₂).biUnion xiZeroCopyFiber := by
  classical
  ext q
  constructor
  · intro hq
    apply Finset.mem_biUnion.mpr
    refine ⟨q.1, ?_, ?_⟩
    · rw [mem_xiDivisorSupportClosedRectangle]
      simpa only [← xiSpectralPoint_eq_support] using
        (mem_xiZeroCopyClosedRectangle.mp hq)
    · exact mem_xiZeroCopyFiber.mpr rfl
  · intro hq
    obtain ⟨rho, hrho, hqrho⟩ := Finset.mem_biUnion.mp hq
    rw [mem_xiDivisorSupportClosedRectangle] at hrho
    apply mem_xiZeroCopyClosedRectangle.mpr
    simpa only [xiSpectralPoint_eq_support, mem_xiZeroCopyFiber.mp hqrho] using hrho

/-- Exact regrouping of a rectangle-copy sum by distinct support and analytic multiplicity. -/
theorem sum_xiZeroCopyClosedRectangle_eq_supportMultiplicitySum
    (target : XiDivisorSupport → ℂ) (z₁ z₂ : ℂ) :
    ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂, target q.1 =
      ∑ rho ∈ xiDivisorSupportClosedRectangle z₁ z₂,
        (xiSupportMultiplicity rho : ℂ) * target rho := by
  classical
  let S := xiDivisorSupportClosedRectangle z₁ z₂
  have hdisj : (S : Set XiDivisorSupport).PairwiseDisjoint xiZeroCopyFiber := by
    intro rho _ sigma _ hrs
    change Disjoint (xiZeroCopyFiber rho) (xiZeroCopyFiber sigma)
    rw [Finset.disjoint_left]
    intro q hqr hqs
    apply hrs
    exact (mem_xiZeroCopyFiber.mp hqr).symm.trans
      (mem_xiZeroCopyFiber.mp hqs)
  rw [xiZeroCopyClosedRectangle_eq_biUnion_supportFibers,
    show xiDivisorSupportClosedRectangle z₁ z₂ = S from rfl,
    Finset.sum_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro rho hrho
  calc
    ∑ q ∈ xiZeroCopyFiber rho, target q.1 =
        ∑ _q ∈ xiZeroCopyFiber rho, target rho := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [mem_xiZeroCopyFiber.mp hq]
    _ = (xiZeroCopyFiber rho).card • target rho :=
      Finset.sum_const (target rho)
    _ = (xiSupportMultiplicity rho : ℂ) * target rho := by
      rw [card_xiZeroCopyFiber]
      simp [xiSupportMultiplicity, nsmul_eq_mul]

/-! ## Centered source clocks -/

/-- Fixed-prime Ward coordinate written on the centered spectral plane. -/
def xiCenteredPrimeWardTranslationCoordinate
    (p : Nat.Primes) (z : ℂ) : ℝ :=
  ((p : ℝ) ^ (-2 * z.im) - 1) /
    ((p : ℝ) ^ (-2 * z.im) + 1)

/-- Unit Ward clock on the centered spectral plane.  It need not be holomorphic; finite Lagrange
lifting is precisely what permits its coefficient-faithful source realization. -/
def xiCenteredPrimeWardSourceCayleyPhase
    (p : Nat.Primes) (z : ℂ) : ℂ :=
  GaloisForLFunctions.HTGeometry.realCayley
    (xiCenteredPrimeWardTranslationCoordinate p z)

/-- Abel--Green row multiplier in centered coordinates. -/
def xiCenteredExteriorCayleyAbelGreenMultiplier (R : ℝ) (z : ℂ) : ℂ :=
  sourceCayleyAbelGreenMultiplier R (-2 * z.im)

theorem xiCenteredPrimeWardTranslationCoordinate_xiSpectralPoint
    (p : Nat.Primes) (q : XiZeroCopy) :
    xiCenteredPrimeWardTranslationCoordinate p (xiSpectralPoint q) =
      xiPrimeWardTranslationCoordinate p q.1 := by
  have hrate : -2 * (xiSpectralPoint q).im =
      primeDepthBVWoldXiCenteredRate q.1 := by
    rw [xiSpectralPoint_im_eq, primeDepthBVWoldXiCenteredRate]
    ring
  rw [xiCenteredPrimeWardTranslationCoordinate,
    xiPrimeWardTranslationCoordinate, hrate]

theorem xiCenteredPrimeWardSourceCayleyPhase_xiSpectralPoint
    (p : Nat.Primes) (q : XiZeroCopy) :
    xiCenteredPrimeWardSourceCayleyPhase p (xiSpectralPoint q) =
      xiPrimeWardSourceCayleyPhase p q.1 := by
  rw [xiCenteredPrimeWardSourceCayleyPhase,
    xiPrimeWardSourceCayleyPhase,
    xiCenteredPrimeWardTranslationCoordinate_xiSpectralPoint]

theorem xiCenteredExteriorCayleyAbelGreenMultiplier_xiSpectralPoint
    (R : ℝ) (q : XiZeroCopy) :
    xiCenteredExteriorCayleyAbelGreenMultiplier R (xiSpectralPoint q) =
      xiExteriorCayleyAbelGreenMultiplier R q.1 := by
  rw [xiCenteredExteriorCayleyAbelGreenMultiplier,
    xiExteriorCayleyAbelGreenMultiplier]
  apply congrArg (sourceCayleyAbelGreenMultiplier R)
  rw [xiSpectralPoint_im_eq]
  ring

/-- Left row of the centered three-clock exterior determinant, before feature insertion. -/
def xiPrimeWardExteriorCenteredLeftRow
    (p : Nat.Primes) (R : ℝ) (a b c : ℕ) (z : ℂ) : ℂ :=
  xiCenteredExteriorCayleyAbelGreenMultiplier R z *
    xiHorizontalPrimePhase 2 z.re ^ a *
    xiHorizontalPrimePhase 3 z.re ^ b *
    xiCenteredPrimeWardSourceCayleyPhase p z ^ c

/-- Right row: prime ordinate clocks are contragredient while the Ward clock is covariant. -/
def xiPrimeWardExteriorCenteredRightRow
    (p : Nat.Primes) (R : ℝ) (a b c : ℕ) (z : ℂ) : ℂ :=
  xiCenteredExteriorCayleyAbelGreenMultiplier R z *
    star (xiHorizontalPrimePhase 2 z.re) ^ a *
    star (xiHorizontalPrimePhase 3 z.re) ^ b *
    xiCenteredPrimeWardSourceCayleyPhase p z ^ c

theorem xiPrimeWardExteriorCenteredLeftRow_xiSpectralPoint
    (p : Nat.Primes) (R : ℝ) (a b c : ℕ) (q : XiZeroCopy) :
    xiPrimeWardExteriorCenteredLeftRow p R a b c (xiSpectralPoint q) =
      xiExteriorCayleyAbelGreenMultiplier R q.1 *
        xiHorizontalPrimePhase 2 (q.1 : ℂ).im ^ a *
        xiHorizontalPrimePhase 3 (q.1 : ℂ).im ^ b *
      xiPrimeWardSourceCayleyPhase p q.1 ^ c := by
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    rw [xiSpectralPoint]
    simp [Complex.mul_re]
  rw [xiPrimeWardExteriorCenteredLeftRow,
    xiCenteredExteriorCayleyAbelGreenMultiplier_xiSpectralPoint,
    xiCenteredPrimeWardSourceCayleyPhase_xiSpectralPoint, hre]

theorem xiPrimeWardExteriorCenteredRightRow_xiSpectralPoint
    (p : Nat.Primes) (R : ℝ) (a b c : ℕ) (q : XiZeroCopy) :
    xiPrimeWardExteriorCenteredRightRow p R a b c (xiSpectralPoint q) =
      xiExteriorCayleyAbelGreenMultiplier R q.1 *
        star (xiHorizontalPrimePhase 2 (q.1 : ℂ).im) ^ a *
        star (xiHorizontalPrimePhase 3 (q.1 : ℂ).im) ^ b *
      xiPrimeWardSourceCayleyPhase p q.1 ^ c := by
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by
    rw [xiSpectralPoint]
    simp [Complex.mul_re]
  rw [xiPrimeWardExteriorCenteredRightRow,
    xiCenteredExteriorCayleyAbelGreenMultiplier_xiSpectralPoint,
    xiCenteredPrimeWardSourceCayleyPhase_xiSpectralPoint, hre]

/-! ## Four source moments and their exterior determinant -/

/-- Support-indexed left row, with multiplicity intentionally omitted: contour residues supply it. -/
def xiPrimeWardExteriorSupportLeftRow
    (p : Nat.Primes) (R : ℝ) (a b c : ℕ) (rho : XiDivisorSupport) : ℂ :=
  xiExteriorCayleyAbelGreenMultiplier R rho *
    xiHorizontalPrimePhase 2 (rho : ℂ).im ^ a *
    xiHorizontalPrimePhase 3 (rho : ℂ).im ^ b *
    xiPrimeWardSourceCayleyPhase p rho ^ c

/-- Support-indexed contragredient right row, again before multiplicity insertion. -/
def xiPrimeWardExteriorSupportRightRow
    (p : Nat.Primes) (R : ℝ) (a b c : ℕ) (rho : XiDivisorSupport) : ℂ :=
  xiExteriorCayleyAbelGreenMultiplier R rho *
    star (xiHorizontalPrimePhase 2 (rho : ℂ).im) ^ a *
    star (xiHorizontalPrimePhase 3 (rho : ℂ).im) ^ b *
    xiPrimeWardSourceCayleyPhase p rho ^ c

theorem xiPrimeWardExteriorCenteredLeftRow_eq_support
    (p : Nat.Primes) (R : ℝ) (a b c : ℕ) (q : XiZeroCopy) :
    xiPrimeWardExteriorCenteredLeftRow p R a b c (xiSpectralPoint q) =
      xiPrimeWardExteriorSupportLeftRow p R a b c q.1 := by
  exact xiPrimeWardExteriorCenteredLeftRow_xiSpectralPoint p R a b c q

theorem xiPrimeWardExteriorCenteredRightRow_eq_support
    (p : Nat.Primes) (R : ℝ) (a b c : ℕ) (q : XiZeroCopy) :
    xiPrimeWardExteriorCenteredRightRow p R a b c (xiSpectralPoint q) =
      xiPrimeWardExteriorSupportRightRow p R a b c q.1 := by
  exact xiPrimeWardExteriorCenteredRightRow_xiSpectralPoint p R a b c q

def xiPrimeWardExteriorCenteredLeftFF
    (p : Nat.Primes) (R t : ℝ) (a b c : ℕ) (z : ℂ) : ℂ :=
  xiPrimeWardExteriorCenteredLeftRow p R a b c z *
    criticalFeatureCauchyKernelTest t z ^ 2

def xiPrimeWardExteriorCenteredRightGG
    (p : Nat.Primes) (R t : ℝ) (a b c : ℕ) (z : ℂ) : ℂ :=
  xiPrimeWardExteriorCenteredRightRow p R a b c z *
    criticalFeatureCauchyKernelTest (t + 1) z ^ 2

def xiPrimeWardExteriorCenteredLeftFG
    (p : Nat.Primes) (R t : ℝ) (a b c : ℕ) (z : ℂ) : ℂ :=
  xiPrimeWardExteriorCenteredLeftRow p R a b c z *
    criticalFeatureCauchyKernelTest t z *
    criticalFeatureCauchyKernelTest (t + 1) z

def xiPrimeWardExteriorCenteredRightFG
    (p : Nat.Primes) (R t : ℝ) (a b c : ℕ) (z : ℂ) : ℂ :=
  xiPrimeWardExteriorCenteredRightRow p R a b c z *
    criticalFeatureCauchyKernelTest t z *
    criticalFeatureCauchyKernelTest (t + 1) z

def xiPrimeWardExteriorSupportLeftFF
    (p : Nat.Primes) (R t : ℝ) (a b c : ℕ) (rho : XiDivisorSupport) : ℂ :=
  xiPrimeWardExteriorSupportLeftRow p R a b c rho *
    xiCriticalFeatureSpectralValue t rho ^ 2

def xiPrimeWardExteriorSupportRightGG
    (p : Nat.Primes) (R t : ℝ) (a b c : ℕ) (rho : XiDivisorSupport) : ℂ :=
  xiPrimeWardExteriorSupportRightRow p R a b c rho *
    xiCriticalFeatureSpectralValue (t + 1) rho ^ 2

def xiPrimeWardExteriorSupportLeftFG
    (p : Nat.Primes) (R t : ℝ) (a b c : ℕ) (rho : XiDivisorSupport) : ℂ :=
  xiPrimeWardExteriorSupportLeftRow p R a b c rho *
    xiCriticalFeatureSpectralValue t rho *
    xiCriticalFeatureSpectralValue (t + 1) rho

def xiPrimeWardExteriorSupportRightFG
    (p : Nat.Primes) (R t : ℝ) (a b c : ℕ) (rho : XiDivisorSupport) : ℂ :=
  xiPrimeWardExteriorSupportRightRow p R a b c rho *
    xiCriticalFeatureSpectralValue t rho *
    xiCriticalFeatureSpectralValue (t + 1) rho

theorem xiPrimeWardExteriorCenteredLeftFF_xiSpectralPoint
    (p : Nat.Primes) (R t : ℝ) (a b c : ℕ) (q : XiZeroCopy) :
    xiPrimeWardExteriorCenteredLeftFF p R t a b c (xiSpectralPoint q) =
      xiPrimeWardExteriorSupportLeftFF p R t a b c q.1 := by
  rw [xiPrimeWardExteriorCenteredLeftFF, xiPrimeWardExteriorSupportLeftFF,
    xiPrimeWardExteriorCenteredLeftRow_eq_support,
    xiCriticalFeatureSpectralValue, xiSpectralPoint_eq_support]

theorem xiPrimeWardExteriorCenteredRightGG_xiSpectralPoint
    (p : Nat.Primes) (R t : ℝ) (a b c : ℕ) (q : XiZeroCopy) :
    xiPrimeWardExteriorCenteredRightGG p R t a b c (xiSpectralPoint q) =
      xiPrimeWardExteriorSupportRightGG p R t a b c q.1 := by
  rw [xiPrimeWardExteriorCenteredRightGG, xiPrimeWardExteriorSupportRightGG,
    xiPrimeWardExteriorCenteredRightRow_eq_support,
    xiCriticalFeatureSpectralValue, xiSpectralPoint_eq_support]

theorem xiPrimeWardExteriorCenteredLeftFG_xiSpectralPoint
    (p : Nat.Primes) (R t : ℝ) (a b c : ℕ) (q : XiZeroCopy) :
    xiPrimeWardExteriorCenteredLeftFG p R t a b c (xiSpectralPoint q) =
      xiPrimeWardExteriorSupportLeftFG p R t a b c q.1 := by
  rw [xiPrimeWardExteriorCenteredLeftFG, xiPrimeWardExteriorSupportLeftFG,
    xiPrimeWardExteriorCenteredLeftRow_eq_support]
  simp only [xiCriticalFeatureSpectralValue, xiSpectralPoint_eq_support]

theorem xiPrimeWardExteriorCenteredRightFG_xiSpectralPoint
    (p : Nat.Primes) (R t : ℝ) (a b c : ℕ) (q : XiZeroCopy) :
    xiPrimeWardExteriorCenteredRightFG p R t a b c (xiSpectralPoint q) =
      xiPrimeWardExteriorSupportRightFG p R t a b c q.1 := by
  rw [xiPrimeWardExteriorCenteredRightFG, xiPrimeWardExteriorSupportRightFG,
    xiPrimeWardExteriorCenteredRightRow_eq_support]
  simp only [xiCriticalFeatureSpectralValue, xiSpectralPoint_eq_support]

/-- Four exact continued-source contours assembled as the oriented exterior determinant. -/
def xiPrimeWardExteriorCoefficientFaithfulSourceDeterminant
    (p : Nat.Primes) (z₁ z₂ : ℂ) (R t : ℝ) (a b c : ℕ) : ℂ :=
  normalizedXiFiniteCoefficientSourceContour z₁ z₂
      (xiPrimeWardExteriorCenteredLeftFF p R t a b c) *
    normalizedXiFiniteCoefficientSourceContour z₁ z₂
      (xiPrimeWardExteriorCenteredRightGG p R t a b c) -
  normalizedXiFiniteCoefficientSourceContour z₁ z₂
      (xiPrimeWardExteriorCenteredLeftFG p R t a b c) *
    normalizedXiFiniteCoefficientSourceContour z₁ z₂
      (xiPrimeWardExteriorCenteredRightFG p R t a b c)

/-- Same exterior determinant written on every multiplicity copy of the enclosed Xi divisor. -/
def xiPrimeWardExteriorRectangleCopyDeterminant
    (p : Nat.Primes) (z₁ z₂ : ℂ) (R t : ℝ) (a b c : ℕ) : ℂ :=
  finiteOrientedExteriorDeterminant
    (xiZeroCopyClosedRectangle z₁ z₂)
    (fun q => criticalFeatureCauchyKernelTest t (xiSpectralPoint q))
    (fun q => criticalFeatureCauchyKernelTest (t + 1) (xiSpectralPoint q))
    (fun q => xiPrimeWardExteriorCenteredLeftRow p R a b c (xiSpectralPoint q))
    (fun q => xiPrimeWardExteriorCenteredRightRow p R a b c (xiSpectralPoint q))

theorem sum_xiPrimeWardExteriorCenteredLeftFF_eq_support
    (p : Nat.Primes) (z₁ z₂ : ℂ) (R t : ℝ) (a b c : ℕ) :
    ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiPrimeWardExteriorCenteredLeftFF p R t a b c (xiSpectralPoint q) =
      ∑ rho ∈ xiDivisorSupportClosedRectangle z₁ z₂,
        (xiSupportMultiplicity rho : ℂ) *
          xiPrimeWardExteriorSupportLeftFF p R t a b c rho := by
  calc
    _ = ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiPrimeWardExteriorSupportLeftFF p R t a b c q.1 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact xiPrimeWardExteriorCenteredLeftFF_xiSpectralPoint p R t a b c q
    _ = _ := sum_xiZeroCopyClosedRectangle_eq_supportMultiplicitySum
      (xiPrimeWardExteriorSupportLeftFF p R t a b c) z₁ z₂

theorem sum_xiPrimeWardExteriorCenteredRightGG_eq_support
    (p : Nat.Primes) (z₁ z₂ : ℂ) (R t : ℝ) (a b c : ℕ) :
    ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiPrimeWardExteriorCenteredRightGG p R t a b c (xiSpectralPoint q) =
      ∑ rho ∈ xiDivisorSupportClosedRectangle z₁ z₂,
        (xiSupportMultiplicity rho : ℂ) *
          xiPrimeWardExteriorSupportRightGG p R t a b c rho := by
  calc
    _ = ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiPrimeWardExteriorSupportRightGG p R t a b c q.1 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact xiPrimeWardExteriorCenteredRightGG_xiSpectralPoint p R t a b c q
    _ = _ := sum_xiZeroCopyClosedRectangle_eq_supportMultiplicitySum
      (xiPrimeWardExteriorSupportRightGG p R t a b c) z₁ z₂

theorem sum_xiPrimeWardExteriorCenteredLeftFG_eq_support
    (p : Nat.Primes) (z₁ z₂ : ℂ) (R t : ℝ) (a b c : ℕ) :
    ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiPrimeWardExteriorCenteredLeftFG p R t a b c (xiSpectralPoint q) =
      ∑ rho ∈ xiDivisorSupportClosedRectangle z₁ z₂,
        (xiSupportMultiplicity rho : ℂ) *
          xiPrimeWardExteriorSupportLeftFG p R t a b c rho := by
  calc
    _ = ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiPrimeWardExteriorSupportLeftFG p R t a b c q.1 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact xiPrimeWardExteriorCenteredLeftFG_xiSpectralPoint p R t a b c q
    _ = _ := sum_xiZeroCopyClosedRectangle_eq_supportMultiplicitySum
      (xiPrimeWardExteriorSupportLeftFG p R t a b c) z₁ z₂

theorem sum_xiPrimeWardExteriorCenteredRightFG_eq_support
    (p : Nat.Primes) (z₁ z₂ : ℂ) (R t : ℝ) (a b c : ℕ) :
    ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiPrimeWardExteriorCenteredRightFG p R t a b c (xiSpectralPoint q) =
      ∑ rho ∈ xiDivisorSupportClosedRectangle z₁ z₂,
        (xiSupportMultiplicity rho : ℂ) *
          xiPrimeWardExteriorSupportRightFG p R t a b c rho := by
  calc
    _ = ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiPrimeWardExteriorSupportRightFG p R t a b c q.1 := by
      apply Finset.sum_congr rfl
      intro q hq
      exact xiPrimeWardExteriorCenteredRightFG_xiSpectralPoint p R t a b c q
    _ = _ := sum_xiZeroCopyClosedRectangle_eq_supportMultiplicitySum
      (xiPrimeWardExteriorSupportRightFG p R t a b c) z₁ z₂

theorem sum_supportMultiplicity_xiPrimeWardExteriorSupportLeftFF_eq_AbelRow
    (p : Nat.Primes) (S : Finset XiDivisorSupport)
    (R t : ℝ) (a b c : ℕ) :
    ∑ rho ∈ S, (xiSupportMultiplicity rho : ℂ) *
        xiPrimeWardExteriorSupportLeftFF p R t a b c rho =
      ∑ rho ∈ S,
        (xiExteriorAbelRowWeight R rho *
          xiHorizontalPrimePhase 2 (rho : ℂ).im ^ a *
          xiHorizontalPrimePhase 3 (rho : ℂ).im ^ b *
          xiPrimeWardSourceCayleyPhase p rho ^ c) *
        xiCriticalFeatureSpectralValue t rho ^ 2 := by
  apply Finset.sum_congr rfl
  intro rho hrho
  simp only [xiPrimeWardExteriorSupportLeftFF,
    xiPrimeWardExteriorSupportLeftRow, xiExteriorAbelRowWeight]
  ring

theorem sum_supportMultiplicity_xiPrimeWardExteriorSupportRightGG_eq_AbelRow
    (p : Nat.Primes) (S : Finset XiDivisorSupport)
    (R t : ℝ) (a b c : ℕ) :
    ∑ rho ∈ S, (xiSupportMultiplicity rho : ℂ) *
        xiPrimeWardExteriorSupportRightGG p R t a b c rho =
      ∑ rho ∈ S,
        (xiExteriorAbelRowWeight R rho *
          star (xiHorizontalPrimePhase 2 (rho : ℂ).im) ^ a *
          star (xiHorizontalPrimePhase 3 (rho : ℂ).im) ^ b *
          xiPrimeWardSourceCayleyPhase p rho ^ c) *
        xiCriticalFeatureSpectralValue (t + 1) rho ^ 2 := by
  apply Finset.sum_congr rfl
  intro rho hrho
  simp only [xiPrimeWardExteriorSupportRightGG,
    xiPrimeWardExteriorSupportRightRow, xiExteriorAbelRowWeight]
  ring

theorem sum_supportMultiplicity_xiPrimeWardExteriorSupportLeftFG_eq_AbelRow
    (p : Nat.Primes) (S : Finset XiDivisorSupport)
    (R t : ℝ) (a b c : ℕ) :
    ∑ rho ∈ S, (xiSupportMultiplicity rho : ℂ) *
        xiPrimeWardExteriorSupportLeftFG p R t a b c rho =
      ∑ rho ∈ S,
        (xiExteriorAbelRowWeight R rho *
          xiHorizontalPrimePhase 2 (rho : ℂ).im ^ a *
          xiHorizontalPrimePhase 3 (rho : ℂ).im ^ b *
          xiPrimeWardSourceCayleyPhase p rho ^ c) *
        xiCriticalFeatureSpectralValue t rho *
        xiCriticalFeatureSpectralValue (t + 1) rho := by
  apply Finset.sum_congr rfl
  intro rho hrho
  simp only [xiPrimeWardExteriorSupportLeftFG,
    xiPrimeWardExteriorSupportLeftRow, xiExteriorAbelRowWeight]
  ring

theorem sum_supportMultiplicity_xiPrimeWardExteriorSupportRightFG_eq_AbelRow
    (p : Nat.Primes) (S : Finset XiDivisorSupport)
    (R t : ℝ) (a b c : ℕ) :
    ∑ rho ∈ S, (xiSupportMultiplicity rho : ℂ) *
        xiPrimeWardExteriorSupportRightFG p R t a b c rho =
      ∑ rho ∈ S,
        (xiExteriorAbelRowWeight R rho *
          star (xiHorizontalPrimePhase 2 (rho : ℂ).im) ^ a *
          star (xiHorizontalPrimePhase 3 (rho : ℂ).im) ^ b *
          xiPrimeWardSourceCayleyPhase p rho ^ c) *
        xiCriticalFeatureSpectralValue t rho *
        xiCriticalFeatureSpectralValue (t + 1) rho := by
  apply Finset.sum_congr rfl
  intro rho hrho
  simp only [xiPrimeWardExteriorSupportRightFG,
    xiPrimeWardExteriorSupportRightRow, xiExteriorAbelRowWeight]
  ring

/-- **Four-leg coefficient-faithful source producer.**  For every admissible rectangle, the four
continued prime--Gamma contours equal the complete multiplicity-copy exterior determinant at each
clock-depth triple.  The equality precedes Cesaro averaging and therefore preserves both clock
orientations and every coefficient. -/
theorem xiPrimeWardExteriorCoefficientFaithfulSourceDeterminant_eq_copyDeterminant
    (p : Nat.Primes) {z₁ z₂ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (R t : ℝ) (a b c : ℕ) :
    xiPrimeWardExteriorCoefficientFaithfulSourceDeterminant
        p z₁ z₂ R t a b c =
      xiPrimeWardExteriorRectangleCopyDeterminant
        p z₁ z₂ R t a b c := by
  rw [xiPrimeWardExteriorCoefficientFaithfulSourceDeterminant,
    normalizedXiFiniteCoefficientSourceContour_eq_zeroSum
      hre him hbot htop hright hleft,
    normalizedXiFiniteCoefficientSourceContour_eq_zeroSum
      hre him hbot htop hright hleft,
    normalizedXiFiniteCoefficientSourceContour_eq_zeroSum
      hre him hbot htop hright hleft,
    normalizedXiFiniteCoefficientSourceContour_eq_zeroSum
      hre him hbot htop hright hleft,
    ← sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum
      (xiPrimeWardExteriorCenteredLeftFF p R t a b c),
    ← sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum
      (xiPrimeWardExteriorCenteredRightGG p R t a b c),
    ← sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum
      (xiPrimeWardExteriorCenteredLeftFG p R t a b c),
    ← sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum
      (xiPrimeWardExteriorCenteredRightFG p R t a b c)]
  rfl

/-- Multiplicity-copy exterior determinant is exactly the previously constructed support-indexed
source-native Abel determinant.  Thus Lagrange lifting changes only the contour presentation, not
the detector or any multiplicity coefficient. -/
theorem xiPrimeWardExteriorRectangleCopyDeterminant_eq_supportDeterminant
    (p : Nat.Primes) (z₁ z₂ : ℂ) (R t : ℝ) (a b c : ℕ) :
    xiPrimeWardExteriorRectangleCopyDeterminant p z₁ z₂ R t a b c =
      xiPrimeWardExteriorAbelDeterminant p
        (xiDivisorSupportClosedRectangle z₁ z₂) R t a b c := by
  rw [xiPrimeWardExteriorRectangleCopyDeterminant,
    finiteOrientedExteriorDeterminant]
  change
    (∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiPrimeWardExteriorCenteredLeftFF p R t a b c (xiSpectralPoint q)) *
      (∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiPrimeWardExteriorCenteredRightGG p R t a b c (xiSpectralPoint q)) -
      (∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiPrimeWardExteriorCenteredLeftFG p R t a b c (xiSpectralPoint q)) *
      (∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiPrimeWardExteriorCenteredRightFG p R t a b c (xiSpectralPoint q)) = _
  rw [sum_xiPrimeWardExteriorCenteredLeftFF_eq_support,
    sum_xiPrimeWardExteriorCenteredRightGG_eq_support,
    sum_xiPrimeWardExteriorCenteredLeftFG_eq_support,
    sum_xiPrimeWardExteriorCenteredRightFG_eq_support,
    sum_supportMultiplicity_xiPrimeWardExteriorSupportLeftFF_eq_AbelRow,
    sum_supportMultiplicity_xiPrimeWardExteriorSupportRightGG_eq_AbelRow,
    sum_supportMultiplicity_xiPrimeWardExteriorSupportLeftFG_eq_AbelRow,
    sum_supportMultiplicity_xiPrimeWardExteriorSupportRightFG_eq_AbelRow]
  rfl

/-- Direct source-contour identification with the existing support-indexed exterior determinant. -/
theorem xiPrimeWardExteriorCoefficientFaithfulSourceDeterminant_eq_supportDeterminant
    (p : Nat.Primes) {z₁ z₂ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (R t : ℝ) (a b c : ℕ) :
    xiPrimeWardExteriorCoefficientFaithfulSourceDeterminant
        p z₁ z₂ R t a b c =
      xiPrimeWardExteriorAbelDeterminant p
        (xiDivisorSupportClosedRectangle z₁ z₂) R t a b c := by
  rw [xiPrimeWardExteriorCoefficientFaithfulSourceDeterminant_eq_copyDeterminant
      p hre him hbot htop hright hleft R t a b c,
    xiPrimeWardExteriorRectangleCopyDeterminant_eq_supportDeterminant]

/-! ## Source-contour Cesaro landing and a block-free two-orientation packet -/

/-- Triple Cesaro average formed entirely from the four coefficient-faithful source contours. -/
def xiPrimeWardExteriorCoefficientFaithfulSourceCesaro
    (p : Nat.Primes) (z₁ z₂ : ℂ) (t : ℝ) (N : ℕ) : ℂ :=
  (((N : ℝ)⁻¹ : ℂ) ^ 3) *
    ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
      xiPrimeWardExteriorCoefficientFaithfulSourceDeterminant
        p z₁ z₂ 1 t a b c

/-- Two adjacent reporter orientations on the same full source rectangle.  No post-divisor block
restriction is needed for a contradiction: every extra coefficient is a nonnegative norm square
after landing. -/
def xiPrimeWardExteriorCoefficientFaithfulTwoOrientationSourceCesaro
    (p : Nat.Primes) (z₁ z₂ : ℂ) (t : ℝ) (N : ℕ) : ℂ :=
  2 * (xiPrimeWardExteriorCoefficientFaithfulSourceCesaro p z₁ z₂ t N +
    xiPrimeWardExteriorCoefficientFaithfulSourceCesaro p z₁ z₂ (t - 1) N)

theorem xiPrimeWardExteriorCoefficientFaithfulSourceCesaro_eq_supportCesaro
    (p : Nat.Primes) {z₁ z₂ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (t : ℝ) (N : ℕ) :
    xiPrimeWardExteriorCoefficientFaithfulSourceCesaro p z₁ z₂ t N =
      (((N : ℝ)⁻¹ : ℂ) ^ 3) *
        ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          xiPrimeWardExteriorAbelDeterminant p
            (xiDivisorSupportClosedRectangle z₁ z₂) 1 t a b c := by
  rw [xiPrimeWardExteriorCoefficientFaithfulSourceCesaro]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  exact xiPrimeWardExteriorCoefficientFaithfulSourceDeterminant_eq_supportDeterminant
    p hre him hbot htop hright hleft 1 t a b c

/-- One source-contour reporter orientation lands on its exact positive Abel packet energy. -/
theorem tendsto_xiPrimeWardExteriorCoefficientFaithfulSourceCesaro
    (p : Nat.Primes) {z₁ z₂ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (hclosed : ∀ rho ∈ xiDivisorSupportClosedRectangle z₁ z₂,
      xiZeroLineConjEquiv rho ∈ xiDivisorSupportClosedRectangle z₁ z₂)
    (t : ℝ) :
    Tendsto
      (xiPrimeWardExteriorCoefficientFaithfulSourceCesaro p z₁ z₂ t)
      atTop
      (nhds (((1 / 2 : ℝ) * xiExteriorCayleyAbelFixedPacketEnergy
        (xiDivisorSupportClosedRectangle z₁ z₂) 1 t : ℝ) : ℂ)) := by
  have hlim := tendsto_xiPrimeWardExteriorAbelDeterminant_one p
    (xiDivisorSupportClosedRectangle z₁ z₂) hclosed t
  apply hlim.congr'
  filter_upwards with N
  exact (xiPrimeWardExteriorCoefficientFaithfulSourceCesaro_eq_supportCesaro
    p hre him hbot htop hright hleft t N).symm

/-- **Block-free positive landing.**  Two full-rectangle source orientations land on the sum of
their positive fixed-center energies.  Reporter blocks were needed only for an exact global packet
partition; they are unnecessary when deriving a contradiction from one retained off-line class. -/
theorem tendsto_xiPrimeWardExteriorCoefficientFaithfulTwoOrientationSourceCesaro
    (p : Nat.Primes) {z₁ z₂ : ℂ}
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I))
    (hclosed : ∀ rho ∈ xiDivisorSupportClosedRectangle z₁ z₂,
      xiZeroLineConjEquiv rho ∈ xiDivisorSupportClosedRectangle z₁ z₂)
    (t : ℝ) :
    Tendsto
      (xiPrimeWardExteriorCoefficientFaithfulTwoOrientationSourceCesaro p z₁ z₂ t)
      atTop
      (nhds (((xiExteriorCayleyAbelFixedPacketEnergy
          (xiDivisorSupportClosedRectangle z₁ z₂) 1 t +
        xiExteriorCayleyAbelFixedPacketEnergy
          (xiDivisorSupportClosedRectangle z₁ z₂) 1 (t - 1) : ℝ) : ℂ))) := by
  have hp := tendsto_xiPrimeWardExteriorCoefficientFaithfulSourceCesaro
    p hre him hbot htop hright hleft hclosed t
  have hm := tendsto_xiPrimeWardExteriorCoefficientFaithfulSourceCesaro
    p hre him hbot htop hright hleft hclosed (t - 1)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℂ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hlim := htwo.mul (hp.add hm)
  convert hlim using 1
  · rfl
  · apply congrArg nhds
    push_cast
    ring

/-! ## A strict source bound forces the exterior quantum contradiction -/

/-- A symmetric centered rectangle is closed under critical-line reflection of its Xi divisor
support. -/
theorem xiDivisorSupportClosedSymmetricRectangle_lineConj_closed
    {R c : ℝ} (hR : 0 ≤ R) (hc : 0 ≤ c) :
    ∀ rho ∈ xiDivisorSupportClosedRectangle (symmetricRectangleLower R c)
        (symmetricRectangleUpper R c),
      xiZeroLineConjEquiv rho ∈
        xiDivisorSupportClosedRectangle (symmetricRectangleLower R c)
          (symmetricRectangleUpper R c) := by
  intro rho hrho
  rw [mem_xiDivisorSupportClosedRectangle] at hrho ⊢
  rw [xiSpectralPointSupport_lineConj_boundaryClosure]
  apply Complex.mem_reProdIm.mpr
  obtain ⟨hrhoRe, hrhoIm⟩ := Complex.mem_reProdIm.mp hrho
  have hre : (symmetricRectangleLower R c).re ≤
      (symmetricRectangleUpper R c).re := by
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith
  have him : (symmetricRectangleLower R c).im ≤
      (symmetricRectangleUpper R c).im := by
    simp [symmetricRectangleLower, symmetricRectangleUpper]
    linarith
  rw [uIcc_of_le hre] at hrhoRe
  rw [uIcc_of_le him] at hrhoIm
  rw [uIcc_of_le hre, uIcc_of_le him]
  have hrhoRe' : -R ≤ (xiSpectralPointSupport rho).re ∧
      (xiSpectralPointSupport rho).re ≤ R := by
    simpa [symmetricRectangleLower, symmetricRectangleUpper] using hrhoRe
  have hrhoIm' : -c ≤ (xiSpectralPointSupport rho).im ∧
      (xiSpectralPointSupport rho).im ≤ c := by
    simpa [symmetricRectangleLower, symmetricRectangleUpper] using hrhoIm
  constructor
  · simpa [symmetricRectangleLower, symmetricRectangleUpper] using hrhoRe'
  · have hcj : -c ≤ -(xiSpectralPointSupport rho).im ∧
        -(xiSpectralPointSupport rho).im ≤ c := by
      constructor <;> linarith [hrhoIm'.1, hrhoIm'.2]
    simpa [symmetricRectangleLower, symmetricRectangleUpper] using hcj

/-- Symmetric admissibility is exactly the four edge hypotheses used by the source contour. -/
theorem xiSymmetricRectangleExplicitAdmissible_sourceEdges
    {R c : ℝ} (hadm : XiSymmetricRectangleExplicitAdmissible R c) :
    (∀ x ∈ uIcc (symmetricRectangleLower R c).re
        (symmetricRectangleUpper R c).re,
      XiExplicitAdmissible
        ((x : ℂ) + (symmetricRectangleLower R c).im * I)) ∧
    (∀ x ∈ uIcc (symmetricRectangleLower R c).re
        (symmetricRectangleUpper R c).re,
      XiExplicitAdmissible
        ((x : ℂ) + (symmetricRectangleUpper R c).im * I)) ∧
    (∀ y ∈ uIcc (symmetricRectangleLower R c).im
        (symmetricRectangleUpper R c).im,
      XiExplicitAdmissible
        (((symmetricRectangleUpper R c).re : ℂ) + y * I)) ∧
    (∀ y ∈ uIcc (symmetricRectangleLower R c).im
        (symmetricRectangleUpper R c).im,
      XiExplicitAdmissible
        (((symmetricRectangleLower R c).re : ℂ) + y * I)) := by
  simpa [XiSymmetricRectangleExplicitAdmissible, symmetricRectangleLower,
    symmetricRectangleUpper, sub_eq_add_neg] using hadm

/-- Countable source-side condition exposed by the exterior quantum.  Prime `2` and rational
admissible symmetric rectangles suffice: the real part of every two-orientation contour packet is
eventually bounded strictly below the cost of one off-line divisor copy. -/
def XiPrimeWardExteriorCoefficientFaithfulSourceSubquantum : Prop :=
  ∀ (R c : ℚ), 0 < (R : ℝ) → 0 < (c : ℝ) → (c : ℝ) < 1 / 2 →
    XiSymmetricRectangleExplicitAdmissible (R : ℝ) (c : ℝ) →
    ∀ t : ℝ, ∃ C : ℝ,
      C < 4 * (96 / 145 : ℝ) ^ 2 ∧
      ∀ᶠ N : ℕ in atTop,
        (xiPrimeWardExteriorCoefficientFaithfulTwoOrientationSourceCesaro
          ⟨2, Nat.prime_two⟩
          (symmetricRectangleLower (R : ℝ) (c : ℝ))
          (symmetricRectangleUpper (R : ℝ) (c : ℝ)) t N).re ≤ C

/-- **Coefficient-faithful source criterion for RH.**  A strict subquantum estimate on the exact
continued prime--Gamma contour packet rules out even one off-line Xi divisor.  The proof retains
both reflected exterior orientations and the full analytic multiplicity; all other rectangle
coefficients enter only through nonnegative norm squares. -/
theorem riemannHypothesis_of_xiPrimeWardExteriorCoefficientFaithfulSourceSubquantum
    (hsource : XiPrimeWardExteriorCoefficientFaithfulSourceSubquantum) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_xiSpectralPointSupport_im_eq_zero
  intro rho
  by_contra hy
  have hoff : (rho : ℂ).re ≠ 1 / 2 := by
    exact fun hline => hy ((xiSpectralPointSupport_im_eq_zero_iff rho).2 hline)
  let q : XiZeroCopy := xiDivisorSupportCanonicalCopy rho
  obtain ⟨R, c, hR, hc, hchalf, hqreL, hqreR, hqimL, hqimR, hadm⟩ :=
    exists_admissible_rational_symmetric_rectangle_containing_xiZeroCopy q
  let z₁ := symmetricRectangleLower (R : ℝ) (c : ℝ)
  let z₂ := symmetricRectangleUpper (R : ℝ) (c : ℝ)
  let S := xiDivisorSupportClosedRectangle z₁ z₂
  let t := xiExteriorReporterCenter rho
  have hzre : z₁.re < z₂.re := by
    have hRrat : (0 : ℚ) < R := by exact_mod_cast hR
    simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using
      (neg_lt_self hRrat)
  have hzim : z₁.im < z₂.im := by
    have hcrat : (0 : ℚ) < c := by exact_mod_cast hc
    simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using
      (neg_lt_self hcrat)
  obtain ⟨hbot, htop, hright, hleft⟩ :=
    xiSymmetricRectangleExplicitAdmissible_sourceEdges hadm
  have hclosed : ∀ sigma ∈ S, xiZeroLineConjEquiv sigma ∈ S := by
    exact xiDivisorSupportClosedSymmetricRectangle_lineConj_closed hR.le hc.le
  have hrho : rho ∈ S := by
    rw [mem_xiDivisorSupportClosedRectangle]
    apply Complex.mem_reProdIm.mpr
    rw [uIcc_of_le hzre.le, uIcc_of_le hzim.le]
    constructor
    · simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper,
        q, xiSpectralPoint_eq_support] using
        ⟨hqreL.le, hqreR.le⟩
    · simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper,
        q, xiSpectralPoint_eq_support] using
        ⟨hqimL.le, hqimR.le⟩
  obtain ⟨C, hC, hbound⟩ := hsource R c hR hc hchalf hadm t
  have hlimComplex :=
    tendsto_xiPrimeWardExteriorCoefficientFaithfulTwoOrientationSourceCesaro
      ⟨2, Nat.prime_two⟩ hzre hzim hbot htop hright hleft hclosed t
  have hlim : Tendsto
      (fun N : ℕ =>
        (xiPrimeWardExteriorCoefficientFaithfulTwoOrientationSourceCesaro
          ⟨2, Nat.prime_two⟩ z₁ z₂ t N).re)
      atTop
      (nhds (xiExteriorCayleyAbelFixedPacketEnergy S 1 t +
        xiExteriorCayleyAbelFixedPacketEnergy S 1 (t - 1))) := by
    have hlimRe := (Complex.continuous_re.tendsto
        (((xiExteriorCayleyAbelFixedPacketEnergy S 1 t +
          xiExteriorCayleyAbelFixedPacketEnergy S 1 (t - 1) : ℝ) : ℂ))).comp
        hlimComplex
    change Tendsto
      (fun N : ℕ =>
        (xiPrimeWardExteriorCoefficientFaithfulTwoOrientationSourceCesaro
          ⟨2, Nat.prime_two⟩ z₁ z₂ t N).re)
      atTop
      (nhds ((((xiExteriorCayleyAbelFixedPacketEnergy S 1 t +
        xiExteriorCayleyAbelFixedPacketEnergy S 1 (t - 1) : ℝ) : ℂ)).re)) at hlimRe
    simpa only [Complex.ofReal_re] using hlimRe
  have hpacketLe : xiExteriorCayleyAbelFixedPacketEnergy S 1 t +
      xiExteriorCayleyAbelFixedPacketEnergy S 1 (t - 1) ≤ C :=
    le_of_tendsto hlim hbound
  have hplus :
      Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) *
        xiWardGreenExteriorPlusCoefficient rho) ≤
      xiExteriorCayleyAbelFixedPacketEnergy S 1 t := by
    rw [← xiExteriorCayleyAbelFixedCoefficient_one_eq_plus_of_center
      t rho rfl]
    rw [xiExteriorCayleyAbelFixedPacketEnergy]
    exact Finset.single_le_sum
      (f := fun sigma => Complex.normSq
        (((xiSupportMultiplicity sigma : ℕ) : ℂ) *
          xiExteriorCayleyAbelFixedCoefficient 1 t sigma))
      (fun sigma _ => Complex.normSq_nonneg _) hrho
  have hminus :
      Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) *
        xiWardGreenExteriorMinusCoefficient rho) ≤
      xiExteriorCayleyAbelFixedPacketEnergy S 1 (t - 1) := by
    rw [← xiExteriorCayleyAbelFixedCoefficient_one_eq_minus_of_center
      t rho rfl]
    rw [xiExteriorCayleyAbelFixedPacketEnergy]
    exact Finset.single_le_sum
      (f := fun sigma => Complex.normSq
        (((xiSupportMultiplicity sigma : ℕ) : ℂ) *
          xiExteriorCayleyAbelFixedCoefficient 1 (t - 1) sigma))
      (fun sigma _ => Complex.normSq_nonneg _) hrho
  have hscaled :
      Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) *
          xiWardGreenExteriorPlusCoefficient rho) +
        Complex.normSq (((xiSupportMultiplicity rho : ℕ) : ℂ) *
          xiWardGreenExteriorMinusCoefficient rho) =
      (xiSupportMultiplicity rho : ℝ) ^ 2 *
        xiWardGreenExteriorLocalEnergy rho := by
    simp only [Complex.normSq_mul, Complex.normSq_natCast,
      xiWardGreenExteriorLocalEnergy]
    ring
  have hscaledLe : (xiSupportMultiplicity rho : ℝ) ^ 2 *
      xiWardGreenExteriorLocalEnergy rho ≤
      xiExteriorCayleyAbelFixedPacketEnergy S 1 t +
        xiExteriorCayleyAbelFixedPacketEnergy S 1 (t - 1) := by
    rw [← hscaled]
    exact add_le_add hplus hminus
  have hlocal :=
    four_mul_transverseQuantum_le_xiWardGreenExteriorLocalEnergy_of_offLine rho hoff
  have hm : (1 : ℝ) ≤ (xiSupportMultiplicity rho : ℝ) ^ 2 := by
    have hmpos : 0 < xiSupportMultiplicity rho := xiSupportMultiplicity_pos rho
    have hm1 : (1 : ℝ) ≤ (xiSupportMultiplicity rho : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hmpos.ne'
    nlinarith
  have hnonneg : 0 ≤ xiWardGreenExteriorLocalEnergy rho := by
    rw [xiWardGreenExteriorLocalEnergy]
    positivity
  have hlower : 4 * (96 / 145 : ℝ) ^ 2 ≤
      (xiSupportMultiplicity rho : ℝ) ^ 2 *
        xiWardGreenExteriorLocalEnergy rho := by
    calc
      4 * (96 / 145 : ℝ) ^ 2 ≤ xiWardGreenExteriorLocalEnergy rho := hlocal
      _ ≤ (xiSupportMultiplicity rho : ℝ) ^ 2 *
          xiWardGreenExteriorLocalEnergy rho := by nlinarith
  linarith

/-- Every fixed-center exterior coefficient vanishes on the critical line, independently of the
reporter center and Abel radius. -/
theorem xiExteriorCayleyAbelFixedCoefficient_eq_zero_of_onLine
    (R t : ℝ) (rho : XiDivisorSupport) (hline : (rho : ℂ).re = 1 / 2) :
    xiExteriorCayleyAbelFixedCoefficient R t rho = 0 := by
  have hy : (xiSpectralPointSupport rho).im = 0 :=
    (xiSpectralPointSupport_im_eq_zero_iff rho).2 hline
  rw [xiExteriorCayleyAbelFixedCoefficient,
    adjacentCriticalFeatureEvaluationDet_eq_zero_of_im_eq_zero _ _
      (abs_xiSpectralPointSupport_im_lt_half_exteriorCarrier rho) hy,
    mul_zero]

/-- Under RH every full fixed-center packet energy vanishes; no reporter-block restriction is
needed. -/
theorem xiExteriorCayleyAbelFixedPacketEnergy_eq_zero_of_riemannHypothesis
    (hRH : RiemannHypothesis) (S : Finset XiDivisorSupport) (R t : ℝ) :
    xiExteriorCayleyAbelFixedPacketEnergy S R t = 0 := by
  rw [xiExteriorCayleyAbelFixedPacketEnergy, Finset.sum_eq_zero]
  intro rho hrho
  rw [xiExteriorCayleyAbelFixedCoefficient_eq_zero_of_onLine R t rho
    (xi_divisor_support_re_eq_half_of_rh hRH rho), mul_zero,
    Complex.normSq_zero]

/-- RH supplies the strict source-subquantum estimate because every exact source packet tends to
zero. -/
theorem xiPrimeWardExteriorCoefficientFaithfulSourceSubquantum_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiPrimeWardExteriorCoefficientFaithfulSourceSubquantum := by
  intro R c hR hc hchalf hadm t
  let z₁ := symmetricRectangleLower (R : ℝ) (c : ℝ)
  let z₂ := symmetricRectangleUpper (R : ℝ) (c : ℝ)
  let S := xiDivisorSupportClosedRectangle z₁ z₂
  have hzre : z₁.re < z₂.re := by
    have hRrat : (0 : ℚ) < R := by exact_mod_cast hR
    simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using
      (neg_lt_self hRrat)
  have hzim : z₁.im < z₂.im := by
    have hcrat : (0 : ℚ) < c := by exact_mod_cast hc
    simpa [z₁, z₂, symmetricRectangleLower, symmetricRectangleUpper] using
      (neg_lt_self hcrat)
  obtain ⟨hbot, htop, hright, hleft⟩ :=
    xiSymmetricRectangleExplicitAdmissible_sourceEdges hadm
  have hclosed : ∀ rho ∈ S, xiZeroLineConjEquiv rho ∈ S := by
    exact xiDivisorSupportClosedSymmetricRectangle_lineConj_closed hR.le hc.le
  have hpacketZero :
      xiExteriorCayleyAbelFixedPacketEnergy S 1 t +
        xiExteriorCayleyAbelFixedPacketEnergy S 1 (t - 1) = 0 := by
    rw [xiExteriorCayleyAbelFixedPacketEnergy_eq_zero_of_riemannHypothesis hRH,
      xiExteriorCayleyAbelFixedPacketEnergy_eq_zero_of_riemannHypothesis hRH,
      add_zero]
  have hlimComplex :=
    tendsto_xiPrimeWardExteriorCoefficientFaithfulTwoOrientationSourceCesaro
      ⟨2, Nat.prime_two⟩ hzre hzim hbot htop hright hleft hclosed t
  rw [hpacketZero] at hlimComplex
  have hlimRe := (Complex.continuous_re.tendsto (0 : ℂ)).comp hlimComplex
  change Tendsto
    (fun N : ℕ =>
      (xiPrimeWardExteriorCoefficientFaithfulTwoOrientationSourceCesaro
        ⟨2, Nat.prime_two⟩ z₁ z₂ t N).re)
    atTop (nhds (0 : ℝ)) at hlimRe
  let C : ℝ := 2 * (96 / 145 : ℝ) ^ 2
  have hCpos : 0 < C := by
    dsimp only [C]
    positivity
  have hCquantum : C < 4 * (96 / 145 : ℝ) ^ 2 := by
    dsimp only [C]
    have hsq : 0 < (96 / 145 : ℝ) ^ 2 := by positivity
    nlinarith
  refine ⟨C, hCquantum, ?_⟩
  exact ((tendsto_order.1 hlimRe).2 C hCpos).mono fun _ h => h.le

/-- **Sharp classification of the new producer.**  The fixed-prime, rational-rectangle,
coefficient-faithful source-subquantum law is exactly RH.  Hence the remaining task cannot be
discharged by a generic finite contour bound: it must consume arithmetic cancellation strong
enough to annihilate the retained two-orientation packet. -/
theorem xiPrimeWardExteriorCoefficientFaithfulSourceSubquantum_iff_riemannHypothesis :
    XiPrimeWardExteriorCoefficientFaithfulSourceSubquantum ↔ RiemannHypothesis := by
  exact ⟨riemannHypothesis_of_xiPrimeWardExteriorCoefficientFaithfulSourceSubquantum,
    xiPrimeWardExteriorCoefficientFaithfulSourceSubquantum_of_riemannHypothesis⟩

end

end RHTower
