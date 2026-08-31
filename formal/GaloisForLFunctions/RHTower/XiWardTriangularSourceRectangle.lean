import GaloisForLFunctions.RHTower.XiWardCellRandomizedAnnulusCoercivity
import GaloisForLFunctions.RHTower.XiCriticalLineThinStripSourceProjector

/-!
# Source rectangles for the triangular Ward receiver

The deterministic half-cell tent in
`XiWardCellRandomizedAnnulusCoercivity` removes every divisor-dependent sign
choice.  This file supplies its linear source primitive.  A raw Ward Cauchy
column is a rational weight whose only pole lies in the upper centered half
plane.  It is therefore holomorphic on every lower-half rectangle containing
strict-right Xi points.  The local Guinand--Weil rectangle theorem then turns
its continued pole--Gamma--von-Mangoldt contour exactly into the finite Ward
response sum in that height window.

No approximation theorem and no zero-fitted coefficient is used.  Remaining
quadratic task is to average products of these fixed rectangle responses
against the already formalized interval autocorrelation and prove the sharp
source budget.
-/

open Complex Set intervalIntegral
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Rational Cauchy weight whose value at a centered spectral point is one
raw anti-causal Ward mode. -/
def xiWardCauchySourceWeight (w z : ℂ) : ℂ :=
  2 * (w + I * z)⁻¹

/-- The sole pole of the Ward Cauchy source weight. -/
def xiWardCauchySourcePoleFreeDomain (w : ℂ) : Set ℂ :=
  {z | z ≠ I * w}

theorem isOpen_xiWardCauchySourcePoleFreeDomain (w : ℂ) :
    IsOpen (xiWardCauchySourcePoleFreeDomain w) := by
  rw [xiWardCauchySourcePoleFreeDomain]
  exact isOpen_compl_singleton

/-- The rational Ward weight is holomorphic away from its explicit upper
half-plane pole. -/
theorem analyticOnNhd_xiWardCauchySourceWeight (w : ℂ) :
    AnalyticOnNhd ℂ (xiWardCauchySourceWeight w)
      (xiWardCauchySourcePoleFreeDomain w) := by
  intro z hz
  have hden : w + I * z ≠ 0 := by
    rw [show w + I * z = I * (z - I * w) by
      rw [mul_sub, ← mul_assoc, I_mul_I]
      ring]
    exact mul_ne_zero I_ne_zero (sub_ne_zero.mpr hz)
  unfold xiWardCauchySourceWeight
  exact analyticAt_const.mul
    ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)).inv hden)

/-- Every rectangle contained in the closed lower centered half-plane avoids
the Ward weight pole whenever the observation node has positive real part. -/
theorem lowerHalf_rectangle_subset_xiWardCauchySourcePoleFreeDomain
    {w z₁ z₂ : ℂ} (hw : 0 < w.re) (him : z₁.im ≤ z₂.im)
    (hupper : z₂.im ≤ 0) :
    (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆
      xiWardCauchySourcePoleFreeDomain w := by
  intro z hz
  have hzIm := (Complex.mem_reProdIm.mp hz).2
  rw [uIcc_of_le him] at hzIm
  rw [xiWardCauchySourcePoleFreeDomain, Set.mem_setOf_eq]
  intro hzw
  have himEq := congrArg Complex.im hzw
  simp only [mul_im, I_re, zero_mul, I_im, one_mul, zero_add] at himEq
  have hzupper : z.im ≤ z₂.im := hzIm.2
  linarith

/-- Normalized local pole--Gamma--von-Mangoldt contour carrying one Ward
Cauchy column. -/
def xiWardCauchySourceRectangleResponse
    (w z₁ z₂ : ℂ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ *
    rectIntegral
      (fun z => xiWardCauchySourceWeight w z *
        continuedPrimeArchSourceRelativeTrace z)
      z₁ z₂

/-- **Local source-to-Ward weld.**  On every admissible lower-half rectangle,
the normalized continued prime--archimedean contour is exactly the sum of
the Ward Cauchy weight over all enclosed Xi multiplicity copies. -/
theorem xiWardCauchySourceRectangleResponse_eq_xiZeroCopy_sum
    {w z₁ z₂ : ℂ}
    (hrect : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆
      xiWardCauchySourcePoleFreeDomain w)
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    xiWardCauchySourceRectangleResponse w z₁ z₂ =
      ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiWardCauchySourceWeight w (xiSpectralPoint q) := by
  have hres :=
    rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum_local
      (isOpen_xiWardCauchySourcePoleFreeDomain w)
      (analyticOnNhd_xiWardCauchySourceWeight w)
      hrect hre him hbot htop hright hleft
  have hconvert :
      (∑ z ∈ xiCClosedRectangleZeros z₁ z₂,
          ((analyticOrderAt XiC z).toNat : ℂ) *
            xiWardCauchySourceWeight w z) =
        ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
          xiWardCauchySourceWeight w (xiSpectralPoint q) := by
    calc
      (∑ z ∈ xiCClosedRectangleZeros z₁ z₂,
          ((analyticOrderAt XiC z).toNat : ℂ) *
            xiWardCauchySourceWeight w z) =
          ∑ z ∈ xiCClosedRectangleZeros z₁ z₂,
            (xiSpectralMultiplicity z : ℂ) *
              xiWardCauchySourceWeight w z := by
        apply Finset.sum_congr rfl
        intro z hz
        have hzero : XiC z = 0 := (mem_xiCClosedRectangleZeros.mp hz).2
        rw [xiSpectralMultiplicity_eq_analyticOrderAt_toNat hzero]
      _ = ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
          xiWardCauchySourceWeight w (xiSpectralPoint q) :=
        (sum_xiZeroCopyClosedRectangle_eq_multiplicity_sum
          (xiWardCauchySourceWeight w) z₁ z₂).symm
  have hc : (2 * Real.pi * I : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
    · exact I_ne_zero
  rw [xiWardCauchySourceRectangleResponse, hres,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul, hconvert]

/-- Lower-half specialization: pole avoidance is automatic from geometry. -/
theorem xiWardCauchySourceRectangleResponse_eq_xiZeroCopy_sum_lowerHalf
    {w z₁ z₂ : ℂ} (hw : 0 < w.re)
    (hre : z₁.re < z₂.re) (him : z₁.im < z₂.im) (hupper : z₂.im ≤ 0)
    (hbot : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₁.im * I))
    (htop : ∀ x ∈ uIcc z₁.re z₂.re,
      XiExplicitAdmissible ((x : ℂ) + z₂.im * I))
    (hright : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₂.re : ℂ) + y * I))
    (hleft : ∀ y ∈ uIcc z₁.im z₂.im,
      XiExplicitAdmissible ((z₁.re : ℂ) + y * I)) :
    xiWardCauchySourceRectangleResponse w z₁ z₂ =
      ∑ q ∈ xiZeroCopyClosedRectangle z₁ z₂,
        xiWardCauchySourceWeight w (xiSpectralPoint q) := by
  exact xiWardCauchySourceRectangleResponse_eq_xiZeroCopy_sum
    (lowerHalf_rectangle_subset_xiWardCauchySourcePoleFreeDomain
      hw him.le hupper)
    hre him hbot htop hright hleft

/-- Pairing one upper strict-right copy with its Schwarz mate turns two
source Cauchy weights into the raw Ward Schwarz-pair response exactly. -/
theorem xiWardCauchySourceWeight_add_conj_eq_schwarzPairResponse
    (q : XiRightUpperZeroCopy) (w : ℂ) :
    xiWardCauchySourceWeight w (xiSpectralPoint q.1.1) +
        xiWardCauchySourceWeight w
          (xiSpectralPoint (xiRightZeroCopyConjEquiv q.1).1) =
      xiAntiCausalWardSchwarzPairResponse q w := by
  unfold xiWardCauchySourceWeight xiAntiCausalWardSchwarzPairResponse
    xiRightCenteredZero
  ring

end

end RHTower
