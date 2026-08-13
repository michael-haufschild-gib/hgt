import GaloisForLFunctions.RHTower.XiHorizontalCollisionPrimeCayleyInformationLoss
import GaloisForLFunctions.RHTower.HedenmalmWardDefectTransverseGreenSource
import GaloisForLFunctions.RHTower.XiReflectionSelfIntersectionCharge

/-!
# Ward--Green normalization of horizontal Cayley information loss

The source-Cayley reflection gap vanishes quadratically as a zero approaches the critical line.
This is exactly the spectral-collapse wall that defeats raw rank/index amplification.  The Ward
Euclidean defect supplies a source-derived inverse-square Green weight with the same kernel.

Multiplying them is not singular bookkeeping: away from the kernel the product is explicitly
`64 / (1 + x^2)^2`, where `x = 2 Re rho - 1`.  Since every Xi divisor point lies in the open
critical strip, each off-line multiplicity copy carries strictly more than `16` units, while the
critical-line value is totalized to zero.  Summing over a finite strip window yields a uniform
source-normalized energy dominating `16` times canonical reflection charge.  Consequently an
absolute energy bound below `32` proves RH.

All statements are unconditional.  Remaining producer is arithmetic evaluation/boundedness of
this Ward--Green normalized source loss.
-/

open Complex Set Metric Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Exact oriented Cayley gap between opposite horizontal source rates. -/
theorem realCayley_sub_neg_eq (x : ℝ) :
    GaloisForLFunctions.HTGeometry.realCayley x -
        GaloisForLFunctions.HTGeometry.realCayley (-x) =
      ((-4 * x : ℝ) : ℂ) * I / ((x ^ 2 + 1 : ℝ) : ℂ) := by
  have hp : (x : ℂ) + I ≠ 0 :=
    GaloisForLFunctions.HTGeometry.real_add_I_ne_zero x
  have hm : ((-x : ℝ) : ℂ) + I ≠ 0 :=
    GaloisForLFunctions.HTGeometry.real_add_I_ne_zero (-x)
  have hd : ((x ^ 2 + 1 : ℝ) : ℂ) ≠ 0 := by
    exact ofReal_ne_zero.mpr (by positivity)
  unfold GaloisForLFunctions.HTGeometry.realCayley
  field_simp [hp, hm, hd]
  ring_nf
  rw [I_sq]
  have hI3 : I ^ 3 = -I := by
    rw [show (3 : ℕ) = 2 + 1 by omega, pow_succ, I_sq]
    ring
  rw [hI3]
  push_cast
  ring

/-- Cayley reflection gap is exactly quadratic in horizontal rate. -/
theorem norm_sq_realCayley_sub_neg (x : ℝ) :
    ‖GaloisForLFunctions.HTGeometry.realCayley x -
        GaloisForLFunctions.HTGeometry.realCayley (-x)‖ ^ 2 =
      16 * x ^ 2 / (1 + x ^ 2) ^ 2 := by
  rw [realCayley_sub_neg_eq, norm_div, norm_mul, norm_real, norm_I, norm_real]
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  rw [mul_one, abs_of_nonneg (by positivity : 0 ≤ x ^ 2 + 1)]
  rw [div_pow, sq_abs]
  field_simp
  ring

/-- Source-derived Green normalization of the Cayley gap between one divisor copy and its
line-reflected copy. -/
def xiHorizontalWardGreenCayleyReflectionQuantum (q : XiZeroCopy) : ℝ :=
  thetaXiWardTransverseGreenWeight q *
    ‖xiHorizontalSourceCayleyPhase q.1 -
      xiHorizontalSourceCayleyPhase (xiZeroCopyLineConjEquiv q).1‖ ^ 2

theorem xiHorizontalSourceCayleyPhase_reflection (q : XiZeroCopy) :
    xiHorizontalSourceCayleyPhase (xiZeroCopyLineConjEquiv q).1 =
      GaloisForLFunctions.HTGeometry.realCayley
        (-(2 * (q.1 : ℂ).re - 1)) := by
  rw [xiHorizontalSourceCayleyPhase]
  congr 1
  rw [xiZeroCopyLineConjEquiv_fst, xiZeroLineConjEquiv_apply]
  simp
  ring

/-- Away from the critical line, Ward Green cancels the complete quadratic Cayley collapse. -/
theorem xiHorizontalWardGreenCayleyReflectionQuantum_eq_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    xiHorizontalWardGreenCayleyReflectionQuantum q =
      64 / (1 + (2 * (q.1 : ℂ).re - 1) ^ 2) ^ 2 := by
  let x : ℝ := 2 * (q.1 : ℂ).re - 1
  have hx : x ≠ 0 := by
    dsimp only [x]
    intro h
    apply hoff
    linarith
  have him : (xiSpectralPoint q).im = -(x / 2) := by
    rw [xiSpectralPoint_im_eq]
    dsimp only [x]
    ring
  rw [xiHorizontalWardGreenCayleyReflectionQuantum,
    thetaXiWardTransverseGreenWeight_eq,
    xiHorizontalSourceCayleyPhase,
    xiHorizontalSourceCayleyPhase_reflection,
    norm_sq_realCayley_sub_neg]
  change ((xiSpectralPoint q).im)⁻¹ ^ 2 *
      (16 * x ^ 2 / (1 + x ^ 2) ^ 2) = _
  rw [him]
  field_simp
  ring

/-- On-line value is totalized to zero, preserving the exact Ward kernel. -/
theorem xiHorizontalWardGreenCayleyReflectionQuantum_eq_zero_of_onLine
    (q : XiZeroCopy) (hon : (q.1 : ℂ).re = 1 / 2) :
    xiHorizontalWardGreenCayleyReflectionQuantum q = 0 := by
  have him : (xiSpectralPoint q).im = 0 := by
    rw [xiSpectralPoint_im_eq, hon]
    norm_num
  have hgreen : thetaXiWardTransverseGreenWeight q = 0 :=
    (thetaXiWardTransverseGreenWeight_eq_zero_iff q).2 him
  rw [xiHorizontalWardGreenCayleyReflectionQuantum, hgreen, zero_mul]

/-- Open-strip geometry quantizes every off-line normalized Cayley loss above sixteen. -/
theorem sixteen_lt_xiHorizontalWardGreenCayleyReflectionQuantum_of_offLine
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2) :
    16 < xiHorizontalWardGreenCayleyReflectionQuantum q := by
  rw [xiHorizontalWardGreenCayleyReflectionQuantum_eq_of_offLine q hoff]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hx : |2 * (q.1 : ℂ).re - 1| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [hstrip.1, hstrip.2]
  have hxsq : (2 * (q.1 : ℂ).re - 1) ^ 2 < 1 := by
    have hx' := abs_lt.mp hx
    nlinarith
  have hdenpos : 0 < (1 + (2 * (q.1 : ℂ).re - 1) ^ 2) ^ 2 := by positivity
  have hdenlt : (1 + (2 * (q.1 : ℂ).re - 1) ^ 2) ^ 2 < 4 := by
    nlinarith [sq_nonneg (2 * (q.1 : ℂ).re - 1)]
  apply (lt_div_iff₀ hdenpos).2
  nlinarith

/-- Support-level presentation of the same totalized quantum. -/
def xiHorizontalWardGreenCayleySupportQuantum (rho : ℂ) : ℝ :=
  if 2 * rho.re - 1 = 0 then 0
  else 64 / (1 + (2 * rho.re - 1) ^ 2) ^ 2

theorem xiHorizontalWardGreenCayleyReflectionQuantum_eq_support
    (q : XiZeroCopy) :
    xiHorizontalWardGreenCayleyReflectionQuantum q =
      xiHorizontalWardGreenCayleySupportQuantum q.1 := by
  by_cases hoff : (q.1 : ℂ).re = 1 / 2
  · rw [xiHorizontalWardGreenCayleyReflectionQuantum_eq_zero_of_onLine q hoff]
    simp [xiHorizontalWardGreenCayleySupportQuantum, hoff]
  · rw [xiHorizontalWardGreenCayleyReflectionQuantum_eq_of_offLine q hoff]
    have hx : 2 * (q.1 : ℂ).re - 1 ≠ 0 := by
      intro h
      apply hoff
      linarith
    rw [xiHorizontalWardGreenCayleySupportQuantum, if_neg hx]

theorem sixteen_le_xiHorizontalWardGreenCayleySupportQuantum_of_offLine
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    (hoff : rho.re ≠ 1 / 2) :
    16 ≤ xiHorizontalWardGreenCayleySupportQuantum rho := by
  rw [xiHorizontalWardGreenCayleySupportQuantum, if_neg]
  · have hx : |2 * rho.re - 1| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hstrip.1, hstrip.2]
    have hxsq : (2 * rho.re - 1) ^ 2 < 1 := by
      have hx' := abs_lt.mp hx
      nlinarith
    have hdenpos : 0 < (1 + (2 * rho.re - 1) ^ 2) ^ 2 := by positivity
    have hdenle : (1 + (2 * rho.re - 1) ^ 2) ^ 2 ≤ 4 := by
      nlinarith [sq_nonneg (2 * rho.re - 1)]
    apply (le_div_iff₀ hdenpos).2
    nlinarith
  · intro h
    apply hoff
    linarith

/-- Finite-window source-normalized reflection energy, retaining both off-line orientations and
the square of every local divisor multiplicity. -/
def xiStripWindowWardGreenCayleyReflectionEnergy (T : ℝ) : ℝ :=
  ∑ rho ∈ (stripZeros_finite T).toFinset.filter (fun rho => rho.re ≠ 1 / 2),
    (((analyticOrderAt xi rho).toNat : ℝ) ^ 2) *
      xiHorizontalWardGreenCayleySupportQuantum rho

/-- Uniform source quantum defeats spectral collapse: normalized energy dominates sixteen times
the complete canonical reflection charge. -/
theorem sixteen_mul_reflectionCharge_le_wardGreenCayleyEnergy (T : ℝ) :
    16 * (xiReflectionSelfIntersectionCharge T : ℝ) ≤
      xiStripWindowWardGreenCayleyReflectionEnergy T := by
  rw [xiReflectionSelfIntersectionCharge_eq_offLineSquareOrder,
    xiStripWindowOffLineSquareOrder,
    xiStripWindowWardGreenCayleyReflectionEnergy]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro rho hrho
  have hdata := Finset.mem_filter.mp hrho
  have hstrip := ((stripZeros_finite T).mem_toFinset.mp hdata.1).1
  have hquantum :=
    sixteen_le_xiHorizontalWardGreenCayleySupportQuantum_of_offLine
      ⟨hstrip.1, hstrip.2.1⟩ hdata.2
  nlinarith [sq_nonneg ((analyticOrderAt xi rho).toNat : ℝ)]

theorem riemannHypothesis_of_forall_wardGreenCayleyReflectionEnergy_lt_thirtyTwo
    (henergy : ∀ T : ℝ, xiStripWindowWardGreenCayleyReflectionEnergy T < 32) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_forall_reflectionSelfIntersectionCharge_lt_two.mpr
  intro T
  have hlower := sixteen_mul_reflectionCharge_le_wardGreenCayleyEnergy T
  have hlt : (xiReflectionSelfIntersectionCharge T : ℝ) < 2 := by
    nlinarith [henergy T]
  exact_mod_cast hlt

end
end RHTower
