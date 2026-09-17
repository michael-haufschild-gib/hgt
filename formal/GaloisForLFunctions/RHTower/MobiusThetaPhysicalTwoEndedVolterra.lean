import GaloisForLFunctions.RHTower.MobiusThetaComplexSourceToXiLanding
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Two-ended physical Möbius--theta source bridge

Every complete Möbius--theta channel is assembled in the physical source variable before any
spectral point is selected. Its Fourier--Laplace transform is an explicit complete-resolution
multiplier times `XiC`. This module transports that identity to the first-order source equation:
at a vanishing transform, the causal and anti-causal Volterra primitives of the same physical
channel coincide.

The result realizes a Xi zero as a two-ended solution of a target-free physical source equation.
It does not identify that forced solution with an eigenvector of a positive closed operator; that
is the remaining SQB producer step.
-/

open Complex Real MeasureTheory ArithmeticFunction LSeries Set
open scoped BigOperators LSeries.notation Moebius

noncomputable section

namespace RHTower

/-- The two-ended Volterra integrand for a complete physical Möbius--theta channel. -/
def mobiusThetaCompleteVolterraIntegrand
    (K j : ℕ) (w : ℂ) (x t : ℝ) : ℂ :=
  mobiusThetaCompleteLaplaceChannelSource K j t *
    Complex.exp (I * w * ((x : ℂ) - (t : ℂ)))

/-- The Volterra integrand factors through the physical Fourier--Laplace integrand. -/
theorem mobiusThetaCompleteVolterraIntegrand_eq
    (K j : ℕ) (w : ℂ) (x t : ℝ) :
    mobiusThetaCompleteVolterraIntegrand K j w x t =
      Complex.exp (I * w * (x : ℂ)) *
        (Complex.exp (-I * w * (t : ℂ)) *
          mobiusThetaCompleteLaplaceChannelSource K j t) := by
  rw [mobiusThetaCompleteVolterraIntegrand,
    show Complex.exp (I * w * ((x : ℂ) - (t : ℂ))) =
        Complex.exp (I * w * (x : ℂ)) * Complex.exp (-I * w * (t : ℂ)) by
      rw [← Complex.exp_add]
      congr 1
      ring]
  ring

/-- The complete physical Fourier--Laplace integrand is integrable on its common source domain. -/
theorem integrable_mobiusThetaCompleteChannelFourierLaplaceIntegrand
    {K : ℕ} (hK : 3 ≤ K) (j : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hKs : 1 / (K : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Integrable (fun x : ℝ =>
      Complex.exp (-I * w * (x : ℂ)) *
        mobiusThetaCompleteLaplaceChannelSource K j x) := by
  have hinter (x : ℝ) :
      Complex.exp (-I * w * (x : ℂ)) *
          mobiusThetaCompleteLaplaceChannelSource K j x =
        ∑' n : ℕ, mobiusThetaCompleteLaplaceChannelIntegrandTerm K j w n x := by
    rw [mobiusThetaCompleteLaplaceChannelSource, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  refine (GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (fun n => integrable_mobiusThetaCompleteLaplaceChannelIntegrandTerm hw n)
    (summable_integral_norm_mobiusThetaCompleteLaplaceChannelIntegrandTerm
      hK j hw hKs)).congr ?_
  exact Filter.Eventually.of_forall fun x => (hinter x).symm

/-- The physical Volterra integrand is integrable whenever the channel Fourier--Laplace integral
is defined. -/
theorem integrable_mobiusThetaCompleteVolterraIntegrand
    {K : ℕ} (hK : 3 ≤ K) (j : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hKs : 1 / (K : ℝ) < (mobiusThetaCenteredParameter w).re) (x : ℝ) :
    Integrable (mobiusThetaCompleteVolterraIntegrand K j w x) := by
  have hbase := integrable_mobiusThetaCompleteChannelFourierLaplaceIntegrand
    hK j hw hKs
  have hmul := hbase.const_mul (Complex.exp (I * w * (x : ℂ)))
  exact hmul.congr (Filter.Eventually.of_forall fun t =>
    (mobiusThetaCompleteVolterraIntegrand_eq K j w x t).symm)

/-- Causal source-pointed primitive of the complete physical channel. -/
def mobiusThetaCompleteCausalVolterra (K j : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  -I * ∫ t in Iic x, mobiusThetaCompleteVolterraIntegrand K j w x t

/-- Anti-causal source-pointed primitive of the complete physical channel. -/
def mobiusThetaCompleteAntiCausalVolterra (K j : ℕ) (w : ℂ) (x : ℝ) : ℂ :=
  I * ∫ t in Ici x, mobiusThetaCompleteVolterraIntegrand K j w x t

/-- The causal-minus-anti-causal defect is the physical channel transform, multiplied by its free
mode. -/
theorem mobiusThetaCompleteCausalVolterra_sub_antiCausal
    {K : ℕ} (hK : 3 ≤ K) (j : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hKs : 1 / (K : ℝ) < (mobiusThetaCenteredParameter w).re) (x : ℝ) :
    mobiusThetaCompleteCausalVolterra K j w x -
      mobiusThetaCompleteAntiCausalVolterra K j w x =
      -I * Complex.exp (I * w * (x : ℂ)) *
        mobiusThetaCompleteChannelFourierLaplace K j w := by
  have hint := integrable_mobiusThetaCompleteVolterraIntegrand hK j hw hKs x
  have hIci : (∫ t in Ici x, mobiusThetaCompleteVolterraIntegrand K j w x t) =
      ∫ t in Ioi x, mobiusThetaCompleteVolterraIntegrand K j w x t :=
    MeasureTheory.integral_Ici_eq_integral_Ioi
  have hsplit : (∫ t in Iic x, mobiusThetaCompleteVolterraIntegrand K j w x t) +
      (∫ t in Ioi x, mobiusThetaCompleteVolterraIntegrand K j w x t) =
      ∫ t : ℝ, mobiusThetaCompleteVolterraIntegrand K j w x t :=
    intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn
  have hfull : (∫ t : ℝ, mobiusThetaCompleteVolterraIntegrand K j w x t) =
      Complex.exp (I * w * (x : ℂ)) *
        mobiusThetaCompleteChannelFourierLaplace K j w := by
    have hrw : (∫ t : ℝ, mobiusThetaCompleteVolterraIntegrand K j w x t) =
        Complex.exp (I * w * (x : ℂ)) *
          ∫ t : ℝ, Complex.exp (-I * w * (t : ℂ)) *
            mobiusThetaCompleteLaplaceChannelSource K j t := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t =>
        mobiusThetaCompleteVolterraIntegrand_eq K j w x t
    exact hrw
  rw [mobiusThetaCompleteCausalVolterra, mobiusThetaCompleteAntiCausalVolterra, hIci]
  have hcombine :
      (-I * ∫ t in Iic x, mobiusThetaCompleteVolterraIntegrand K j w x t) -
        I * (∫ t in Ioi x, mobiusThetaCompleteVolterraIntegrand K j w x t) =
      -I * ((∫ t in Iic x, mobiusThetaCompleteVolterraIntegrand K j w x t) +
        ∫ t in Ioi x, mobiusThetaCompleteVolterraIntegrand K j w x t) := by
    ring
  rw [hcombine, hsplit, hfull]
  ring

/-- At every `XiC` zero, each target-free complete physical channel has one two-ended Volterra
primitive. -/
theorem mobiusThetaCompleteCausalVolterra_eq_antiCausal_of_XiC_eq_zero
    {K : ℕ} (hK : 3 ≤ K) (j : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hKs : 1 / (K : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hzero : XiC w = 0) (x : ℝ) :
    mobiusThetaCompleteCausalVolterra K j w x =
      mobiusThetaCompleteAntiCausalVolterra K j w x := by
  have hdefect := mobiusThetaCompleteCausalVolterra_sub_antiCausal hK j hw hKs x
  rw [mobiusThetaCompleteChannelFourierLaplace_eq_zero_of_XiC_eq_zero
    hK j hw hKs hzero, mul_zero] at hdefect
  exact sub_eq_zero.mp hdefect

end RHTower
