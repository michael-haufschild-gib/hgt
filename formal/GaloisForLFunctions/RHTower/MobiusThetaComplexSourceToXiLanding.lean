import GaloisForLFunctions.RHTower.MFreeLadder
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFourierLaplace
import GaloisForLFunctions.RHTower.CompletePositiveKolchinFreeRiemannResolution
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Complex physical Möbius--theta source-to-Xi landing

This module constructs the source before spectral evaluation.  Its `m`-th rung is the pointwise
sum of the canonical theta-cusp source translated by every integer logarithmic label and weighted
by the half-density `m`-power-supported Möbius coefficient.  Absolute Bochner convergence permits
the Fourier--Laplace integral and source sum to be interchanged.

The capstone identifies the resulting transform throughout its honest complex convergence domain:

`FL(Psi_m)(w) = zeta(m (1/2 + I*w))⁻¹ * XiC(w)`.

Neither the source nor its convergence proof mentions a zero or inserts `XiC` as a scalar.  This is
the unconditional complex source-to-Xi landing needed before Route R's still-open Ward/Hodge sign.
-/

open Complex Real MeasureTheory ArithmeticFunction LSeries Set
open scoped BigOperators LSeries.notation Moebius

noncomputable section
namespace RHTower

/-- Centered conversion from Xi frequency to the classical zeta coordinate. -/
def mobiusThetaCenteredParameter (w : ℂ) : ℂ :=
  1 / 2 + I * w

/-- One target-free physical source term: an arithmetic half-density times a logarithmic translate
of the full theta-cusp source. -/
def mobiusThetaLaplaceSourceTerm (m n : ℕ) (x : ℝ) : ℂ :=
  LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ))) (1 / 2 : ℂ) n *
    (thetaCuspFullSource (x - Real.log n) : ℂ)

/-- Physical high-exponent Möbius--theta source rung. -/
def mobiusThetaLaplaceSource (m : ℕ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, mobiusThetaLaplaceSourceTerm m n x

/-- Fourier--Laplace integrand of one physical arithmetic translate. -/
def mobiusThetaLaplaceIntegrandTerm (m : ℕ) (w : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (-I * w * (x : ℂ)) * mobiusThetaLaplaceSourceTerm m n x

/-- Fourier--Laplace transform of the synthesized physical source. -/
def mobiusThetaFourierLaplace (m : ℕ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-I * w * (x : ℂ)) * mobiusThetaLaplaceSource m x

/-- Translation character promotes a half-density Dirichlet term to the centered complex
Dirichlet parameter. -/
theorem LSeries_term_half_mul_exp_neg_I_mul_log
    (f : ℕ → ℂ) (n : ℕ) (w : ℂ) :
    LSeries.term f (1 / 2 : ℂ) n *
        Complex.exp (-I * w * (Real.log n : ℂ)) =
      LSeries.term f (mobiusThetaCenteredParameter w) n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  have hpow : Complex.exp (-I * w * (Real.log n : ℂ)) =
      (n : ℂ) ^ (-I * w) := by
    rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
    change Complex.exp (-I * w * (Real.log (n : ℝ) : ℂ)) =
      Complex.exp (Complex.log ((n : ℝ) : ℂ) * (-I * w))
    rw [← Complex.ofReal_log hnpos.le]
    congr 1
    ring
  rw [hpow]
  rw [show -I * w = -(I * w) by ring, Complex.cpow_neg]
  rw [mobiusThetaCenteredParameter,
    Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- A translated source integrand is exactly the centered Dirichlet coefficient times a translate
of the canonical theta Fourier--Laplace integrand. -/
theorem mobiusThetaLaplaceIntegrandTerm_eq
    (m : ℕ) (w : ℂ) (n : ℕ) (x : ℝ) :
    mobiusThetaLaplaceIntegrandTerm m w n x =
      LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ)))
          (mobiusThetaCenteredParameter w) n *
        thetaCuspFourierLaplaceIntegrand w (x - Real.log n) := by
  rw [mobiusThetaLaplaceIntegrandTerm, mobiusThetaLaplaceSourceTerm,
    thetaCuspFourierLaplaceIntegrand]
  rw [show Complex.exp (-I * w * (x : ℂ)) =
      Complex.exp (-I * w * (Real.log n : ℂ)) *
        Complex.exp (-I * w * ((x - Real.log n : ℝ) : ℂ)) by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring]
  rw [← LSeries_term_half_mul_exp_neg_I_mul_log]
  ring

theorem integrable_mobiusThetaLaplaceIntegrandTerm
    {m : ℕ} {w : ℂ} (hw : |w.im| < 1) (n : ℕ) :
    Integrable (mobiusThetaLaplaceIntegrandTerm m w n) := by
  rw [show mobiusThetaLaplaceIntegrandTerm m w n =
      fun x : ℝ =>
        LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ)))
            (mobiusThetaCenteredParameter w) n *
          thetaCuspFourierLaplaceIntegrand w (x - Real.log n) by
    funext x
    exact mobiusThetaLaplaceIntegrandTerm_eq m w n x]
  exact ((integrable_thetaCuspFourierLaplaceIntegrand hw).comp_add_right
    (-Real.log n)).const_mul _

theorem integral_norm_mobiusThetaLaplaceIntegrandTerm
    {m : ℕ} {w : ℂ} (n : ℕ) :
    ∫ x : ℝ, ‖mobiusThetaLaplaceIntegrandTerm m w n x‖ =
      ‖LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ)))
          (mobiusThetaCenteredParameter w) n‖ *
        ∫ x : ℝ, ‖thetaCuspFourierLaplaceIntegrand w x‖ := by
  simp_rw [mobiusThetaLaplaceIntegrandTerm_eq, norm_mul]
  rw [integral_const_mul]
  congr 1
  simpa only [sub_eq_add_neg] using
    (integral_add_right_eq_self
      (fun x : ℝ => ‖thetaCuspFourierLaplaceIntegrand w x‖) (-Real.log n))

theorem summable_integral_norm_mobiusThetaLaplaceIntegrandTerm
    {m : ℕ} (hm : m ≠ 0) {w : ℂ}
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Summable (fun n : ℕ =>
      ∫ x : ℝ, ‖mobiusThetaLaplaceIntegrandTerm m w n x‖) := by
  have hcoeff := LSeriesSummable_mPart_moebius hm hms
  unfold LSeriesSummable at hcoeff
  simpa only [integral_norm_mobiusThetaLaplaceIntegrandTerm] using
    hcoeff.norm.mul_right
      (∫ x : ℝ, ‖thetaCuspFourierLaplaceIntegrand w x‖)

theorem integral_mobiusThetaLaplaceIntegrandTerm
    {m : ℕ} {w : ℂ} (hw : |w.im| < 1) (n : ℕ) :
    ∫ x : ℝ, mobiusThetaLaplaceIntegrandTerm m w n x =
      LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ)))
          (mobiusThetaCenteredParameter w) n * XiC w := by
  simp_rw [mobiusThetaLaplaceIntegrandTerm_eq]
  rw [integral_const_mul]
  rw [show (∫ x : ℝ, thetaCuspFourierLaplaceIntegrand w (x - Real.log n)) =
      ∫ x : ℝ, thetaCuspFourierLaplaceIntegrand w x by
    simpa only [sub_eq_add_neg] using
      (integral_add_right_eq_self
        (thetaCuspFourierLaplaceIntegrand w) (-Real.log n))]
  rw [← thetaCuspFourierLaplace]
  rw [thetaCuspFourierLaplace_eq_XiC_on_strip]
  simpa [thetaCuspFourierLaplaceStrip] using (abs_lt.mp hw)

/-- **Unconditional complex physical source-to-Xi landing.**  In the joint theta strip and
Möbius absolute-convergence half-plane, the Fourier--Laplace transform of the source synthesized
before evaluation is the full Xi function times the reciprocal high-exponent zeta factor. -/
theorem mobiusThetaFourierLaplace_eq_invZeta_mul_XiC
    {m : ℕ} (hm : m ≠ 0) {w : ℂ} (hw : |w.im| < 1)
    (hms : 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re) :
    mobiusThetaFourierLaplace m w =
      (riemannZeta ((m : ℂ) * mobiusThetaCenteredParameter w))⁻¹ * XiC w := by
  unfold mobiusThetaFourierLaplace mobiusThetaLaplaceSource
  have hinter (x : ℝ) :
      Complex.exp (-I * w * (x : ℂ)) *
          (∑' n : ℕ, mobiusThetaLaplaceSourceTerm m n x) =
        ∑' n : ℕ, mobiusThetaLaplaceIntegrandTerm m w n x := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  simp_rw [hinter]
  rw [← integral_tsum_of_summable_integral_norm
    (fun n => integrable_mobiusThetaLaplaceIntegrandTerm hw n)
    (summable_integral_norm_mobiusThetaLaplaceIntegrandTerm hm hms)]
  rw [show (∑' n : ℕ, ∫ x : ℝ, mobiusThetaLaplaceIntegrandTerm m w n x) =
      ∑' n : ℕ,
        LSeries.term (↗(mPart m (μ : ArithmeticFunction ℤ)))
            (mobiusThetaCenteredParameter w) n * XiC w by
    apply tsum_congr
    intro n
    exact integral_mobiusThetaLaplaceIntegrandTerm hw n]
  rw [tsum_mul_right]
  change LSeries (↗(mPart m (μ : ArithmeticFunction ℤ)))
      (mobiusThetaCenteredParameter w) * XiC w = _
  rw [LSeries_mPart_moebius hm hms]

/-! ## Complete physical channel before scalarization -/

/-- One term of the complete physical source channel.  The head is the first rung and every
successor is formed by subtracting adjacent physical terms before summation or transform. -/
def mobiusThetaCompleteLaplaceChannelTerm
    (K : ℕ) : ℕ → ℕ → ℝ → ℂ
  | 0 => mobiusThetaLaplaceSourceTerm K
  | j + 1 => fun n x =>
      mobiusThetaLaplaceSourceTerm (K + j + 1) n x -
        mobiusThetaLaplaceSourceTerm (K + j) n x

/-- Target-free complete channel synthesized in the physical source variable. -/
def mobiusThetaCompleteLaplaceChannelSource (K j : ℕ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, mobiusThetaCompleteLaplaceChannelTerm K j n x

/-- One Fourier--Laplace integrand term of a complete physical channel. -/
def mobiusThetaCompleteLaplaceChannelIntegrandTerm
    (K j : ℕ) (w : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (-I * w * (x : ℂ)) *
    mobiusThetaCompleteLaplaceChannelTerm K j n x

/-- Actual Fourier--Laplace transform of a complete physical channel. -/
def mobiusThetaCompleteChannelFourierLaplace (K j : ℕ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, Complex.exp (-I * w * (x : ℂ)) *
    mobiusThetaCompleteLaplaceChannelSource K j x

theorem mobiusTheta_commonDomain_of_le
    {K m : ℕ} (hK : 0 < K) (hKm : K ≤ m) {w : ℂ}
    (hKs : 1 / (K : ℝ) < (mobiusThetaCenteredParameter w).re) :
    1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hmpos : (0 : ℝ) < m := by exact_mod_cast lt_of_lt_of_le hK hKm
  have hcast : (K : ℝ) ≤ m := by exact_mod_cast hKm
  have hspos : 0 < (mobiusThetaCenteredParameter w).re :=
    lt_trans (one_div_pos.mpr hKpos) hKs
  have hbase : 1 < (mobiusThetaCenteredParameter w).re * (K : ℝ) :=
    (div_lt_iff₀ hKpos).mp hKs
  apply (div_lt_iff₀ hmpos).mpr
  exact hbase.trans_le (mul_le_mul_of_nonneg_left hcast hspos.le)

theorem integrable_mobiusThetaCompleteLaplaceChannelIntegrandTerm
    {K j : ℕ} {w : ℂ} (hw : |w.im| < 1) (n : ℕ) :
    Integrable (mobiusThetaCompleteLaplaceChannelIntegrandTerm K j w n) := by
  cases j with
  | zero =>
      rw [show mobiusThetaCompleteLaplaceChannelIntegrandTerm K 0 w n =
          mobiusThetaLaplaceIntegrandTerm K w n by
        funext x
        rfl]
      exact integrable_mobiusThetaLaplaceIntegrandTerm hw n
  | succ j =>
      have hleft := integrable_mobiusThetaLaplaceIntegrandTerm
        (m := K + j + 1) hw n
      have hright := integrable_mobiusThetaLaplaceIntegrandTerm
        (m := K + j) hw n
      rw [show mobiusThetaCompleteLaplaceChannelIntegrandTerm K (j + 1) w n =
          mobiusThetaLaplaceIntegrandTerm (K + j + 1) w n -
            mobiusThetaLaplaceIntegrandTerm (K + j) w n by
        funext x
        simp [mobiusThetaCompleteLaplaceChannelIntegrandTerm,
          mobiusThetaCompleteLaplaceChannelTerm,
          mobiusThetaLaplaceIntegrandTerm, mul_sub]]
      exact hleft.sub hright

theorem summable_integral_norm_mobiusThetaCompleteLaplaceChannelIntegrandTerm
    {K : ℕ} (hK : 3 ≤ K) (j : ℕ) {w : ℂ}
    (hw : |w.im| < 1)
    (hKs : 1 / (K : ℝ) < (mobiusThetaCenteredParameter w).re) :
    Summable (fun n : ℕ =>
      ∫ x : ℝ, ‖mobiusThetaCompleteLaplaceChannelIntegrandTerm K j w n x‖) := by
  cases j with
  | zero =>
      simpa [mobiusThetaCompleteLaplaceChannelIntegrandTerm,
        mobiusThetaCompleteLaplaceChannelTerm,
        mobiusThetaLaplaceIntegrandTerm] using
        (summable_integral_norm_mobiusThetaLaplaceIntegrandTerm
          (m := K) (by omega) hKs)
  | succ j =>
      have hleft := summable_integral_norm_mobiusThetaLaplaceIntegrandTerm
        (m := K + j + 1) (by omega)
        (mobiusTheta_commonDomain_of_le (by omega : 0 < K) (by omega) hKs)
      have hright := summable_integral_norm_mobiusThetaLaplaceIntegrandTerm
        (m := K + j) (by omega)
        (mobiusTheta_commonDomain_of_le (by omega : 0 < K) (by omega) hKs)
      refine Summable.of_nonneg_of_le
        (fun n => integral_nonneg fun _ => norm_nonneg _)
        (fun n => ?_) (hleft.add hright)
      have hleftInt := integrable_mobiusThetaLaplaceIntegrandTerm
        (m := K + j + 1) hw n
      have hrightInt := integrable_mobiusThetaLaplaceIntegrandTerm
        (m := K + j) hw n
      calc
        (∫ x : ℝ,
            ‖mobiusThetaCompleteLaplaceChannelIntegrandTerm K (j + 1) w n x‖)
            ≤ ∫ x : ℝ,
                (‖mobiusThetaLaplaceIntegrandTerm (K + j + 1) w n x‖ +
                  ‖mobiusThetaLaplaceIntegrandTerm (K + j) w n x‖) := by
              refine integral_mono_ae
                (integrable_mobiusThetaCompleteLaplaceChannelIntegrandTerm
                  (K := K) (j := j + 1) hw n).norm
                (hleftInt.norm.add hrightInt.norm) (ae_of_all _ fun x => ?_)
              simpa [mobiusThetaCompleteLaplaceChannelIntegrandTerm,
                mobiusThetaCompleteLaplaceChannelTerm,
                mobiusThetaLaplaceIntegrandTerm, mul_sub] using
                norm_sub_le
                  (mobiusThetaLaplaceIntegrandTerm (K + j + 1) w n x)
                  (mobiusThetaLaplaceIntegrandTerm (K + j) w n x)
        _ = (∫ x : ℝ, ‖mobiusThetaLaplaceIntegrandTerm (K + j + 1) w n x‖) +
              ∫ x : ℝ, ‖mobiusThetaLaplaceIntegrandTerm (K + j) w n x‖ := by
              rw [integral_add hleftInt.norm hrightInt.norm]

theorem integral_mobiusThetaCompleteLaplaceChannelIntegrandTerm
    {K j : ℕ} {w : ℂ} (hw : |w.im| < 1) (n : ℕ) :
    ∫ x : ℝ, mobiusThetaCompleteLaplaceChannelIntegrandTerm K j w n x =
      match j with
      | 0 =>
          LSeries.term (↗(mPart K (μ : ArithmeticFunction ℤ)))
              (mobiusThetaCenteredParameter w) n * XiC w
      | j + 1 =>
          (LSeries.term (↗(mPart (K + j + 1) (μ : ArithmeticFunction ℤ)))
                (mobiusThetaCenteredParameter w) n -
            LSeries.term (↗(mPart (K + j) (μ : ArithmeticFunction ℤ)))
                (mobiusThetaCenteredParameter w) n) * XiC w := by
  cases j with
  | zero =>
      simpa [mobiusThetaCompleteLaplaceChannelIntegrandTerm,
        mobiusThetaCompleteLaplaceChannelTerm,
        mobiusThetaLaplaceIntegrandTerm] using
        (integral_mobiusThetaLaplaceIntegrandTerm (m := K) hw n)
  | succ j =>
      have hleft := integrable_mobiusThetaLaplaceIntegrandTerm
        (m := K + j + 1) hw n
      have hright := integrable_mobiusThetaLaplaceIntegrandTerm
        (m := K + j) hw n
      rw [show mobiusThetaCompleteLaplaceChannelIntegrandTerm K (j + 1) w n =
          fun x : ℝ =>
            mobiusThetaLaplaceIntegrandTerm (K + j + 1) w n x -
              mobiusThetaLaplaceIntegrandTerm (K + j) w n x by
        funext x
        simp [mobiusThetaCompleteLaplaceChannelIntegrandTerm,
          mobiusThetaCompleteLaplaceChannelTerm,
          mobiusThetaLaplaceIntegrandTerm, mul_sub]]
      rw [integral_sub hleft hright,
        integral_mobiusThetaLaplaceIntegrandTerm hw,
        integral_mobiusThetaLaplaceIntegrandTerm hw]
      ring

/-- **Unconditional complete physical source-to-Xi landing.**  Each coordinate is synthesized
termwise in the source variable before transform.  On the common convergence domain, its actual
Fourier--Laplace integral is the common Xi divisor times the corresponding complete-resolution
multiplier. -/
theorem mobiusThetaCompleteChannelFourierLaplace_eq
    {K : ℕ} (hK : 3 ≤ K) (j : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hKs : 1 / (K : ℝ) < (mobiusThetaCenteredParameter w).re) :
    mobiusThetaCompleteChannelFourierLaplace K j w =
      completeResolutionMultiplier K j (mobiusThetaCenteredParameter w) * XiC w := by
  unfold mobiusThetaCompleteChannelFourierLaplace
    mobiusThetaCompleteLaplaceChannelSource
  have hinter (x : ℝ) :
      Complex.exp (-I * w * (x : ℂ)) *
          (∑' n : ℕ, mobiusThetaCompleteLaplaceChannelTerm K j n x) =
        ∑' n : ℕ, mobiusThetaCompleteLaplaceChannelIntegrandTerm K j w n x := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    rfl
  simp_rw [hinter]
  rw [← integral_tsum_of_summable_integral_norm
    (fun n => integrable_mobiusThetaCompleteLaplaceChannelIntegrandTerm hw n)
    (summable_integral_norm_mobiusThetaCompleteLaplaceChannelIntegrandTerm
      hK j hw hKs)]
  cases j with
  | zero =>
      simp_rw [integral_mobiusThetaCompleteLaplaceChannelIntegrandTerm hw]
      rw [tsum_mul_right]
      change LSeries (↗(mPart K (μ : ArithmeticFunction ℤ)))
          (mobiusThetaCenteredParameter w) * XiC w = _
      rw [LSeries_mPart_moebius (by omega : K ≠ 0) hKs]
      rfl
  | succ j =>
      simp_rw [integral_mobiusThetaCompleteLaplaceChannelIntegrandTerm hw]
      have hleft : Summable (LSeries.term
          (↗(mPart (K + j + 1) (μ : ArithmeticFunction ℤ)))
          (mobiusThetaCenteredParameter w)) :=
        LSeriesSummable_mPart_moebius (by omega)
          (mobiusTheta_commonDomain_of_le (by omega : 0 < K) (by omega) hKs)
      have hright : Summable (LSeries.term
          (↗(mPart (K + j) (μ : ArithmeticFunction ℤ)))
          (mobiusThetaCenteredParameter w)) :=
        LSeriesSummable_mPart_moebius (by omega)
          (mobiusTheta_commonDomain_of_le (by omega : 0 < K) (by omega) hKs)
      rw [tsum_mul_right, hleft.tsum_sub hright]
      change
        (LSeries (↗(mPart (K + j + 1) (μ : ArithmeticFunction ℤ)))
            (mobiusThetaCenteredParameter w) -
          LSeries (↗(mPart (K + j) (μ : ArithmeticFunction ℤ)))
            (mobiusThetaCenteredParameter w)) * XiC w = _
      rw [LSeries_mPart_moebius (by omega)
          (mobiusTheta_commonDomain_of_le (by omega : 0 < K) (by omega) hKs),
        LSeries_mPart_moebius (by omega)
          (mobiusTheta_commonDomain_of_le (by omega : 0 < K) (by omega) hKs)]
      simp only [completeResolutionMultiplier, shellMultiplier]
      push_cast
      ring

/-- Every coordinate of the physical complete channel vanishes on an Xi zero fibre, with no zero
used in the construction of the source. -/
theorem mobiusThetaCompleteChannelFourierLaplace_eq_zero_of_XiC_eq_zero
    {K : ℕ} (hK : 3 ≤ K) (j : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hKs : 1 / (K : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hzero : XiC w = 0) :
    mobiusThetaCompleteChannelFourierLaplace K j w = 0 := by
  rw [mobiusThetaCompleteChannelFourierLaplace_eq hK j hw hKs, hzero, mul_zero]

end RHTower
