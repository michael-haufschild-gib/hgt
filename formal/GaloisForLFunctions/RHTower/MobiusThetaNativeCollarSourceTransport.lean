import GaloisForLFunctions.RHTower.MobiusThetaRawSourceModulation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspTiltedSchwartz
import GaloisForLFunctions.RHTower.Deninger.DeningerMobiusPreimage
import GaloisForLFunctions.RHTower.Deninger.DeningerCollarExchange

/-!
# Native logarithmic collar of the complete raw theta source

The original internally promoted theta source is transported to a genuine Schwartz
collar before selecting any spectral point. Its canonical Mobius preimage reconstructs
all original raw arithmetic packets, with half-density and finite prime prefix retained.
Absolute pointwise admission holds at every native honest depth.

The existing collar exchange produces the character `(-1)^k exp((m-1)t)`.
The source Mellin parameter is `m*s(v)` and its Jacobian is `1/m`. This is an actual
source-coordinate comparison, not full Gamma/BV reader agreement: strong Meyer
admission, the Fourier collar and the fixed physical reader still need comparison.
-/

set_option autoImplicit false
open Complex Real MeasureTheory ArithmeticFunction LSeries
open scoped Moebius LSeries.notation SchwartzMap
noncomputable section
namespace RHTower

private def nativeScale (m : ℕ+) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 (-(m : ℝ))
    (neg_ne_zero.mpr (by exact_mod_cast m.ne_zero)))

/-- Original internal theta jet, transported to the native logarithmic collar with its
half-density. No spectral point or divisor is used in this source. -/
def mobiusThetaNativeCollarSource (k : ℕ) (m : ℕ+) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (nativeScale m)
    (SchwartzMap.smulLeftCLM ℂ (fun u : ℝ => (-I * (u : ℂ)) ^ k)
      (thetaCuspTiltedSchwartz (1 / 2) (by norm_num)))

theorem mobiusThetaNativeCollarSource_apply (k : ℕ) (m : ℕ+) (t : ℝ) :
    mobiusThetaNativeCollarSource k m t =
      (Real.exp (-(m : ℝ) * t / 2) : ℂ) *
        (-I * ((-(m : ℝ) * t : ℝ) : ℂ)) ^ k *
          (thetaCuspFullSource (-(m : ℝ) * t) : ℂ) := by
  change SchwartzMap.smulLeftCLM ℂ (fun u : ℝ => (-I * (u : ℂ)) ^ k)
      (thetaCuspTiltedSchwartz (1 / 2) _) (-(m : ℝ) * t) = _
  rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), thetaCuspTiltedSchwartz_apply]
  rw [show (1 / 2 : ℝ) * (-(m : ℝ) * t) = -(m : ℝ) * t / 2 by ring]
  simp only [smul_eq_mul, Complex.ofReal_mul]
  ring

/-- The existing collar exchange retains the native depth correction. -/
theorem mobiusThetaNativeCollarSource_collar (k : ℕ) (m : ℕ+) (t : ℝ) :
    deningerCollarFun (mobiusThetaNativeCollarSource k m) t =
      (-1 : ℂ) ^ k * (Real.exp (((m : ℝ) - 1) * t) : ℂ) *
        mobiusThetaNativeCollarSource k m t := by
  rw [deningerCollarFun, deningerCollarWeight,
    mobiusThetaNativeCollarSource_apply, mobiusThetaNativeCollarSource_apply]
  rw [show -(m : ℝ) * -t = -(-(m : ℝ) * t) by ring,
    thetaCuspFullSource_neg]
  have hp : (-I * ((-(-(m : ℝ) * t) : ℝ) : ℂ)) ^ k =
      (-1 : ℂ) ^ k * (-I * ((-(m : ℝ) * t : ℝ) : ℂ)) ^ k := by
    rw [← mul_pow]
    congr 1
    push_cast
    ring
  rw [hp]
  have he : (Real.exp (-t) : ℂ) * (Real.exp (-(-(m : ℝ) * t) / 2) : ℂ) =
      (Real.exp (((m : ℝ) - 1) * t) : ℂ) *
        (Real.exp (-(m : ℝ) * t / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  linear_combination he * ((-1 : ℂ) ^ k *
    (-I * ((-(m : ℝ) * t : ℝ) : ℂ)) ^ k *
      (thetaCuspFullSource (-(m : ℝ) * t) : ℂ))

private theorem rawHalfCoefficient (m n : ℕ) :
    LSeries.term (↗(μ : ArithmeticFunction ℤ)) ((m : ℂ) / 2) n =
      ((moebius n : ℤ) : ℂ) * (Real.exp (-(m : ℝ) * Real.log n / 2) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero
    (Nat.cast_ne_zero.mpr hn), div_eq_mul_inv, ← Complex.exp_neg]
  change ((moebius n : ℤ) : ℂ) *
    Complex.exp (-(Complex.log ((n : ℝ) : ℂ) * ((m : ℂ) / 2))) = _
  rw [← Complex.ofReal_log hnpos.le, Complex.ofReal_exp]
  congr 1
  congr 1
  push_cast
  ring

/-- Literal Mobius inversion summand, with original coordinate and half-density retained. -/
theorem mobiusThetaNativeCollarSource_mobiusTerm
    (k n : ℕ) (m : ℕ+) (x : ℝ) :
    ((moebius n : ℤ) : ℂ) * deningerLogPull (mobiusThetaNativeCollarSource k m)
        ((n : ℝ) * Real.exp (-x / (m : ℝ))) =
      (Real.exp (x / 2) : ℂ) * mobiusThetaInternalJetRawHeadSource k n m x := by
  by_cases hn : n = 0
  · subst n
    simp [mobiusThetaInternalJetRawHeadSource]
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast m.ne_zero
  rw [deningerLogPull_apply, Real.log_mul hnpos.ne' (Real.exp_pos _).ne',
    Real.log_exp, mobiusThetaNativeCollarSource_apply,
    mobiusThetaInternalJetRawHeadSource, rawHalfCoefficient]
  have hx : -(m : ℝ) * (Real.log n + -x / (m : ℝ)) =
      x - (m : ℝ) * Real.log n := by
    field_simp
    ring
  rw [hx]
  have he : (Real.exp ((x - (m : ℝ) * Real.log n) / 2) : ℂ) =
      (Real.exp (x / 2) : ℂ) *
        (Real.exp (-(m : ℝ) * Real.log n / 2) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [he]
  ring

/-- Complete original tail, without changing its prime anchor or dropping arithmetic terms. -/
theorem mobiusThetaNativeCollarSource_tail_reconstruction
    (k p : ℕ) (m : ℕ+) (x : ℝ) :
    (∑' j : ℕ, ((moebius (p + j) : ℤ) : ℂ) *
      deningerLogPull (mobiusThetaNativeCollarSource k m)
        (((p + j : ℕ) : ℝ) * Real.exp (-x / (m : ℝ)))) =
      (Real.exp (x / 2) : ℂ) * mobiusThetaInternalJetRawResidualSource k p m x := by
  simp_rw [mobiusThetaNativeCollarSource_mobiusTerm]
  rw [tsum_mul_left]
  rfl

/-- The existing canonical all-integer preimage reconstructs the complete raw source. -/
theorem mobiusThetaNativeCollarSource_preimage
    (k : ℕ) (m : ℕ+) (x : ℝ) :
    deningerMobiusPreimage (mobiusThetaNativeCollarSource k m)
        (Real.exp (-x / (m : ℝ))) =
      (Real.exp (x / 2) : ℂ) * mobiusThetaInternalJetRawResidualSource k 0 m x := by
  simpa only [deningerMobiusPreimage, Nat.zero_add] using
    mobiusThetaNativeCollarSource_tail_reconstruction k 0 m x

/-- Absolute pointwise admission of every original raw arithmetic tail at honest depth. -/
theorem summable_norm_mobiusThetaInternalJetRawHeadSource
    (k p : ℕ) (m : ℕ+) (hm : 3 ≤ (m : ℕ)) (x : ℝ) :
    Summable (fun j : ℕ => ‖mobiusThetaInternalJetRawHeadSource k (p + j) m x‖) := by
  have hs : LSeriesSummable (↗(μ : ArithmeticFunction ℤ)) ((m : ℂ) / 2) := by
    apply LSeriesSummable_moebius_iff.mpr
    have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    simp only [Complex.div_ofNat_re, Complex.natCast_re]
    linarith
  have ht : Summable (fun j : ℕ =>
      ‖LSeries.term (↗(μ : ArithmeticFunction ℤ)) ((m : ℂ) / 2) (p + j)‖) := by
    simpa only [Nat.add_comm] using (_root_.summable_nat_add_iff p).2 hs.norm
  let C := SchwartzMap.seminorm ℝ k 0 thetaCuspSchwartz
  apply (ht.mul_right C).of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
  have hb := SchwartzMap.norm_pow_mul_le_seminorm ℝ thetaCuspSchwartz k
    (x - (m : ℝ) * Real.log ((p + j : ℕ) : ℝ))
  have hb' : ‖(-I * ((x - (m : ℝ) * Real.log ((p + j : ℕ) : ℝ) : ℝ) : ℂ)) ^ k *
      (thetaCuspFullSource (x - (m : ℝ) * Real.log ((p + j : ℕ) : ℝ)) : ℂ)‖ ≤ C := by
    simpa only [C, thetaCuspSchwartz_apply, norm_mul, norm_pow, norm_neg,
      Complex.norm_I, one_mul, Complex.norm_real] using hb
  rw [mobiusThetaInternalJetRawHeadSource, mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_left hb' (norm_nonneg _)

/-- Absolute admission accompanies the transported infinite source; no use of a default
value of a divergent `tsum` is needed at native honest depths. -/
theorem summable_norm_mobiusThetaNativeCollarSource_tail
    (k p : ℕ) (m : ℕ+) (hm : 3 ≤ (m : ℕ)) (x : ℝ) :
    Summable (fun j : ℕ => ‖((moebius (p + j) : ℤ) : ℂ) *
      deningerLogPull (mobiusThetaNativeCollarSource k m)
        (((p + j : ℕ) : ℝ) * Real.exp (-x / (m : ℝ)))‖) := by
  simp_rw [mobiusThetaNativeCollarSource_mobiusTerm, norm_mul]
  exact (summable_norm_mobiusThetaInternalJetRawHeadSource k p m hm x).mul_left _

/-- The original prime prefix is retained when the full canonical inverse is used. -/
theorem mobiusThetaNativeCollarSource_preimage_at_anchor
    (k p : ℕ) (m : ℕ+) (hm : 3 ≤ (m : ℕ)) (x : ℝ) :
    deningerMobiusPreimage (mobiusThetaNativeCollarSource k m)
        (Real.exp (-x / (m : ℝ))) =
      (Real.exp (x / 2) : ℂ) *
        ((∑ n ∈ Finset.range p, mobiusThetaInternalJetRawHeadSource k n m x) +
          mobiusThetaInternalJetRawResidualSource k p m x) := by
  have hs : Summable (fun n : ℕ => mobiusThetaInternalJetRawHeadSource k n m x) := by
    simpa only [Nat.zero_add] using
      (summable_norm_mobiusThetaInternalJetRawHeadSource k 0 m hm x).of_norm
  rw [mobiusThetaNativeCollarSource_preimage]
  congr 1
  simpa only [mobiusThetaInternalJetRawResidualSource, Nat.zero_add, Nat.add_zero, Nat.add_comm]
    using (hs.sum_add_tsum_nat_add p).symm

/-- The transported source has the actual native Mellin parameter `m*s(v)`.
Both absolute admission and the Jacobian `1/m` are retained. -/
theorem mobiusThetaNativeCollarSource_mellin_data
    (k : ℕ) (m : ℕ+) {v : ℂ} (hv : |v.im| < 1) :
    Integrable (fun t : ℝ =>
      Complex.exp (((m : ℂ) * mobiusThetaCenteredParameter v) * (t : ℂ)) *
        mobiusThetaNativeCollarSource k m t) ∧
    (∫ t : ℝ,
      Complex.exp (((m : ℂ) * mobiusThetaCenteredParameter v) * (t : ℂ)) *
        mobiusThetaNativeCollarSource k m t) =
      (m : ℂ)⁻¹ * iteratedDeriv k XiC v := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast m.pos
  have hf : (fun t : ℝ =>
      Complex.exp (((m : ℂ) * mobiusThetaCenteredParameter v) * (t : ℂ)) *
        mobiusThetaNativeCollarSource k m t) =
      fun t : ℝ => thetaCuspFourierLaplaceJetIntegrand k v (-(m : ℝ) * t) := by
    funext t
    rw [mobiusThetaNativeCollarSource_apply,
      thetaCuspFourierLaplaceJetIntegrand, thetaCuspFourierLaplaceIntegrand]
    have he : Complex.exp (((m : ℂ) * mobiusThetaCenteredParameter v) * (t : ℂ)) *
        (Real.exp (-(m : ℝ) * t / 2) : ℂ) =
        Complex.exp (-I * v * ((-(m : ℝ) * t : ℝ) : ℂ)) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      dsimp [mobiusThetaCenteredParameter]
      push_cast
      ring
    linear_combination he * ((-I * ((-(m : ℝ) * t : ℝ) : ℂ)) ^ k *
      (thetaCuspFullSource (-(m : ℝ) * t) : ℂ))
  rw [hf]
  refine ⟨(integrable_thetaCuspFourierLaplaceJetIntegrand k hv).comp_mul_left'
    (neg_ne_zero.mpr hmR.ne'), ?_⟩
  rw [MeasureTheory.Measure.integral_comp_mul_left,
    ← iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet k (abs_lt.mp hv)]
  simp only [abs_inv, abs_neg, abs_of_pos hmR, real_smul, Complex.ofReal_inv,
    Complex.ofReal_natCast]

end RHTower
