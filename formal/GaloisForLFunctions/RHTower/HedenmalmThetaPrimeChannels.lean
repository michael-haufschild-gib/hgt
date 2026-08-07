import GaloisForLFunctions.RHTower.HedenmalmTwoPrimeNormalFrame
import GaloisForLFunctions.RHTower.CCMTwoPoleSourceCriterion

/-!
# The two positive-kernel self-adjoint prime channels

Convolution by the centered prime window `c_n` acts on the Fourier side as multiplication by the
real symbol `hat c_n = a_n Xi_C`.  Since `c_n` is positive, even and integrable the symbol is real
and bounded by the total mass of `c_n`, so the channel is a bounded self-adjoint operator on
`L²(ℝ)`.  Its symbol is exactly the multiplier of the divisor factorization, so the two prime
channels see the whole `Xi` divisor.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace HedenmalmThetaSource

open HedenmalmQuantile HedenmalmIntervalAnomaly

/-! ### The centered prime window is an integrable positive even kernel -/

theorem centeredWindow_eq_cdf {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    centeredWindow thetaSource n x
      = ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        * (thetaSource.mass * (thetaSource.cdfFun (x + Real.log n / 2)
            - thetaSource.cdfFun (x - Real.log n / 2))) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  rw [centeredWindow, mass_mul_cdfFun_sub thetaSource (by linarith : x - Real.log n / 2
    ≤ x + Real.log n / 2)]

theorem continuous_centeredWindow {n : ℕ} (hn : 1 ≤ n) :
    Continuous (centeredWindow thetaSource n) := by
  have h : Continuous fun x : ℝ => ((n : ℝ) ^ (-(1 / 2 : ℝ)))
      * (thetaSource.mass * (thetaSource.cdfFun (x + Real.log n / 2)
          - thetaSource.cdfFun (x - Real.log n / 2))) :=
    continuous_const.mul (continuous_const.mul
      ((thetaSource.continuous_cdfFun.comp (continuous_id.add continuous_const)).sub
        (thetaSource.continuous_cdfFun.comp (continuous_id.sub continuous_const))))
  exact h.congr fun x => (centeredWindow_eq_cdf hn x).symm

/-- The exponential envelope constant of the centered prime window. -/
def channelBoundConstant (n : ℕ) : ℝ :=
  ((n : ℝ) ^ (-(1 / 2 : ℝ)))
    * (Real.log n * (thetaBound * Real.exp (Real.log n)) * Real.exp (Real.log n / 2))

theorem centeredWindow_le_exp {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    centeredWindow thetaSource n x ≤ channelBoundConstant n * Real.exp (-|x|) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hpow : (0 : ℝ) < (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos (by linarith) _
  have hshift : centeredWindow thetaSource n x
      = ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        * intervalMass thetaSource (x - Real.log n / 2)
            ((x - Real.log n / 2) + Real.log n) := by
    rw [centeredWindow]
    congr 2
    ring
  have hmass := intervalMass_le_exp hL (x - Real.log n / 2)
  have habs : Real.exp (-|x - Real.log n / 2|)
      ≤ Real.exp (Real.log n / 2) * Real.exp (-|x|) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h := abs_sub_abs_le_abs_sub x (x - Real.log n / 2)
    have habs2 : |x - (x - Real.log n / 2)| = Real.log n / 2 := by
      rw [show x - (x - Real.log n / 2) = Real.log n / 2 by ring, abs_of_nonneg (by linarith)]
    rw [habs2] at h
    linarith
  have hCnn : (0 : ℝ) ≤ Real.log n * (thetaBound * Real.exp (Real.log n)) := by
    have := thetaBound_nonneg
    positivity
  rw [hshift, channelBoundConstant]
  calc ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        * intervalMass thetaSource (x - Real.log n / 2) ((x - Real.log n / 2) + Real.log n)
      ≤ ((n : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.log n * (thetaBound * Real.exp (Real.log n))
          * Real.exp (-|x - Real.log n / 2|)) := mul_le_mul_of_nonneg_left hmass hpow.le
    _ ≤ ((n : ℝ) ^ (-(1 / 2 : ℝ))) * (Real.log n * (thetaBound * Real.exp (Real.log n))
          * (Real.exp (Real.log n / 2) * Real.exp (-|x|))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left habs hCnn) hpow.le
    _ = ((n : ℝ) ^ (-(1 / 2 : ℝ)) * (Real.log n * (thetaBound * Real.exp (Real.log n))
          * Real.exp (Real.log n / 2))) * Real.exp (-|x|) := by ring

theorem centeredWindow_nonneg (n : ℕ) (x : ℝ) : 0 ≤ centeredWindow thetaSource n x := by
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  exact mul_nonneg hpow (intervalMass_nonneg _ _)

theorem integrable_centeredWindow {n : ℕ} (hn : 1 ≤ n) :
    Integrable (centeredWindow thetaSource n) (volume : Measure ℝ) := by
  refine Integrable.mono'
    ((integrable_exp_neg_mul_abs (by norm_num : (0:ℝ) < 1)).const_mul (channelBoundConstant n))
    (continuous_centeredWindow hn).aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (centeredWindow_nonneg n x), one_mul]
  exact centeredWindow_le_exp hn x

end HedenmalmThetaSource

end

end RHTower
