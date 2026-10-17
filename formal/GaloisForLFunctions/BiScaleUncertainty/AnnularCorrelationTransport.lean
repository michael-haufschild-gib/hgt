import GaloisForLFunctions.BiScaleUncertainty.KreinKantorovichMeasureTransportAndPrimePolarPairing
import GaloisForLFunctions.BiScaleUncertainty.SignedDyadicCollarPartition

/-!
# Differentiable annular transport of continuous correlations

A moving annular average admits an explicit continuous derivative even when the
source has no derivative. Its uniform error is controlled by the origin Krein
increment, so subsequent signed measure pairings retain all node values.
-/

open MeasureTheory Set
open scoped CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-- Moving average over an annulus, with its usual totalized zero-width value. -/
def annularAverage (h : C(ℝ, ℝ)) (a d t : ℝ) : ℝ :=
  (∫ x in t + a..t + a + d, h x) / d

theorem annularAverage_eq_shift (h : C(ℝ, ℝ)) (a d t : ℝ) :
    annularAverage h a d t = (∫ y in a..a + d, h (t + y)) / d := by
  rw [annularAverage, intervalIntegral.integral_comp_add_left]
  congr 2
  ring

theorem annularAverage_eq_primitive (h : C(ℝ, ℝ)) (a d t : ℝ) :
    annularAverage h a d t =
      ((∫ x in (0 : ℝ)..t + a + d, h x) - ∫ x in (0 : ℝ)..t + a, h x) / d := by
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (h.continuous.intervalIntegrable 0 (t + a))
    (h.continuous.intervalIntegrable (t + a) (t + a + d))
  unfold annularAverage
  congr 1
  linarith only [hi]

theorem hasDerivAt_annularAverage (h : C(ℝ, ℝ)) (a d t : ℝ) :
    HasDerivAt (annularAverage h a d)
      ((h (t + a + d) - h (t + a)) / d) t := by
  have hp (x : ℝ) : HasDerivAt (fun u => ∫ y in (0 : ℝ)..u, h y) (h x) x :=
    intervalIntegral.integral_hasDerivAt_right (h.continuous.intervalIntegrable 0 x)
      h.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter h.continuous.continuousAt
  have h₁ := (hp (t + a + d)).comp t (((hasDerivAt_id t).add_const a).add_const d)
  have h₂ := (hp (t + a)).comp t ((hasDerivAt_id t).add_const a)
  have heq : annularAverage h a d = fun u =>
      ((∫ x in (0 : ℝ)..u + a + d, h x) - ∫ x in (0 : ℝ)..u + a, h x) / d :=
    funext (annularAverage_eq_primitive h a d)
  rw [heq]
  simpa only [Function.comp_def, Pi.sub_apply, id_eq, mul_one] using
    (h₁.sub h₂).div_const d

theorem continuous_annularAverage (h : C(ℝ, ℝ)) (a d : ℝ) :
    Continuous (annularAverage h a d) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_annularAverage h a d t).continuousAt

theorem continuous_annularAverage_slope (h : C(ℝ, ℝ)) (a d : ℝ) :
    Continuous (fun t => (h (t + a + d) - h (t + a)) / d) :=
  ((h.continuous.comp ((continuous_id.add_const a).add_const d)).sub
    (h.continuous.comp (continuous_id.add_const a))).div_const d

/-- Positive annular endpoints are constructed from arbitrary real parameters. -/
def correlationAverage (f : C_c(ℝ, ℝ)) (a b : ℝ) : ℝ → ℝ :=
  annularAverage ⟨autocorr f, continuous_autocorr_compact f⟩ (Real.exp a) (Real.exp b)

def correlationAverageSlope (f : C_c(ℝ, ℝ)) (a b t : ℝ) : ℝ :=
  (autocorr f (t + Real.exp a + Real.exp b) - autocorr f (t + Real.exp a)) / Real.exp b

theorem hasDerivAt_correlationAverage (f : C_c(ℝ, ℝ)) (a b t : ℝ) :
    HasDerivAt (correlationAverage f a b) (correlationAverageSlope f a b t) t :=
  hasDerivAt_annularAverage _ _ _ _

theorem continuous_correlationAverage (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    Continuous (correlationAverage f a b) := continuous_annularAverage _ _ _

theorem continuous_correlationAverageSlope (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    Continuous (correlationAverageSlope f a b) :=
  continuous_annularAverage_slope ⟨autocorr f, continuous_autocorr_compact f⟩ _ _

/-- Uniform transport cost, finite for every compact continuous source. -/
def correlationTransportCost (f : C_c(ℝ, ℝ)) (a b : ℝ) : ℝ :=
  (∫ y in Real.exp a..Real.exp a + Real.exp b,
    Real.sqrt (2 * autocorr f 0 * (autocorr f 0 - autocorr f y))) / Real.exp b

theorem correlationTransportCost_nonneg (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    0 ≤ correlationTransportCost f a b := by
  apply div_nonneg _ (Real.exp_pos b).le
  exact intervalIntegral.integral_nonneg (le_add_of_nonneg_right (Real.exp_pos b).le)
    (fun _ _ => Real.sqrt_nonneg _)

/-- Uniform control retains arbitrary signed correlations at every real node. -/
theorem abs_correlationAverage_sub_le (f : C_c(ℝ, ℝ)) (a b t : ℝ) :
    |correlationAverage f a b t - autocorr f t| ≤ correlationTransportCost f a b := by
  let h : C(ℝ, ℝ) := ⟨autocorr f, continuous_autocorr_compact f⟩
  have hd : 0 < Real.exp b := Real.exp_pos b
  have hab : Real.exp a ≤ Real.exp a + Real.exp b := le_add_of_nonneg_right hd.le
  have hi : IntervalIntegrable (fun y => autocorr f (t + y)) volume
      (Real.exp a) (Real.exp a + Real.exp b) :=
    (h.continuous.comp (continuous_const.add continuous_id)).intervalIntegrable _ _
  have heq : correlationAverage f a b t - autocorr f t =
      (∫ y in Real.exp a..Real.exp a + Real.exp b,
        autocorr f (t + y) - autocorr f t) / Real.exp b := by
    rw [correlationAverage, annularAverage_eq_shift, intervalIntegral.integral_sub hi
      intervalIntegrable_const, intervalIntegral.integral_const]
    dsimp
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  calc
    _ ≤ ∫ y in Real.exp a..Real.exp a + Real.exp b,
        |autocorr f (t + y) - autocorr f t| :=
      intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ _ := by
      apply intervalIntegral.integral_mono_on hab
        (((h.continuous.comp (continuous_const.add continuous_id)).sub continuous_const).abs.intervalIntegrable _ _)
        ((continuous_const.mul (continuous_const.sub h.continuous)).sqrt.intervalIntegrable _ _)
      intro y _
      exact abs_autocorr_add_sub_le_sqrt f.hasCompactSupport f.continuous t y

/-- The local transport cost uses one adjustable origin-energy budget and the
reciprocal archimedean penalty. Every integral is finite on the constructed annulus. -/
theorem correlationTransportCost_le_levy (f : C_c(ℝ, ℝ)) (a b c : ℝ) :
    correlationTransportCost f a b ≤
      Real.exp c * (∫ y in Real.exp a..Real.exp a + Real.exp b,
        (autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
      autocorr f 0 / (2 * Real.exp c * Real.exp b ^ 2) *
        ∫ y in Real.exp a..Real.exp a + Real.exp b,
          Real.exp (-y / 2) * Real.sinh y := by
  have hab : Real.exp a ≤ Real.exp a + Real.exp b :=
    le_add_of_nonneg_right (Real.exp_pos b).le
  have hh := continuous_autocorr_compact f
  have hw : ContinuousOn archLevySinhWeight (Icc (Real.exp a) (Real.exp a + Real.exp b)) :=
    continuousOn_archLevySinhWeight fun _ hy => (Real.exp_pos a).trans_le hy.1
  have hi : IntervalIntegrable (fun y => (autocorr f 0 - autocorr f y) *
      archLevySinhWeight y) volume (Real.exp a) (Real.exp a + Real.exp b) :=
    ((continuousOn_const.sub hh.continuousOn).mul hw).intervalIntegrable_of_Icc hab
  have hc : Continuous (fun y : ℝ => Real.exp (-y / 2) * Real.sinh y) := by fun_prop
  have hj := hc.intervalIntegrable (μ := volume) (Real.exp a) (Real.exp a + Real.exp b)
  have hm : (∫ y in Real.exp a..Real.exp a + Real.exp b,
      Real.sqrt (2 * autocorr f 0 * (autocorr f 0 - autocorr f y)) / Real.exp b) ≤
      ∫ y in Real.exp a..Real.exp a + Real.exp b,
        Real.exp c * ((autocorr f 0 - autocorr f y) * archLevySinhWeight y) +
          autocorr f 0 / (2 * Real.exp c * Real.exp b ^ 2) *
            (Real.exp (-y / 2) * Real.sinh y) := by
    apply intervalIntegral.integral_mono_on hab
      (((continuous_const.mul (continuous_const.sub hh)).sqrt.div_const _).intervalIntegrable _ _)
      ((hi.const_mul _).add (hj.const_mul _))
    intro y hy
    have hW := archLevySinhWeight_pos ((Real.exp_pos a).trans_le hy.1)
    have hY := signed_collar_young_bound (w := 1 / Real.exp b)
      (mul_pos (Real.exp_pos c) hW) (autocorr_zero_nonneg (f : ℝ → ℝ))
      (autocorr_sub_nonneg f.hasCompactSupport f.continuous y)
    have hp : (1 / Real.exp b) ^ 2 / (2 * (Real.exp c * archLevySinhWeight y)) *
        autocorr f 0 = autocorr f 0 / (2 * Real.exp c * Real.exp b ^ 2) *
          (Real.exp (-y / 2) * Real.sinh y) := by
      rw [← inv_archLevySinhWeight_eq]
      ring
    rw [hp] at hY
    dsimp only [Pi.mul_apply, Pi.sub_apply]
    convert hY using 1 <;> ring
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hi.const_mul _)
    (hj.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hm
  exact hm

end
end GaloisForLFunctions.BiScaleUncertainty
