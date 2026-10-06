import GaloisForLFunctions.RHTower.PrimeAlmostAllShortIntervalsAsymptotic
import GaloisForLFunctions.RHTower.WeilLagLocalWorkHuxley

/-!
# Prime-window errors at shrinking logarithmic tolerances

BAG's hyperbolic phase-cell argument averages one prime variable before taking norms.
The test kernel depends on two other prime variables, so fixed-tolerance almost-all
convergence is insufficient. This module derives logarithmic rates directly from the
unconditional zero-density estimate, with the exceptional intervals retained.
-/

noncomputable section

namespace RHTower

open Filter Topology MeasureTheory

private theorem window_zeroWeight_scale {x Y c : ℝ} (hx : 0 ≤ x) (hc : 1 ≤ c)
    (ρ : ℂ) : zeroShortWeight x (c * Y) ρ ≤ c * zeroShortWeight x Y ρ := by
  unfold zeroShortWeight
  have hc0 : 0 ≤ c := by linarith
  rw [mul_div_assoc, mul_left_comm c, mul_min_of_nonneg _ _ hc0, mul_one]
  exact mul_le_mul_of_nonneg_left (min_le_min hc le_rfl) (Real.rpow_nonneg hx _)

private theorem window_zeroSum_scale {x Y c : ℝ} (hx : 1 ≤ x) (hY : 0 ≤ Y)
    (hc : 1 ≤ c) :
    (∑' q : XiZeroCopy, zeroShortWeight x (c * Y) (q.1 : ℂ)) ≤
      c * ∑' q : XiZeroCopy, zeroShortWeight x Y (q.1 : ℂ) := by
  rw [← tsum_mul_left]
  exact (summable_zeroShortWeight hx (mul_nonneg (by linarith) hY)).tsum_le_tsum
    (fun q => window_zeroWeight_scale (by linarith) hc (q.1 : ℂ))
    ((summable_zeroShortWeight hx hY).mul_left c)

private theorem window_volume_fixed_zeroSum {θ ε X : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hX : 4 ≤ X) (hδ : X ^ (θ - 1) ≤ 1 / 2)
    (hbig : 16 * (64 + 1152 * xiSpectralThreeHalvesMass) ≤ ε ^ 2 * X ^ (2 * θ)) :
    (volume {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ε * (X ^ (θ - 1) * x)
      < |Chebyshev.psi (x + X ^ (θ - 1) * x) - Chebyshev.psi x - X ^ (θ - 1) * x|}).toReal
      ≤ (25600 * (64 * (|xiLineTwoLogDerivConstant| + 2))) / ε ^ 3 *
        (Real.log (X ^ 2) + 2) ^ 2 * X *
        ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2)
          (192 / 5 * (X ^ 2) ^ (2 * ((1 - θ) / 2))) (q.1 : ℂ) := by
  have hX1 : 1 ≤ X ^ 2 := by nlinarith
  have hscale := window_zeroSum_scale (x := X ^ 2)
    (Y := 192 / 5 * (X ^ 2) ^ (2 * ((1 - θ) / 2))) (c := 1 / ε)
    hX1 (by positivity) ((le_div_iff₀ hε).2 (by simpa using hε1))
  have hYeq : 1 / ε * (192 / 5 * (X ^ 2) ^ (2 * ((1 - θ) / 2))) =
      192 / (5 * ε) * (X ^ 2) ^ (2 * ((1 - θ) / 2)) := by ring
  rw [hYeq] at hscale
  have hW := almostAllHarmonicWeight_le (show 1 ≤ X by linarith)
  have hW0 : 0 ≤ almostAllHarmonicWeight X := by
    unfold almostAllHarmonicWeight
    have h4 : 1 ≤ X ^ 4 := one_le_pow₀ (by linarith)
    have hlog1 := Real.log_nonneg (show 1 ≤ 3 * X ^ 4 + 4 by linarith)
    have hlog2 := Real.log_nonneg (show 1 ≤ 2 * X ^ 4 + 1 by linarith)
    positivity
  have hZ0 : 0 ≤ ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2)
      (192 / 5 * (X ^ 2) ^ (2 * ((1 - θ) / 2))) (q.1 : ℂ) :=
    tsum_nonneg fun q => zeroShortWeight_nonneg (sq_nonneg _) (by positivity) _
  refine (volume_psi_short_asymptotic_le hε hε1 hX hδ hbig).trans ?_
  calc _ ≤ 25600 / ε ^ 2 * almostAllHarmonicWeight X * X *
      (1 / ε * ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2)
        (192 / 5 * (X ^ 2) ^ (2 * ((1 - θ) / 2))) (q.1 : ℂ)) := by
        exact mul_le_mul_of_nonneg_left hscale (by positivity)
    _ ≤ 25600 / ε ^ 2 * (64 * (|xiLineTwoLogDerivConstant| + 2) *
        (Real.log (X ^ 2) + 2) ^ 2) * X *
      (1 / ε * ∑' q : XiZeroCopy, zeroShortWeight (X ^ 2)
        (192 / 5 * (X ^ 2) ^ (2 * ((1 - θ) / 2))) (q.1 : ℂ)) := by gcongr
    _ = _ := by ring

/-- Every logarithmic saving holds even when the allowed relative prime-window error
shrinks by an arbitrary logarithmic power. No RH or prime-distribution premise is used. -/
theorem tendsto_logPow_volume_psi_short_shrinking (k a : ℕ) {θ : ℝ}
    (hθ : 1 / 6 < θ) (hθ1 : θ < 1) :
    Tendsto (fun X : ℝ => (Real.log (X ^ 2) + 2) ^ k *
      (volume {x : ℝ | x ∈ Set.Icc X (2 * X) ∧
        ((Real.log (X ^ 2) + 2) ^ a)⁻¹ * (X ^ (θ - 1) * x)
          < |Chebyshev.psi (x + X ^ (θ - 1) * x) - Chebyshev.psi x - X ^ (θ - 1) * x|}).toReal / X)
      atTop (𝓝 0) := by
  let C : ℝ := 25600 * (64 * (|xiLineTwoLogDerivConstant| + 2))
  let B : ℝ := 16 * (64 + 1152 * xiSpectralThreeHalvesMass)
  have hθ0 : 0 < θ := by linarith
  have hpow : Tendsto (fun X : ℝ => X ^ (2 : ℕ)) atTop atTop :=
    tendsto_pow_atTop two_ne_zero
  have hlim := ((tendsto_logPow_mul_tsum_zeroShortWeight_seven_twelfths
    (k + a * 3 + 2) (u := (1 - θ) / 2) (c := 192 / 5)
    (by linarith) (by linarith) (by norm_num)).comp hpow).const_mul C
  rw [mul_zero] at hlim
  have hsmall := ((tendsto_log_add_two_pow_mul_rpow_neg (a * 2) hθ0).comp hpow).const_mul B
  rw [mul_zero] at hsmall
  have hevB := hsmall.eventually_le_const (by norm_num : (0 : ℝ) < 1)
  have hevδ : ∀ᶠ X : ℝ in atTop, X ^ (θ - 1) ≤ 1 / 2 := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 1 - θ by linarith)).eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 2)
    simpa only [neg_sub] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [eventually_ge_atTop (4 : ℝ)] with X hX
    have hlog : 0 ≤ Real.log (X ^ 2) + 2 := by
      have := Real.log_nonneg (show 1 ≤ X ^ 2 by nlinarith)
      linarith
    exact div_nonneg (mul_nonneg (pow_nonneg hlog _) ENNReal.toReal_nonneg) (by linarith)
  · filter_upwards [hevB, hevδ, eventually_ge_atTop (4 : ℝ)] with X hB hδ hX
    let L : ℝ := Real.log (X ^ 2) + 2
    let ε : ℝ := (L ^ a)⁻¹
    have hX0 : 0 < X := by linarith
    have hL1 : 1 ≤ L := by
      have := Real.log_nonneg (show 1 ≤ X ^ 2 by nlinarith)
      dsimp [L]; linarith
    have hLp : 0 < L ^ a := pow_pos (by linarith) _
    have hε : 0 < ε := inv_pos.mpr hLp
    have hε1 : ε ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hL1)
    have hpoweq : (X ^ (2 : ℕ)) ^ θ = X ^ (2 * θ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      norm_num
    have hbig : B ≤ ε ^ 2 * X ^ (2 * θ) := by
      change B * (L ^ (a * 2) * (X ^ 2) ^ (-θ)) ≤ 1 at hB
      rw [Real.rpow_neg (sq_nonneg X), ← mul_assoc, ← div_eq_mul_inv,
        div_le_iff₀ (Real.rpow_pos_of_pos (sq_pos_of_pos hX0) θ), one_mul, hpoweq] at hB
      have hb := (le_div_iff₀ (pow_pos hLp 2)).2 (by simpa only [pow_mul] using hB)
      simpa only [ε, inv_pow, div_eq_mul_inv, mul_comm] using hb
    have hv := window_volume_fixed_zeroSum hε hε1 hX hδ hbig
    have hle := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hv (pow_nonneg (by linarith : 0 ≤ L) k)) hX0.le
    refine hle.trans_eq ?_
    change L ^ k * (C / ε ^ 3 * L ^ 2 * X * _) / X = C * (L ^ (k + a * 3 + 2) * _)
    simp only [pow_add, pow_mul, ε]
    field_simp

/-- Relative error of the actual von Mangoldt mass in a multiplicative short window. -/
def chiCubicPrimeWindowError (θ X x : ℝ) : ℝ :=
  |Chebyshev.psi (x + X ^ (θ - 1) * x) - Chebyshev.psi x - X ^ (θ - 1) * x| /
    (X ^ (θ - 1) * x)

private theorem window_error_measurable (θ X : ℝ) :
    Measurable (chiCubicPrimeWindowError θ X) := by
  unfold chiCubicPrimeWindowError
  exact (((Chebyshev.psi_mono.measurable.comp
    (measurable_id.add (measurable_const.mul measurable_id))).sub
      Chebyshev.psi_mono.measurable).sub
        (measurable_const.mul measurable_id)).abs.div (measurable_const.mul measurable_id)

private theorem window_error_bound {θ X x : ℝ} (hθ : 0 < θ) (hX : 4 ≤ X)
    (hδ : X ^ (θ - 1) ≤ 1 / 2) (hx : x ∈ Set.Icc X (2 * X)) :
    0 ≤ chiCubicPrimeWindowError θ X x ∧
      chiCubicPrimeWindowError θ X x ≤ 2 * (Real.log (X ^ 2) + 2) := by
  have hX0 : 0 < X := by linarith
  have hx1 : 1 ≤ x := by linarith [hx.1]
  have hd0 : 0 < X ^ (θ - 1) := Real.rpow_pos_of_pos hX0 _
  have heq : X ^ (θ - 1) * X = X ^ θ := by
    calc X ^ (θ - 1) * X = X ^ (θ - 1) * X ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = X ^ θ := by rw [← Real.rpow_add hX0]; congr 1; ring
  have hL1 : 1 ≤ X ^ (θ - 1) * x := by
    calc 1 ≤ X ^ θ := Real.one_le_rpow (by linarith) hθ.le
      _ = X ^ (θ - 1) * X := heq.symm
      _ ≤ X ^ (θ - 1) * x := mul_le_mul_of_nonneg_left hx.1 hd0.le
  have hL0 : 0 < X ^ (θ - 1) * x := by linarith
  have hlog0 : 0 ≤ Real.log (X ^ 2) := Real.log_nonneg (by nlinarith)
  have hlog : Real.log (x + X ^ (θ - 1) * x) ≤ Real.log (X ^ 2) := by
    refine Real.log_le_log (by positivity) ?_
    have := mul_le_mul_of_nonneg_right hδ (by linarith : 0 ≤ x)
    nlinarith [hx.2]
  have htriv := abs_psi_window_sub_le_trivial hx1 hL0.le
  constructor
  · exact div_nonneg (abs_nonneg _) hL0.le
  · unfold chiCubicPrimeWindowError
    rw [div_le_iff₀ hL0]
    have hterm := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ X ^ (θ - 1) * x + 1)
    have hterm2 := mul_le_mul_of_nonneg_right
      (show X ^ (θ - 1) * x + 1 ≤ 2 * (X ^ (θ - 1) * x) by linarith) hlog0
    nlinarith

private theorem window_integral_error_le {θ ε X : ℝ} (hθ : 0 < θ) (hε : 0 ≤ ε)
    (hX : 4 ≤ X) (hδ : X ^ (θ - 1) ≤ 1 / 2) :
    (∫ x in Set.Icc X (2 * X), chiCubicPrimeWindowError θ X x) ≤ ε * X +
      2 * (Real.log (X ^ 2) + 2) *
        (volume {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ε * (X ^ (θ - 1) * x)
          < |Chebyshev.psi (x + X ^ (θ - 1) * x) - Chebyshev.psi x - X ^ (θ - 1) * x|}).toReal := by
  let E := {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ε < chiCubicPrimeWindowError θ X x}
  let M : ℝ := 2 * (Real.log (X ^ 2) + 2)
  have hE : MeasurableSet E := measurableSet_Icc.inter
    (measurableSet_lt measurable_const (window_error_measurable θ X))
  have hEsub : E ⊆ Set.Icc X (2 * X) := fun _ hx => hx.1
  have hfin : volume (Set.Icc X (2 * X)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hc : IntegrableOn (fun _ : ℝ => ε) (Set.Icc X (2 * X)) volume := integrableOn_const hfin
  have hM : IntegrableOn (fun _ : ℝ => M) (Set.Icc X (2 * X)) volume := integrableOn_const hfin
  have hi := setIntegral_mono_of_nonneg
    (fun x hx => (window_error_bound hθ hX hδ hx).1)
    (g := fun x => ε + E.indicator (fun _ => M) x)
    (fun x hx => by
      by_cases hxE : x ∈ E
      · rw [Set.indicator_of_mem hxE]
        exact (window_error_bound hθ hX hδ hx).2.trans (by dsimp [M]; linarith)
      · rw [Set.indicator_of_notMem hxE, add_zero]
        exact le_of_not_gt (fun h => hxE ⟨hx, h⟩)) (hc.add (hM.indicator hE))
  have heq : E = {x : ℝ | x ∈ Set.Icc X (2 * X) ∧ ε * (X ^ (θ - 1) * x)
      < |Chebyshev.psi (x + X ^ (θ - 1) * x) - Chebyshev.psi x - X ^ (θ - 1) * x|} := by
    ext x
    refine and_congr_right fun hx => ?_
    have hpos : 0 < X ^ (θ - 1) * x := by
      have : 0 < X := by linarith
      have : 0 < x := by linarith [hx.1]
      positivity
    exact lt_div_iff₀ hpos
  rw [integral_add hc (hM.indicator hE), setIntegral_const,
    integral_indicator hE, setIntegral_const] at hi
  dsimp only [Measure.real] at hi
  rw [Measure.restrict_apply hE, Set.inter_eq_left.mpr hEsub,
    Real.volume_Icc, show 2 * X - X = X by ring,
    ENNReal.toReal_ofReal (show 0 ≤ X by linarith)] at hi
  simpa only [smul_eq_mul, mul_comm, heq, M] using hi

/-- The prime-window relative error is integrable and its L¹ mean tends to zero faster
than every fixed logarithmic power. This is an unconditional averaged estimate; it
makes no claim about sampling the error at prime anchors. -/
theorem chiCubicPrimeWindowError_logRate (k : ℕ) {θ : ℝ}
    (hθ : 1 / 6 < θ) (hθ1 : θ < 1) :
    (∀ᶠ X : ℝ in atTop, IntegrableOn (chiCubicPrimeWindowError θ X)
      (Set.Icc X (2 * X)) volume) ∧
    Tendsto (fun X : ℝ => (Real.log (X ^ 2) + 2) ^ k / X *
      ∫ x in Set.Icc X (2 * X), chiCubicPrimeWindowError θ X x) atTop (𝓝 0) := by
  have hθ0 : 0 < θ := by linarith
  have hevδ : ∀ᶠ X : ℝ in atTop, X ^ (θ - 1) ≤ 1 / 2 := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 1 - θ by linarith)).eventually_le_const
      (by norm_num : (0 : ℝ) < 1 / 2)
    simpa only [neg_sub] using h
  constructor
  · filter_upwards [hevδ, eventually_ge_atTop (4 : ℝ)] with X hδ hX
    have hc : IntegrableOn (fun _ : ℝ => 2 * (Real.log (X ^ 2) + 2))
        (Set.Icc X (2 * X)) volume := integrableOn_const (by
          rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    refine hc.mono' (window_error_measurable θ X).aestronglyMeasurable.restrict ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (window_error_bound hθ0 hX hδ hx).1]
    exact (window_error_bound hθ0 hX hδ hx).2
  · have hL : Tendsto (fun X : ℝ => Real.log (X ^ 2) + 2) atTop atTop :=
      tendsto_atTop_add_const_right atTop 2
        (Real.tendsto_log_atTop.comp (tendsto_pow_atTop two_ne_zero))
    have hinv := tendsto_inv_atTop_zero.comp hL
    have hbad := (tendsto_logPow_volume_psi_short_shrinking (k + 1) (k + 1) hθ hθ1).const_mul 2
    have hlim := hinv.add hbad
    simp only [mul_zero, add_zero] at hlim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [hevδ, eventually_ge_atTop (4 : ℝ)] with X hδ hX
      have hX0 : 0 < X := by linarith
      have hlog : 0 ≤ Real.log (X ^ 2) + 2 := by
        have := Real.log_nonneg (show 1 ≤ X ^ 2 by nlinarith); linarith
      exact mul_nonneg (div_nonneg (pow_nonneg hlog _) hX0.le)
        (setIntegral_nonneg measurableSet_Icc (fun x hx => (window_error_bound hθ0 hX hδ hx).1))
    · filter_upwards [hevδ, eventually_ge_atTop (4 : ℝ)] with X hδ hX
      let L : ℝ := Real.log (X ^ 2) + 2
      have hX0 : 0 < X := by linarith
      have hL0 : 0 < L := by
        have := Real.log_nonneg (show 1 ≤ X ^ 2 by nlinarith); dsimp [L]; linarith
      have hb := window_integral_error_le hθ0 (show 0 ≤ (L ^ (k + 1))⁻¹ by positivity) hX hδ
      have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ L ^ k / X by positivity)
      refine hh.trans_eq ?_
      have halg (v : ℝ) : L ^ k / X * ((L ^ (k + 1))⁻¹ * X + 2 * L * v) =
          L⁻¹ + 2 * (L ^ (k + 1) * v / X) := by
        simp only [pow_succ]
        field_simp [hL0.ne', hX0.ne']
      exact halg _

end RHTower

end
