import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralGammaIntegral
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.SpectralCutObstruction

/-!
# Scaling of the source integral and the regularized cut

Substituting `t = V s` turns the source integral on the unit interval into a truncated Gamma
integral,

`∫₀¹ (e^{-Vs} − 1) s^{a-1} ds = V^{-a} ∫₀^V (e^{-t} − 1) t^{a-1} dt`,

so the regularized combination `V^a (∫₀¹ (e^{-Vs} − 1) s^{a-1} ds + 1/a)` converges to `Γ(a)` for
`−1 < a < 0`.  The same substitution evaluates the tail integral
`∫₀^∞ e^{-Vs} s^a ds = V^{-(a+1)} Γ(a+1)`.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology

noncomputable section

variable {a V : ℝ}

/-! ## The scaling identity -/

theorem gammaDefect_scaling (hV : 0 < V) {s : ℝ} (hs : 0 ≤ s) :
    gammaDefect a (V * s) = V ^ (a - 1) * (laplaceCochain V s * s ^ (a - 1)) := by
  rw [gammaDefect, laplaceCochain, Real.mul_rpow hV.le hs]
  ring

theorem cutIntegral_eq_interval (a V : ℝ) :
    cutIntegral a V = ∫ s in (0 : ℝ)..1, laplaceCochain V s * s ^ (a - 1) := by
  rw [cutIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

theorem cutIntegral_scaling (hV : 0 < V) :
    cutIntegral a V = V ^ (-a) * ∫ t in (0 : ℝ)..V, gammaDefect a t := by
  have hVne : V ≠ 0 := ne_of_gt hV
  have hcongr : (∫ s in (0 : ℝ)..1, gammaDefect a (V * s)) =
      ∫ s in (0 : ℝ)..1, V ^ (a - 1) * (laplaceCochain V s * s ^ (a - 1)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le zero_le_one] at hs
    exact gammaDefect_scaling hV hs.1
  have hsub : (∫ s in (0 : ℝ)..1, gammaDefect a (V * s)) =
      V⁻¹ • ∫ t in (V * 0)..(V * 1), gammaDefect a t :=
    intervalIntegral.integral_comp_mul_left _ hVne
  rw [hcongr, intervalIntegral.integral_const_mul] at hsub
  rw [mul_zero, mul_one, smul_eq_mul] at hsub
  have hpow : V ^ (-a) = (V ^ (a - 1))⁻¹ * V⁻¹ := by
    rw [← Real.rpow_neg hV.le, ← Real.rpow_neg_one V, ← Real.rpow_add hV]
    congr 1
    ring
  have hne : V ^ (a - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hV _)
  rw [cutIntegral_eq_interval, hpow, mul_assoc, ← hsub]
  field_simp

/-! ## The regularized cut converges to Gamma -/

theorem tendsto_rpow_div_atTop (ha0 : a < 0) : Tendsto (fun V : ℝ => V ^ a / a) atTop (𝓝 0) := by
  have hneg := tendsto_rpow_neg_atTop (y := -a) (by linarith)
  simp only [neg_neg] at hneg
  simpa using hneg.div_const a

/-- **The regularized cut integral converges to the Gamma value.** -/
theorem tendsto_regularizedCut (ha : -1 < a) (ha0 : a < 0) :
    Tendsto (fun V : ℝ => V ^ a * (cutIntegral a V + 1 / a)) atTop (𝓝 (Real.Gamma a)) := by
  have hIoi := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ)
    (integrableOn_gammaDefect ha ha0) (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  rw [integral_gammaDefect ha ha0] at hIoi
  have hsum := hIoi.add (tendsto_rpow_div_atTop ha0)
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with V hV
  rw [cutIntegral_scaling hV, mul_add]
  have hcollapse : V ^ a * (V ^ (-a) * ∫ t in (0 : ℝ)..V, gammaDefect a t) =
      ∫ t in (0 : ℝ)..V, gammaDefect a t := by
    rw [← mul_assoc, ← Real.rpow_add hV, add_neg_cancel, Real.rpow_zero, one_mul]
  rw [hcollapse]
  simp only [id_eq]
  ring

/-! ## The scaled Gamma tail -/

theorem integrableOn_expScaled (ha : -1 < a) (hV : 0 < V) :
    IntegrableOn (fun s : ℝ => Real.exp (-(V * s)) * s ^ a) (Ioi 0) := by
  have hconv := Real.GammaIntegral_convergent (s := a + 1) (by linarith)
  simp only [add_sub_cancel_right] at hconv
  have hscale : IntegrableOn (fun s : ℝ => Real.exp (-(V * s)) * (V * s) ^ a) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun t => Real.exp (-t) * t ^ a) 0 hV).2 (by simpa using hconv)
  have hVa : (0 : ℝ) < V ^ a := Real.rpow_pos_of_pos hV _
  have hmul : IntegrableOn (fun s : ℝ => (V ^ a)⁻¹ * (Real.exp (-(V * s)) * (V * s) ^ a))
      (Ioi 0) := hscale.const_mul _
  refine hmul.congr_fun (fun s hs => ?_) measurableSet_Ioi
  have hs0 : (0 : ℝ) < s := hs
  show (V ^ a)⁻¹ * (Real.exp (-(V * s)) * (V * s) ^ a) = Real.exp (-(V * s)) * s ^ a
  rw [Real.mul_rpow hV.le hs0.le]
  field_simp

/-- **The scaled Gamma tail.** -/
theorem integral_expScaled (ha : -1 < a) (hV : 0 < V) :
    (∫ s in Ioi (0 : ℝ), Real.exp (-(V * s)) * s ^ a) = V ^ (-(a + 1)) * Real.Gamma (a + 1) := by
  have hVa : (0 : ℝ) < V ^ a := Real.rpow_pos_of_pos hV _
  have hgamma : (∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ a) = Real.Gamma (a + 1) := by
    rw [Real.Gamma_eq_integral (by linarith : (0 : ℝ) < a + 1)]
    simp only [add_sub_cancel_right]
  have hsub : (∫ s in Ioi (0 : ℝ), Real.exp (-(V * s)) * (V * s) ^ a) =
      V⁻¹ * ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ a := by
    have h := integral_comp_mul_left_Ioi (fun t => Real.exp (-t) * t ^ a) 0 hV
    simpa using h
  have hexpand : (∫ s in Ioi (0 : ℝ), Real.exp (-(V * s)) * (V * s) ^ a) =
      V ^ a * ∫ s in Ioi (0 : ℝ), Real.exp (-(V * s)) * s ^ a := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    have hs0 : (0 : ℝ) < s := hs
    rw [Real.mul_rpow hV.le hs0.le]
    ring
  rw [hexpand, hgamma] at hsub
  have hpow : V ^ (-(a + 1)) = (V ^ a)⁻¹ * V⁻¹ := by
    rw [← Real.rpow_neg hV.le, ← Real.rpow_neg_one V, ← Real.rpow_add hV]
    congr 1
    ring
  rw [hpow, mul_assoc, ← hsub]
  field_simp

end

end GaloisForLFunctions.HTGeometry.Interfinity
