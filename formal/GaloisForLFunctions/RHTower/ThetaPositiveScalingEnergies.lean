import GaloisForLFunctions.RHTower.ThetaGammaPolarScalingEnergy

/-!
# Separate positive Gamma and pole ground energies

The signed continuous energy splits into pole energy minus Gamma energy.
Both parts converge absolutely and are nonnegative. Thus the complete
arithmetic form compares three positive jump energies without discarding
either pole channel or the singular Gamma contribution.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

theorem thetaContinuousLinkMeasure_ae_pos :
    ∀ᵐ p : ℝ × ℝ ∂thetaContinuousLinkMeasure, 0 < p.1 := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact Eventually.of_forall fun _ => hu

def thetaPolarScalingDensity (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) (p : ℝ × ℝ) : ℝ :=
  2 * Real.cosh (p.1 / 2) * S.k p.2 * S.k (p.2 + p.1) *
    ‖chi (p.2 + p.1) - chi p.2‖ ^ 2

def thetaGammaScalingDensity (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) (p : ℝ × ℝ) : ℝ :=
  Real.exp (-p.1 / 2) / (1 - Real.exp (-2 * p.1)) * S.k p.2 * S.k (p.2 + p.1) *
    ‖chi (p.2 + p.1) - chi p.2‖ ^ 2

def thetaPolarScalingEnergy (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) : ℝ :=
  ∫ p, thetaPolarScalingDensity S chi p ∂thetaContinuousLinkMeasure

def thetaGammaScalingEnergy (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) : ℝ :=
  ∫ p, thetaGammaScalingDensity S chi p ∂thetaContinuousLinkMeasure

theorem thetaPolarScalingDensity_nonneg (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) (p : ℝ × ℝ) :
    0 ≤ thetaPolarScalingDensity S chi p := by
  have hx := (S.pos p.2).le
  have hy := (S.pos (p.2 + p.1)).le
  unfold thetaPolarScalingDensity
  positivity

theorem thetaGammaScalingDensity_nonneg (S : ThetaSource) (chi : 𝓢(ℝ, ℂ))
    {p : ℝ × ℝ} (hp : 0 < p.1) : 0 ≤ thetaGammaScalingDensity S chi p := by
  have hx := (S.pos p.2).le
  have hy := (S.pos (p.2 + p.1)).le
  have hd : 0 < 1 - Real.exp (-2 * p.1) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  unfold thetaGammaScalingDensity
  positivity

private theorem damped_cosh {u : ℝ} (hu : 0 ≤ u) :
    2 * Real.cosh (u / 2) * Real.exp (-2 * u) ≤ 2 * Real.exp (-u) := by
  have hc : Real.cosh (u / 2) ≤ Real.exp (u / 2) := by
    rw [Real.cosh_eq]
    have := Real.exp_le_exp.mpr (show -(u / 2) ≤ u / 2 by linarith)
    linarith
  calc
    _ ≤ 2 * Real.exp (u / 2) * Real.exp (-2 * u) := by gcongr
    _ = 2 * Real.exp (u / 2 - 2 * u) := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ _ := by gcongr; linarith

/-- The growing pole kernel is controlled by the actual source pair decay. -/
theorem integrable_thetaPolarScalingDensity (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    Integrable (thetaPolarScalingDensity S chi) thetaContinuousLinkMeasure := by
  obtain ⟨C, hC, hb⟩ := thetaSource_shiftPair_decay S
  let N := ‖chi.toBoundedContinuousFunction‖
  have hN : 0 ≤ N := norm_nonneg _
  have hx : Integrable (fun x : ℝ => Real.exp (-2 * |x|)) := by
    simpa only [pow_zero, one_mul] using
      HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 (show (0 : ℝ) < 2 by norm_num)
  have hm : Measurable (thetaPolarScalingDensity S chi) := by
    have hs := S.cont.measurable
    have hc := chi.continuous.measurable
    unfold thetaPolarScalingDensity
    fun_prop
  have hmajor := ((integrableOn_exp_neg_Ioi 0).mul_prod hx).const_mul (8 * C ^ 2 * N ^ 2)
  apply hmajor.mono' hm.aestronglyMeasurable
  filter_upwards [thetaContinuousLinkMeasure_ae_pos] with p hp
  have hinc : ‖chi (p.2 + p.1) - chi p.2‖ ≤ 2 * N := by
    calc
      _ ≤ ‖chi (p.2 + p.1)‖ + ‖chi p.2‖ := norm_sub_le _ _
      _ ≤ N + N := add_le_add (chi.toBoundedContinuousFunction.norm_coe_le_norm _)
        (chi.toBoundedContinuousFunction.norm_coe_le_norm _)
      _ = _ := by ring
  have hsq : ‖chi (p.2 + p.1) - chi p.2‖ ^ 2 ≤ 4 * N ^ 2 := by
    calc
      _ ≤ (2 * N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hinc 2
      _ = _ := by ring
  rw [Real.norm_of_nonneg (thetaPolarScalingDensity_nonneg S chi p)]
  unfold thetaPolarScalingDensity
  calc
    _ = (2 * Real.cosh (p.1 / 2)) * (S.k p.2 * S.k (p.2 + p.1)) *
        ‖chi (p.2 + p.1) - chi p.2‖ ^ 2 := by ring
    _ ≤ (2 * Real.cosh (p.1 / 2)) *
        (C ^ 2 * Real.exp (-2 * |p.2|) * Real.exp (-2 * p.1)) * (4 * N ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hb _ _ hp.le) (by positivity)) hsq
        (sq_nonneg _) (by positivity)
    _ = 4 * C ^ 2 * N ^ 2 * Real.exp (-2 * |p.2|) *
        (2 * Real.cosh (p.1 / 2) * Real.exp (-2 * p.1)) := by ring
    _ ≤ 4 * C ^ 2 * N ^ 2 * Real.exp (-2 * |p.2|) * (2 * Real.exp (-p.1)) :=
      mul_le_mul_of_nonneg_left (damped_cosh hp.le) (by positivity)
    _ = _ := by ring

theorem thetaGammaPolarScalingDensity_eq (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) (p : ℝ × ℝ) :
    thetaGammaPolarScalingDensity S chi p =
      thetaPolarScalingDensity S chi p - thetaGammaScalingDensity S chi p := by
  unfold thetaGammaPolarScalingDensity thetaGammaPolarScalingKernel
    thetaPolarScalingDensity thetaGammaScalingDensity
  ring

/-- Convergence of the Gamma part follows from two convergent compensated expressions. -/
theorem integrable_thetaGammaScalingDensity (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    Integrable (thetaGammaScalingDensity S chi) thetaContinuousLinkMeasure := by
  apply ((integrable_thetaPolarScalingDensity S chi).sub
    (integrable_thetaGammaPolarScalingDensity S chi)).congr
  exact Eventually.of_forall fun p => by
    simp only [Pi.sub_apply, thetaGammaPolarScalingDensity_eq, sub_sub_cancel]

theorem thetaGammaPolarScalingEnergy_eq_polar_sub_gamma (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    thetaGammaPolarScalingEnergy S chi = thetaPolarScalingEnergy S chi - thetaGammaScalingEnergy S chi := by
  unfold thetaGammaPolarScalingEnergy thetaPolarScalingEnergy thetaGammaScalingEnergy
  simp_rw [thetaGammaPolarScalingDensity_eq]
  exact integral_sub (integrable_thetaPolarScalingDensity S chi) (integrable_thetaGammaScalingDensity S chi)

theorem thetaPolarScalingEnergy_nonneg (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    0 ≤ thetaPolarScalingEnergy S chi := integral_nonneg (thetaPolarScalingDensity_nonneg S chi)

theorem thetaGammaScalingEnergy_nonneg (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    0 ≤ thetaGammaScalingEnergy S chi := by
  apply integral_nonneg_of_ae
  filter_upwards [thetaContinuousLinkMeasure_ae_pos] with p hp
  exact thetaGammaScalingDensity_nonneg S chi hp

end RHTower.ThetaSourceWard
