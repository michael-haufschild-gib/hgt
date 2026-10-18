import GaloisForLFunctions.RHTower.CHMDKleinGordonTemporalSpectrum

/-!
# Temporal spectrum of each folded Möbius kernel

The exponentially growing elementary source produces one explicit pole
oscillation. The remaining folded source has no temporal atoms. The
arithmetic sum over all scales is not exchanged with temporal averaging.
-/

open MeasureTheory Filter Set Topology
open scoped Real

namespace RHTower.CHMDChebyshevTransport

open RHTower.CHMDLightCone RHTower.CHMDStage22 GaloisForLFunctions.HTGeometry

noncomputable section

theorem measurable_chmdPrimeKernel_time (s : ℝ) :
    Measurable (fun y => chmdPrimeKernel y s) := by
  unfold chmdPrimeKernel
  have hm : Measurable (fun p : ℝ × ℝ =>
      Real.cos (p.1 * Real.sqrt (p.2 ^ 2 + 2)) * sechSqHalf p.2 * Real.cos (p.2 * s)) :=
    (((by fun_prop : Continuous (fun p : ℝ × ℝ =>
      Real.cos (p.1 * Real.sqrt (p.2 ^ 2 + 2)))).mul
        (continuous_sechSqHalf.comp continuous_snd)).mul (by fun_prop)).measurable
  exact measurable_const.mul hm.stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_kernelDeriv_time (s : ℝ) :
    Measurable (fun y => kernelDeriv y s) :=
  measurable_kernelDeriv_joint.comp (measurable_id.prodMk measurable_const)

theorem measurable_kernelDeriv2_time (s : ℝ) :
    Measurable (fun y => kernelDeriv2 y s) :=
  measurable_kernelDeriv2_joint.comp (measurable_id.prodMk measurable_const)

theorem measurable_conjugatedLaplacian_time (s : ℝ) :
    Measurable (fun y => conjugatedLaplacian y s) :=
  measurable_conjugatedLaplacian_joint.comp (measurable_id.prodMk measurable_const)

theorem conjugatedKernel_temporalCoefficient_zero (s : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (temporalCosineAverage (fun y => conjugatedKernel y s) lam) atTop (𝓝 0) := by
  have h := (chmdPrimeKernel_temporalCoefficient_zero s hlam).const_mul (Real.exp (-(s / 2)))
  change Tendsto (temporalCosineAverage (fun y => Real.exp (-(s / 2)) * chmdPrimeKernel y s) lam)
    atTop (𝓝 0)
  simpa only [← temporalCosineAverage_const_mul, mul_zero] using h

theorem conjugatedLaplacian_temporalCoefficient_zero (s : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (temporalCosineAverage (fun y => conjugatedLaplacian y s) lam) atTop (𝓝 0) := by
  have hi0 (T : ℝ) := integrable_temporalCosineIntegrand
    (measurable_chmdPrimeKernel_time s) (fun y => abs_chmdPrimeKernel_le y s) lam T
  have hi1 (T : ℝ) := integrable_temporalCosineIntegrand
    (measurable_kernelDeriv_time s) (fun y => abs_kernelDeriv_le y s) lam T
  have hi2 (T : ℝ) := integrable_temporalCosineIntegrand
    (measurable_kernelDeriv2_time s) (fun y => abs_kernelDeriv2_le y s) lam T
  have heq (T : ℝ) : temporalCosineAverage (fun y => conjugatedLaplacian y s) lam T =
      Real.exp (-(s / 2)) *
        (temporalCosineAverage (fun y => kernelDeriv2 y s) lam T -
          temporalCosineAverage (fun y => kernelDeriv y s) lam T +
          temporalCosineAverage (fun y => chmdPrimeKernel y s) lam T / 4) := by
    unfold temporalCosineAverage conjugatedLaplacian
    have hp (t : ℝ) :
        Real.exp (-(s / 2)) *
          (kernelDeriv2 (T * t) s - kernelDeriv (T * t) s + chmdPrimeKernel (T * t) s / 4) *
            Real.cos (lam * (T * t)) =
        Real.exp (-(s / 2)) *
          ((kernelDeriv2 (T * t) s * Real.cos (lam * (T * t)) -
            kernelDeriv (T * t) s * Real.cos (lam * (T * t))) +
            chmdPrimeKernel (T * t) s * Real.cos (lam * (T * t)) / 4) := by ring
    simp_rw [hp]
    have hsub := (hi2 T).sub (hi1 T)
    change IntegrableOn (fun t => kernelDeriv2 (T * t) s * Real.cos (lam * (T * t)) -
      kernelDeriv (T * t) s * Real.cos (lam * (T * t))) (Ioc (0 : ℝ) 1) at hsub
    rw [integral_const_mul, integral_add hsub ((hi0 T).div_const 4),
      integral_sub (hi2 T) (hi1 T), integral_div]
  have h := (((kernelDeriv2_temporalCoefficient_zero s hlam).sub
    (kernelDeriv_temporalCoefficient_zero s hlam)).add
    ((chmdPrimeKernel_temporalCoefficient_zero s hlam).div_const 4)).const_mul
      (Real.exp (-(s / 2)))
  simpa only [sub_self, zero_div, add_zero, mul_zero, ← heq] using h

theorem poleShadow_temporalCoefficient_zero {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (temporalCosineAverage poleShadow lam) atTop (𝓝 0) := by
  have hm : Measurable (fun p : ℝ × ℝ =>
      chmdPrimeKernel p.1 p.2 * Real.exp (-(p.2 / 2))) :=
    measurable_chmdPrimeKernel_joint.mul (by fun_prop)
  have hi : IntegrableOn (fun s : ℝ => (4 / π) * Real.exp (-(s / 2))) (Ioi (0 : ℝ)) := by
    have h : IntegrableOn (fun s : ℝ => (4 / π) * Real.exp (-(1 / 2) * s)) (Ioi (0 : ℝ)) :=
      (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul (4 / π)
    refine h.congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp only [show -(1 / 2 : ℝ) * s = -(s / 2) by ring]
  have hb : ∀ y s, |chmdPrimeKernel y s * Real.exp (-(s / 2))| ≤
      (4 / π) * Real.exp (-(s / 2)) := by
    intro y s
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (abs_chmdPrimeKernel_le y s) (Real.exp_pos _).le
  have h := temporalCosineAverage_integral_tendsto hm hi hb (lam := lam)
    (L := fun _ => 0) (Eventually.of_forall fun s => by
      have h := (chmdPrimeKernel_temporalCoefficient_zero s hlam).const_mul (Real.exp (-(s / 2)))
      have heq : (fun y => chmdPrimeKernel y s * Real.exp (-(s / 2))) =
          (fun y => Real.exp (-(s / 2)) * chmdPrimeKernel y s) := funext fun y => mul_comm _ _
      rw [heq]
      simpa only [mul_zero, ← temporalCosineAverage_const_mul] using h)
  change Tendsto (temporalCosineAverage
    (fun y => ∫ s in Ioi (0 : ℝ), chmdPrimeKernel y s * Real.exp (-(s / 2))) lam) atTop (𝓝 0)
  simpa only [integral_zero] using h

/-- The bounded centered source contributes no temporal atom at any positive frequency. -/
theorem remainderFold_temporalCoefficient_zero (v : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (temporalCosineAverage (fun y => remainderFold y v) lam) atTop (𝓝 0) := by
  let F : ℝ → ℝ → ℝ := fun y u =>
    (Ioi (0 : ℝ)).indicator
      (fun u => ccmPrimeDeficitDilationRemainder u * conjugatedLaplacian y (u + v)) u
  let b : ℝ → ℝ := fun u => (Ioi (0 : ℝ)).indicator
    (fun u => (7 / 2) * laplacianBound * Real.exp (-(v / 2)) * Real.exp (-(u / 2))) u
  have hm : Measurable (Function.uncurry F) := by
    exact (((measurable_ccmPrimeDeficitDilationRemainder.comp measurable_snd).mul
      (measurable_conjugatedLaplacian_joint.comp
        (measurable_fst.prodMk (measurable_snd.add measurable_const)))).indicator
          (measurable_snd measurableSet_Ioi))
  have hi : Integrable b := by
    dsimp only [b]
    rw [integrable_indicator_iff measurableSet_Ioi]
    have h : IntegrableOn (fun u : ℝ =>
        (7 / 2) * laplacianBound * Real.exp (-(v / 2)) * Real.exp (-(1 / 2) * u))
          (Ioi (0 : ℝ)) :=
      (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul
        ((7 / 2) * laplacianBound * Real.exp (-(v / 2)))
    refine h.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp only [show -(1 / 2 : ℝ) * u = -(u / 2) by ring]
  have hb : ∀ y u, |F y u| ≤ b u := by
    intro y u
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · simp only [F, b, indicator_of_mem hu, abs_mul]
      calc |ccmPrimeDeficitDilationRemainder u| * |conjugatedLaplacian y (u + v)|
          ≤ (7 / 2) * (laplacianBound * Real.exp (-((u + v) / 2))) :=
            mul_le_mul (abs_ccmPrimeDeficitDilationRemainder_le_uniform (le_of_lt hu))
              (abs_conjugatedLaplacian_le y (u + v)) (abs_nonneg _) (by norm_num)
        _ = _ := by
          rw [show -((u + v) / 2) = -(v / 2) + -(u / 2) by ring, Real.exp_add]
          ring
    · simp only [F, b, indicator_of_notMem hu, abs_zero, le_refl]
  have hlim : ∀ᵐ u : ℝ, Tendsto (temporalCosineAverage (fun y => F y u) lam)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards with u
    by_cases hu : u ∈ Ioi (0 : ℝ)
    · have h := (conjugatedLaplacian_temporalCoefficient_zero (u + v) hlam).const_mul
        (ccmPrimeDeficitDilationRemainder u)
      simpa only [F, indicator_of_mem hu, ← temporalCosineAverage_const_mul, mul_zero] using h
    · change Tendsto (fun T => temporalCosineAverage (fun y => F y u) lam T) atTop (𝓝 0)
      simpa only [F, indicator_of_notMem hu, temporalCosineAverage, zero_mul, integral_zero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0))
  have h := temporalCosineAverage_integral_tendsto hm hi hb hlim
  have heq (y : ℝ) : (∫ u : ℝ, F y u) = remainderFold y v := by
    exact integral_indicator measurableSet_Ioi
  simpa only [heq, integral_zero] using h

end

end RHTower.CHMDChebyshevTransport
