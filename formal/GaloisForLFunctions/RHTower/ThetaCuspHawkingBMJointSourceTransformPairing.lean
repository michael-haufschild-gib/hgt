import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTransformChamber

/-! Absolute Fubini control for every original radial L² test, before source-transform identification. -/
open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore
noncomputable section

/-- The original source and every radial L² probe have an absolutely integrable joint time-space pairing. -/
theorem timeRadialSourceVector_pairing_integrable (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : -2 < w.re) (u : Lp ℂ 2 radialMeasure) :
    Integrable (fun p : ℝ × ℝ => star (u p.2)*
      (Complex.exp (-w*(p.1:ℂ))*timeReducedCoefficient (physicalRate q branch) a p.1 p.2))
      ((volume.restrict (Ioi (0:ℝ))).prod radialMeasure) := by
  let c := 1-w.re/2
  obtain ⟨hc,hwc⟩ := sourceTransform_exponent w hw
  obtain ⟨C,hC,hb⟩ := timeReducedCoefficient_physical_bound q branch a c hc
  have hspace : Integrable (fun t : ℝ => ‖u t‖*Real.exp ((2-c)*t)) radialMeasure :=
    (Lp.memLp u).norm.integrable_mul (horizonEnvelope_memLp c hc)
  have htime : Integrable (fun τ : ℝ => C*Real.exp (-(w.re+c)*τ)) (volume.restrict (Ioi 0)) :=
    (integrableOn_exp_mul_Ioi (by dsimp [c]; linarith : -(w.re+c)<0) 0).const_mul C
  have hcont : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (-w*(p.1:ℂ))*timeReducedCoefficient (physicalRate q branch) a p.1 p.2) :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ => Complex.exp (-w*(p.1:ℂ)))).mul
      (timeReducedCoefficient_joint_continuous (physicalRate q branch) a)
  apply (htime.mul_prod hspace).mono'
    (((Lp.aestronglyMeasurable u).aemeasurable.comp_snd.aestronglyMeasurable.star).mul
      hcont.aestronglyMeasurable)
  have hneg : ∀ᵐ p : ℝ × ℝ ∂(volume.restrict (Ioi (0:ℝ))).prod radialMeasure, p.2 < 0 :=
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Iio)
  filter_upwards [hneg] with p hp
  change ‖star (u p.2)*(Complex.exp (-w*(p.1:ℂ))*
    timeReducedCoefficient (physicalRate q branch) a p.1 p.2)‖ ≤
      (C*Real.exp (-(w.re+c)*p.1))*(‖u p.2‖*Real.exp ((2-c)*p.2))
  rw [norm_mul,norm_star,norm_mul,Complex.norm_exp]
  have hre : (-w*(p.1:ℂ)).re = -w.re*p.1 := by simp
  rw [hre]
  calc
    _ ≤ ‖u p.2‖*(Real.exp (-w.re*p.1)*(C*Real.exp (-c*p.1)*Real.exp ((2-c)*p.2))) := by
      gcongr
      exact hb p.1 p.2 hp
    _ = (C*Real.exp (-(w.re+c)*p.1))*(‖u p.2‖*Real.exp ((2-c)*p.2)) := by
      have he : Real.exp (-w.re*p.1)*Real.exp (-c*p.1) = Real.exp (-(w.re+c)*p.1) := by
        rw [← Real.exp_add]
        congr 1
        ring
      linear_combination ‖u p.2‖*C*Real.exp ((2-c)*p.2)*he

/-- The Bochner integral is identified against every original radial test by genuine absolute Fubini. -/
theorem timeRadialSourceVector_laplace_pairing (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : -2 < w.re) (u : Lp ℂ 2 radialMeasure) :
    (∫ τ in Ioi (0:ℝ), ∫ t, star (u t)*
      (Complex.exp (-w*(τ:ℂ))*timeReducedCoefficient (physicalRate q branch) a τ t) ∂radialMeasure) =
      ∫ t, star (u t)*reducedCoefficient (physicalRate q branch) w a
        (onsetTransform (2*physicalRate q branch) w) t ∂radialMeasure := by
  rw [integral_integral_swap (timeRadialSourceVector_pairing_integrable q branch a w hw u)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
  rw [integral_const_mul,timeReducedCoefficient_laplace (physicalRate q branch) a w _ t ht.le]
  have h := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at h
  exact h.trans hw

end
end RHTower.D4BMJointSource
