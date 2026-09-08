import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceVectorDecay

/-! Source transforms are admitted in the original Hilbert space for Re(w) > -2. -/
open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMJointWave D4BMModularCore
noncomputable section

/-- The two horizon zeros persist at independent frequency. -/
theorem reducedCoefficient_frequency_horizon (s w a T : ℂ) (t : ℝ) :
    reducedCoefficient s w a T t = Complex.exp ((w+2)*(t:ℂ))*
      (T*(sourceHorizonProfile s a 0 (radialUnit t)+w*sourceHorizonProfile s a 1 (radialUnit t))) := by
  rw [reducedCoefficient_frequency s w a T t,reducedCoefficient_horizon]
  rw [show 2*w*radialLiftFirst s 0 a 1 t = w*(2*radialLiftFirst s 0 a 1 t) by ring,
    radialLiftFirst_horizon]
  have he : Complex.exp (w*(t:ℂ))*(Real.exp (2*t):ℂ) = Complex.exp ((w+2)*(t:ℂ)) := by
    rw [Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (Complex.exp (w*(t:ℂ))*(Real.exp (2*t):ℂ))*
        (T*(sourceHorizonProfile s a 0 (radialUnit t)+w*sourceHorizonProfile s a 1 (radialUnit t))) := by ring
    _ = _ := by rw [he]

/-- The literal reduced frequency source has original L² admission throughout the enlarged source chamber. -/
theorem reducedCoefficient_memLp_horizon (s w a T : ℂ) (hw : -2 < w.re) :
    MemLp (reducedCoefficient s w a T) 2 radialMeasure := by
  have h := laplaceProfile_memLp (w+2) (by simp; linarith)
    (fun u => T*(sourceHorizonProfile s a 0 u+w*sourceHorizonProfile s a 1 u))
    (continuousOn_const.mul ((sourceHorizonProfile_continuousOn s a 0).add
      (continuousOn_const.mul (sourceHorizonProfile_continuousOn s a 1))))
  exact h.ae_eq (Eventually.of_forall (fun t => (reducedCoefficient_frequency_horizon s w a T t).symm))

/-- One damping exponent simultaneously controls time integrability and the entire radial horizon. -/
theorem sourceTransform_exponent (w : ℂ) (hw : -2 < w.re) :
    1-w.re/2 < 2 ∧ 0 < w.re+(1-w.re/2) := by constructor <;> linarith

/-- Norm convergence of the genuine radial Bochner Laplace integral, extending across Re(w)=0. -/
theorem timeRadialSourceVector_laplace_integrable (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : -2 < w.re) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ)) •
      timeRadialSourceVector (physicalRate q branch) a τ) (Ioi 0) := by
  let c := 1-w.re/2
  obtain ⟨hc,hwc⟩ := sourceTransform_exponent w hw
  obtain ⟨B,hB,hb⟩ := timeRadialSourceVector_bound q branch a c hc
  apply ((integrableOn_exp_mul_Ioi (by dsimp [c]; linarith : -(w.re+c) < 0) 0).const_mul B).mono'
    (((by fun_prop : Continuous (fun τ : ℝ => Complex.exp (-w*(τ:ℂ)))).smul
      (timeRadialSourceVector_continuous q branch a)).aestronglyMeasurable)
  filter_upwards [] with τ
  change ‖Complex.exp (-w*(τ:ℂ)) • timeRadialSourceVector (physicalRate q branch) a τ‖ ≤
    B*Real.exp (-(w.re+c)*τ)
  rw [norm_smul,Complex.norm_exp]
  have hre : (-w*(τ:ℂ)).re = -w.re*τ := by simp
  rw [hre]
  calc
    _ ≤ Real.exp (-w.re*τ)*(B*Real.exp (-c*τ)) := mul_le_mul_of_nonneg_left (hb τ) (Real.exp_pos _).le
    _ = B*Real.exp (-(w.re+c)*τ) := by
      rw [mul_left_comm,← Real.exp_add]
      congr 2
      ring

/-- The original joint spatial source has a norm-convergent Bochner Laplace transform in the enlarged chamber. -/
theorem timeCuspMainVector_laplace_integrable (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : -2 < w.re) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ)) • timeCuspMainVector q branch a τ) (Ioi 0) := by
  have h := (l2SeparatedProductContinuousBilinear.flip (squareResidualVector q)).integrable_comp
    (timeRadialSourceVector_laplace_integrable q branch a w hw)
  apply h.congr
  filter_upwards [] with τ
  rw [map_smul]
  simp only [ContinuousLinearMap.flip_apply,l2SeparatedProductContinuousBilinear_apply,
    timeCuspMainVector_separated]

end
end RHTower.D4BMJointSource
