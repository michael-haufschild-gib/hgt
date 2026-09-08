import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeField
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceOnsetLaplace
import GaloisForLFunctions.HTGeometry.CausalLaplaceDelay

/-! The actual delayed time source has the original independent-frequency transform. -/
open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMHorizon
noncomputable section

private theorem delayedOnset_integrable (v w : ℂ) (hw : v.re < w.re) (t : ℝ) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ))*timeOnset v (τ+t)) (Ioi 0) :=
  causal_laplace_delay_integrable _ (fun _ hu => timeOnset_zero_of_nonpos v hu.le) _
    (timeOnset_integrable v w hw) t

private theorem delayedOnsetFirst_integrable (v w : ℂ) (hw : v.re < w.re) (t : ℝ) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ))*timeOnsetFirst v (τ+t)) (Ioi 0) :=
  causal_laplace_delay_integrable _ (fun _ hu => timeOnsetFirst_zero_of_neg v hu) _
    (timeOnsetFirst_integrable v w hw) t

/-- Absolute convergence of the actual reduced time source, including its onset derivative. -/
theorem timeReducedCoefficient_integrable (s a w : ℂ) (hw : (2*s).re < w.re) (t : ℝ) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ))*timeReducedCoefficient s a τ t) (Ioi 0) := by
  have h0 := (delayedOnset_integrable (2*s) w hw t).const_mul (reducedCoefficient s 0 a 1 t)
  have h1 := (delayedOnsetFirst_integrable (2*s) w hw t).const_mul (2*radialLiftFirst s 0 a 1 t)
  apply (h0.add h1).congr
  filter_upwards [] with τ
  simp only [timeReducedCoefficient,Pi.add_apply]
  ring

/-- The complete time-domain reduction transforms into the original reduced coefficient,
with the true radial delay and the fixed smooth-onset transform retained. -/
theorem timeReducedCoefficient_laplace (s a w : ℂ) (hw : (2*s).re < w.re)
    (t : ℝ) (ht : t ≤ 0) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ))*timeReducedCoefficient s a τ t) =
      reducedCoefficient s w a (onsetTransform (2*s) w) t := by
  have h0 := delayedOnset_integrable (2*s) w hw t
  have h1 := delayedOnsetFirst_integrable (2*s) w hw t
  have he0 := causal_laplace_delay (timeOnset (2*s))
    (fun _ hu => timeOnset_zero_of_nonpos (2*s) hu.le) w t ht
  have he1 := causal_laplace_delay (timeOnsetFirst (2*s))
    (fun _ hu => timeOnsetFirst_zero_of_neg (2*s) hu) w t ht
  rw [timeOnset_laplace] at he0
  rw [timeOnsetFirst_laplace (2*s) w hw] at he1
  have he : (fun τ : ℝ => Complex.exp (-w*(τ:ℂ))*timeReducedCoefficient s a τ t) =
      fun τ : ℝ => reducedCoefficient s 0 a 1 t*(Complex.exp (-w*(τ:ℂ))*timeOnset (2*s) (τ+t))+
        (2*radialLiftFirst s 0 a 1 t)*(Complex.exp (-w*(τ:ℂ))*timeOnsetFirst (2*s) (τ+t)) := by
    ext τ
    simp only [timeReducedCoefficient]
    ring
  rw [he,integral_add (h0.const_mul _) (h1.const_mul _),integral_const_mul,integral_const_mul,
    he0,he1,reducedCoefficient_frequency s w a (onsetTransform (2*s) w) t]
  ring

theorem originalForcing_frequency (s w a T J K : ℂ) (t : ℝ) :
    originalForcing s w a T J K t = Complex.exp (w*(t:ℂ))*T*originalForcing s 0 a 1 J K t := by
  unfold originalForcing
  rw [sourceAmplitude_frequency]
  ring

/-- Absolute convergence of the actual full angular current source at each original spatial point. -/
theorem timeOriginalForcing_integrable (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : (2*physicalRate q branch).re < w.re) (t : ℝ) (z : Point) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ))*timeOriginalForcing q branch a τ t z) (Ioi 0) := by
  apply ((delayedOnset_integrable (2*physicalRate q branch) w hw t).const_mul
    (originalForcing (physicalRate q branch) 0 a 1 (fullSquarePotential q z) (fullGradientEnergy q z/2) t)).congr
  filter_upwards [] with τ
  simp only [timeOriginalForcing]
  ring

/-- The full original time source has exactly the frequency-domain source used by the physical Green inverse. -/
theorem timeOriginalForcing_laplace (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (t : ℝ) (ht : t ≤ 0) (z : Point) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ))*timeOriginalForcing q branch a τ t z) =
      originalForcing (physicalRate q branch) w a (onsetTransform (2*physicalRate q branch) w)
        (fullSquarePotential q z) (fullGradientEnergy q z/2) t := by
  have he := causal_laplace_delay (timeOnset (2*physicalRate q branch))
    (fun _ hu => timeOnset_zero_of_nonpos _ hu.le) w t ht
  rw [timeOnset_laplace] at he
  unfold timeOriginalForcing
  simp_rw [mul_left_comm (Complex.exp (-w*(_ : ℂ)))]
  rw [integral_const_mul,he,originalForcing_frequency (physicalRate q branch) w a
    (onsetTransform (2*physicalRate q branch) w) (fullSquarePotential q z) (fullGradientEnergy q z/2) t]
  ring

/-- The differentiated original lift has an absolutely convergent time transform. -/
theorem timeLiftField_wave_integrable (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : (2*physicalRate q branch).re < w.re) (t : ℝ) (z : Point) (hz : 0 < z 1) :
    IntegrableOn (fun τ : ℝ => Complex.exp (-w*(τ:ℂ))*timeFieldWave (timeLiftField q branch a) τ t z)
      (Ioi 0) := by
  have ho := timeOriginalForcing_integrable q branch a w hw t z
  have hr := (timeReducedCoefficient_integrable (physicalRate q branch) a w hw t).mul_const
    (fullSquarePotential q z)
  apply (ho.sub hr).congr
  filter_upwards [] with τ
  have he := timeOriginalForcing_gradient_absorption q branch a τ t z hz
  dsimp only [Pi.sub_apply]
  linear_combination Complex.exp (-w*(τ:ℂ))*he

/-- The actual time wave of the full angular lift transforms into the original frequency wave,
with every onset term retained through the exact source identity. -/
theorem timeLiftField_wave_laplace (q : XiZeroCopy) (branch : Bool) (a w : ℂ)
    (hw : (2*physicalRate q branch).re < w.re) (t : ℝ) (ht : t ≤ 0)
    (z : Point) (hz : 0 < z 1) :
    (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ))*timeFieldWave (timeLiftField q branch a) τ t z) =
      separatedScalarWave w (radialLift (physicalRate q branch) w a
        (onsetTransform (2*physicalRate q branch) w)) (fullSquarePotential q) t z := by
  have ho := timeOriginalForcing_integrable q branch a w hw t z
  have hr := timeReducedCoefficient_integrable (physicalRate q branch) a w hw t
  calc
    _ = (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ))*timeOriginalForcing q branch a τ t z)-
        (∫ τ in Ioi (0:ℝ), Complex.exp (-w*(τ:ℂ))*timeReducedCoefficient (physicalRate q branch) a τ t)*
          fullSquarePotential q z := by
      rw [← integral_mul_const,← integral_sub ho (hr.mul_const _)]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro τ _
      have he := timeOriginalForcing_gradient_absorption q branch a τ t z hz
      linear_combination -Complex.exp (-w*(τ:ℂ))*he
    _ = _ := by
      rw [timeOriginalForcing_laplace q branch a w t ht z,
        timeReducedCoefficient_laplace (physicalRate q branch) a w hw t ht]
      have he := scalar_gradient_absorption q branch w a
        (onsetTransform (2*physicalRate q branch) w) t z hz
      linear_combination he

end
end RHTower.D4BMJointSource
