import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceFrequencyAffine
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceOnsetJets

/-! The original lift with its fixed ingoing onset has actual time and radial derivatives. -/
namespace RHTower.D4BMJointSource
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The fixed source-rate onset is evaluated at original ingoing time. -/
def timeRadialLift (s a : ℂ) (τ t : ℝ) : ℂ :=
  radialLift s 0 a 1 t*timeOnset (2*s) (τ+t)

def timeRadialLiftFirst (s a : ℂ) (τ t : ℝ) : ℂ :=
  radialLiftFirst s 0 a 1 t*timeOnset (2*s) (τ+t)+
    radialLift s 0 a 1 t*timeOnsetFirst (2*s) (τ+t)

def timeRadialLiftSecond (s a : ℂ) (τ t : ℝ) : ℂ :=
  radialLiftSecond s 0 a 1 t*timeOnset (2*s) (τ+t)+
    2*radialLiftFirst s 0 a 1 t*timeOnsetFirst (2*s) (τ+t)+
    radialLift s 0 a 1 t*timeOnsetSecond (2*s) (τ+t)

theorem timeRadialLift_time (s a : ℂ) (τ t : ℝ) :
    HasDerivAt (fun σ => timeRadialLift s a σ t)
      (radialLift s 0 a 1 t*timeOnsetFirst (2*s) (τ+t)) τ := by
  simpa only [one_smul,Function.comp_apply,id_eq,timeRadialLift] using
    ((timeOnset_hasDerivAt (2*s) (τ+t)).scomp τ ((hasDerivAt_id τ).add_const t)).const_mul
      (radialLift s 0 a 1 t)

theorem timeRadialLift_timeSecond (s a : ℂ) (τ t : ℝ) :
    deriv (deriv (fun σ => timeRadialLift s a σ t)) τ =
      radialLift s 0 a 1 t*timeOnsetSecond (2*s) (τ+t) := by
  have he : deriv (fun σ => timeRadialLift s a σ t) =
      fun σ => radialLift s 0 a 1 t*timeOnsetFirst (2*s) (σ+t) :=
    funext (fun σ => (timeRadialLift_time s a σ t).deriv)
  rw [he]
  have hd := ((timeOnsetFirst_hasDerivAt (2*s) (τ+t)).scomp τ
    ((hasDerivAt_id τ).add_const t)).const_mul (radialLift s 0 a 1 t)
  simpa only [one_smul,Function.comp_apply,id_eq,timeRadialLift] using hd.deriv

theorem timeRadialLift_radial (s a : ℂ) (τ t : ℝ) :
    HasDerivAt (timeRadialLift s a τ) (timeRadialLiftFirst s a τ t) t := by
  have hh := (timeOnset_hasDerivAt (2*s) (τ+t)).scomp t ((hasDerivAt_id t).const_add τ)
  convert! (radialLift_hasDerivAt s 0 a 1 t).mul hh using 1
  simp [timeRadialLiftFirst]

theorem timeRadialLiftFirst_radial (s a : ℂ) (τ t : ℝ) :
    HasDerivAt (timeRadialLiftFirst s a τ) (timeRadialLiftSecond s a τ t) t := by
  have hh := (timeOnset_hasDerivAt (2*s) (τ+t)).scomp t ((hasDerivAt_id t).const_add τ)
  have hh' := (timeOnsetFirst_hasDerivAt (2*s) (τ+t)).scomp t ((hasDerivAt_id t).const_add τ)
  apply (((radialLiftFirst_hasDerivAt s 0 a 1 t).mul hh).add
    ((radialLift_hasDerivAt s 0 a 1 t).mul hh')).congr_deriv
  simp only [timeRadialLiftSecond,Complex.real_smul,Complex.ofReal_one,Function.comp_apply]
  ring

theorem timeRadialLift_radialSecond (s a : ℂ) (τ t : ℝ) :
    deriv (deriv (timeRadialLift s a τ)) t = timeRadialLiftSecond s a τ t := by
  have he : deriv (timeRadialLift s a τ) = timeRadialLiftFirst s a τ :=
    funext (fun x => (timeRadialLift_radial s a τ x).deriv)
  rw [he]
  exact (timeRadialLiftFirst_radial s a τ t).deriv

/-- The second onset derivative cancels between time and tortoise derivatives. -/
theorem timeRadialLift_wave (s a : ℂ) (τ t : ℝ) :
    deriv (deriv (fun σ => timeRadialLift s a σ t)) τ-
      deriv (deriv (timeRadialLift s a τ)) t =
      -radialLiftSecond s 0 a 1 t*timeOnset (2*s) (τ+t)-
        2*radialLiftFirst s 0 a 1 t*timeOnsetFirst (2*s) (τ+t) := by
  rw [timeRadialLift_timeSecond,timeRadialLift_radialSecond,timeRadialLiftSecond]
  ring

end
end RHTower.D4BMJointSource
