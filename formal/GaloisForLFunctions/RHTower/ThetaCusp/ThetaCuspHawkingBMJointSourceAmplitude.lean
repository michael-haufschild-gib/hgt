import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceRadialUnit
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLaplaceSourceProfile

/-! The independent-frequency radial amplitude is the original ingoing source amplitude. -/
open Complex Set
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMIngoingCoordinates
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def sourceAmplitude (s w a T : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (w*(t:ℂ))*power (2*s) (1+radialUnit t)*a^(2 : ℕ)*T

def amplitudeRate (s w u : ℂ) : ℂ := w+2*s*(u-1)

/-- Actual radial differentiation retains the independent transform frequency and physical rate. -/
theorem sourceAmplitude_hasDerivAt (s w a T : ℂ) (t : ℝ) :
    HasDerivAt (sourceAmplitude s w a T)
      (amplitudeRate s w (radialUnit t)*sourceAmplitude s w a T t) t := by
  have hu := radialUnit_hasDerivAt t
  have hp := (power_derivatives (2*s) (radialUnit_add_one_pos t)).1.scomp t (hu.const_add 1)
  have he := ((hasDerivAt_id t).ofReal_comp.const_mul w).cexp
  have hd := ((he.mul hp).mul_const (a^(2 : ℕ))).mul_const T
  apply hd.congr_deriv
  dsimp only [sourceAmplitude,amplitudeRate,powerFirst,Function.comp_apply,id_eq]
  simp only [Complex.real_smul]
  have hn : ((1+radialUnit t : ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (radialUnit_add_one_pos t))
  push_cast at hn ⊢
  field_simp
  ring

/-- This is the literal ingoing envelope squared, including the fixed onset transform factor. -/
theorem sourceAmplitude_original (s w a T : ℂ) (t : ℝ) :
    sourceAmplitude s w a T t =
      Complex.exp (w*(t:ℂ))*(compactEnvelope s a 0 (radialUnit t))^(2 : ℕ)*T := by
  have hn : ((1+radialUnit t : ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (radialUnit_add_one_pos t))
  have hp : power (2*s) (1+radialUnit t) =
      (Complex.exp (s*Complex.log (1+(radialUnit t:ℂ))))^(2 : ℕ) := by
    rw [power,Complex.cpow_def_of_ne_zero hn,pow_two,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [sourceAmplitude,hp]
  simp only [compactEnvelope,Complex.ofReal_zero,zero_add]
  ring

/-- Exact normalized current coefficient, retaining both full angular covectors. -/
def originalForcing (s w a T J K : ℂ) (t : ℝ) : ℂ :=
  -2*(1-(radialUnit t:ℂ)^(2 : ℕ))*(radialUnit t:ℂ)*sourceAmplitude s w a T t*
    (((5*s^(2 : ℕ)+15*s+4)/4)*J+s*(s-1)*(radialUnit t:ℂ)^(2 : ℕ)/4*((s+2)^(2 : ℕ)*J-K))

/-- The displayed forcing is exactly the original source-normalized mixed current. -/
theorem originalForcing_current (s w a T J K : ℂ) (t : ℝ) (ht : t < 0) :
    originalForcing s w a T J K t =
      -2*((D4BMJointWave.tortoiseRadius t : ℂ)^(2 : ℕ)-1)/(D4BMJointWave.tortoiseRadius t:ℂ)^(3 : ℕ)*
      (Complex.exp (w*(t:ℂ))*D4BMQuadraticMixedSource.current s (D4BMJointWave.tortoiseRadius t)
        (compactEnvelope s a 0 (D4BMJointWave.tortoiseRadius t:ℂ)⁻¹) J K*T) := by
  have hr : (D4BMJointWave.tortoiseRadius t : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_trans (by norm_num) (D4BMJointWave.tortoiseRadius_exterior t ht)))
  unfold originalForcing
  rw [sourceAmplitude_original,radialUnit_inverse_radius]
  push_cast
  unfold D4BMQuadraticMixedSource.current
  field_simp
  ring

end
end RHTower.D4BMJointSource
