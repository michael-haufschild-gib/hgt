import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceGradientReduction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceTimeField

/-!
# Exact onset remainder of the original theta-cusp mixed source

Use the corpus-constructed full angular inverse in an explicit causal field.
The original unprojected scalar source, including its full gradient term, is
the sum of two actual wave images and a completely specified pulse supported
on the fixed ingoing transition strip. The free Laplace frequency is retained.

This is an identity for the original scalar potential of the mixed stream.
It does not identify the full SS/SV/VV Einstein Peierls pairing or prove its
extinction. The constructed fields' incoming horizon tails remain to be paired.
-/

namespace RHTower.D4BMJointSource
noncomputable section
open _root_.Complex
set_option autoImplicit false

theorem source_fundamental_onset_polynomial (s w u : ℂ) :
    reducedPolynomial s w u =
      -(2*s+1)*(2*s+2)*(1-u^(2 : ℕ))*u +
        s*(s-1)/2*(w-2*s)*(1-u)*u^(2 : ℕ)*(3+(2*s+3)*u) := by
  unfold reducedPolynomial liftSecondPolynomial amplitudeRate
  ring

def sourceSeedPolynomial (s lam u : ℂ) : ℂ :=
  -(2*s+1)*(2*s+2)*u - s*(s-1)/4*((2*s+1)*(2*s+2)-lam)*u^(3 : ℕ)

def sourceSeedFirst (s lam u : ℂ) : ℂ :=
  -(2*s+1)*(2*s+2) - 3*s*(s-1)/4*((2*s+1)*(2*s+2)-lam)*u^(2 : ℕ)

def sourceSeedSecond (s lam u : ℂ) : ℂ :=
  -6*s*(s-1)/4*((2*s+1)*(2*s+2)-lam)*u

-- Free Laplace frequency retained; expression is the exact radial wave after factoring sourceAmplitude.
theorem full_source_onset_polynomial (s w lam u : ℂ) :
    (w^(2 : ℕ)-(amplitudeRate s w u)^(2 : ℕ)-2*s*(u^(2 : ℕ)-1)-lam*(1-u^(2 : ℕ)))*sourceSeedPolynomial s lam u -
      (2*amplitudeRate s w u+2*u)*(u^(2 : ℕ)-1)*sourceSeedFirst s lam u -
      (u^(2 : ℕ)-1)^(2 : ℕ)*sourceSeedSecond s lam u =
    ((2*s+1)*(2*s+2)-lam)*
      (-2*(1-u^(2 : ℕ))*u*((5*s^(2 : ℕ)+15*s+4)/4+
        s*(s-1)/4*((s+2)^(2 : ℕ)-(lam/2-(s+1)*(s+2)))*u^(2 : ℕ))) +
      2*(w-2*s)*(1-u)*((1+u)*sourceSeedFirst s lam u+2*s*sourceSeedPolynomial s lam u) := by
  unfold amplitudeRate sourceSeedPolynomial sourceSeedFirst sourceSeedSecond
  ring


end
end RHTower.D4BMJointSource

namespace RHTower.D4BMJointSource
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
set_option autoImplicit false

def sourceSeedField (s w a T lam : ℂ) (t : ℝ) : ℂ :=
  sourceAmplitude s w a T t*sourceSeedPolynomial s lam (radialUnit t)

def sourceSeedFieldFirst (s w a T lam : ℂ) (t : ℝ) : ℂ :=
  sourceAmplitude s w a T t*(amplitudeRate s w (radialUnit t)*sourceSeedPolynomial s lam (radialUnit t)+
    ((radialUnit t:ℂ)^(2 : ℕ)-1)*sourceSeedFirst s lam (radialUnit t))

def sourceSeedFieldSecond (s w a T lam : ℂ) (t : ℝ) : ℂ :=
  let u : ℂ := radialUnit t
  sourceAmplitude s w a T t*((amplitudeRate s w u)^(2 : ℕ)*sourceSeedPolynomial s lam u+
    2*s*(u^(2 : ℕ)-1)*sourceSeedPolynomial s lam u+
    (2*amplitudeRate s w u+2*u)*(u^(2 : ℕ)-1)*sourceSeedFirst s lam u+
    (u^(2 : ℕ)-1)^(2 : ℕ)*sourceSeedSecond s lam u)

private theorem sourceSeed_radial_derivatives (s lam : ℂ) (t : ℝ) :
    HasDerivAt (fun t => sourceSeedPolynomial s lam (radialUnit t))
      (((radialUnit t:ℂ)^(2 : ℕ)-1)*sourceSeedFirst s lam (radialUnit t)) t ∧
    HasDerivAt (fun t => sourceSeedFirst s lam (radialUnit t))
      (((radialUnit t:ℂ)^(2 : ℕ)-1)*sourceSeedSecond s lam (radialUnit t)) t := by
  have h := (radialUnit_hasDerivAt t).ofReal_comp
  constructor
  · apply ((h.const_mul (-(2*s+1)*(2*s+2))).sub
      ((h.pow 3).const_mul (s*(s-1)/4*((2*s+1)*(2*s+2)-lam)))).congr_deriv
    dsimp [sourceSeedFirst]
    push_cast
    ring
  · apply ((hasDerivAt_const t (-(2*s+1)*(2*s+2))).sub
      ((h.pow 2).const_mul (3*s*(s-1)/4*((2*s+1)*(2*s+2)-lam)))).congr_deriv
    dsimp [sourceSeedSecond]
    push_cast
    ring

theorem sourceSeedField_hasDerivAt (s w a T lam : ℂ) (t : ℝ) :
    HasDerivAt (sourceSeedField s w a T lam) (sourceSeedFieldFirst s w a T lam t) t := by
  apply ((sourceAmplitude_hasDerivAt s w a T t).mul (sourceSeed_radial_derivatives s lam t).1).congr_deriv
  dsimp [sourceSeedFieldFirst]
  ring

theorem sourceSeedFieldFirst_hasDerivAt (s w a T lam : ℂ) (t : ℝ) :
    HasDerivAt (sourceSeedFieldFirst s w a T lam) (sourceSeedFieldSecond s w a T lam t) t := by
  have hu := (radialUnit_hasDerivAt t).ofReal_comp
  have hb := ((hu.sub_const 1).const_mul (2*s)).const_add w
  have hq := sourceSeed_radial_derivatives s lam t
  apply ((sourceAmplitude_hasDerivAt s w a T t).mul
    ((hb.mul hq.1).add (((hu.pow 2).sub_const 1).mul hq.2))).congr_deriv
  dsimp [sourceSeedFieldSecond,amplitudeRate]
  push_cast
  ring

theorem sourceSeedField_derivatives (s w a T lam : ℂ) :
    deriv (sourceSeedField s w a T lam) = sourceSeedFieldFirst s w a T lam ∧
    deriv (deriv (sourceSeedField s w a T lam)) = sourceSeedFieldSecond s w a T lam := by
  have h := funext (fun t => (sourceSeedField_hasDerivAt s w a T lam t).deriv)
  exact ⟨h,by rw [h]; exact funext (fun t => (sourceSeedFieldFirst_hasDerivAt s w a T lam t).deriv)⟩

/-- Exact original source equation with its free target frequency and explicit residual.
No source or target frequency has been identified with the other. -/
theorem sourceSeedField_originalWave (s w a T lam : ℂ) (t : ℝ) :
    w^(2 : ℕ)*sourceSeedField s w a T lam t-deriv (deriv (sourceSeedField s w a T lam)) t-
      lam*(1-(radialUnit t:ℂ)^(2 : ℕ))*sourceSeedField s w a T lam t =
    ((2*s+1)*(2*s+2)-lam)*originalForcing s w a T 1 (lam/2-(s+1)*(s+2)) t+
      2*(w-2*s)*sourceAmplitude s w a T t*(1-(radialUnit t:ℂ))*
        ((1+(radialUnit t:ℂ))*sourceSeedFirst s lam (radialUnit t)+
          2*s*sourceSeedPolynomial s lam (radialUnit t)) := by
  rw [(sourceSeedField_derivatives s w a T lam).2]
  have h := full_source_onset_polynomial s w lam (radialUnit t)
  dsimp only [sourceSeedField,sourceSeedFieldSecond,originalForcing]
  linear_combination sourceAmplitude s w a T t*h
end
end RHTower.D4BMJointSource

namespace RHTower.D4BMJointSource
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- The fixed source-rate onset is evaluated at original ingoing time. -/
def timeSourceSeed (s a lam : ℂ) (τ t : ℝ) : ℂ :=
  sourceSeedField s 0 a 1 lam t*timeOnset (2*s) (τ+t)

def timeSourceSeedFirst (s a lam : ℂ) (τ t : ℝ) : ℂ :=
  sourceSeedFieldFirst s 0 a 1 lam t*timeOnset (2*s) (τ+t)+
    sourceSeedField s 0 a 1 lam t*timeOnsetFirst (2*s) (τ+t)

def timeSourceSeedSecond (s a lam : ℂ) (τ t : ℝ) : ℂ :=
  sourceSeedFieldSecond s 0 a 1 lam t*timeOnset (2*s) (τ+t)+
    2*sourceSeedFieldFirst s 0 a 1 lam t*timeOnsetFirst (2*s) (τ+t)+
    sourceSeedField s 0 a 1 lam t*timeOnsetSecond (2*s) (τ+t)

theorem timeSourceSeed_time (s a lam : ℂ) (τ t : ℝ) :
    HasDerivAt (fun σ => timeSourceSeed s a lam σ t)
      (sourceSeedField s 0 a 1 lam t*timeOnsetFirst (2*s) (τ+t)) τ := by
  simpa only [one_smul,Function.comp_apply,id_eq,timeSourceSeed] using
    ((timeOnset_hasDerivAt (2*s) (τ+t)).scomp τ ((hasDerivAt_id τ).add_const t)).const_mul
      (sourceSeedField s 0 a 1 lam t)

theorem timeSourceSeed_timeSecond (s a lam : ℂ) (τ t : ℝ) :
    deriv (deriv (fun σ => timeSourceSeed s a lam σ t)) τ =
      sourceSeedField s 0 a 1 lam t*timeOnsetSecond (2*s) (τ+t) := by
  have he : deriv (fun σ => timeSourceSeed s a lam σ t) =
      fun σ => sourceSeedField s 0 a 1 lam t*timeOnsetFirst (2*s) (σ+t) :=
    funext (fun σ => (timeSourceSeed_time s a lam σ t).deriv)
  rw [he]
  have hd := ((timeOnsetFirst_hasDerivAt (2*s) (τ+t)).scomp τ
    ((hasDerivAt_id τ).add_const t)).const_mul (sourceSeedField s 0 a 1 lam t)
  simpa only [one_smul,Function.comp_apply,id_eq,timeSourceSeed] using hd.deriv

theorem timeSourceSeed_radial (s a lam : ℂ) (τ t : ℝ) :
    HasDerivAt (timeSourceSeed s a lam τ) (timeSourceSeedFirst s a lam τ t) t := by
  have hh := (timeOnset_hasDerivAt (2*s) (τ+t)).scomp t ((hasDerivAt_id t).const_add τ)
  convert! (sourceSeedField_hasDerivAt s 0 a 1 lam t).mul hh using 1
  simp [timeSourceSeedFirst]

theorem timeSourceSeedFirst_radial (s a lam : ℂ) (τ t : ℝ) :
    HasDerivAt (timeSourceSeedFirst s a lam τ) (timeSourceSeedSecond s a lam τ t) t := by
  have hh := (timeOnset_hasDerivAt (2*s) (τ+t)).scomp t ((hasDerivAt_id t).const_add τ)
  have hh' := (timeOnsetFirst_hasDerivAt (2*s) (τ+t)).scomp t ((hasDerivAt_id t).const_add τ)
  apply (((sourceSeedFieldFirst_hasDerivAt s 0 a 1 lam t).mul hh).add
    ((sourceSeedField_hasDerivAt s 0 a 1 lam t).mul hh')).congr_deriv
  simp only [timeSourceSeedSecond,Complex.real_smul,Complex.ofReal_one,Function.comp_apply]
  ring

theorem timeSourceSeed_radialSecond (s a lam : ℂ) (τ t : ℝ) :
    deriv (deriv (timeSourceSeed s a lam τ)) t = timeSourceSeedSecond s a lam τ t := by
  have he : deriv (timeSourceSeed s a lam τ) = timeSourceSeedFirst s a lam τ :=
    funext (fun x => (timeSourceSeed_radial s a lam τ x).deriv)
  rw [he]
  exact (timeSourceSeedFirst_radial s a lam τ t).deriv

/-- The second onset derivative cancels between time and tortoise derivatives. -/
theorem timeSourceSeed_wave (s a lam : ℂ) (τ t : ℝ) :
    deriv (deriv (fun σ => timeSourceSeed s a lam σ t)) τ-
      deriv (deriv (timeSourceSeed s a lam τ)) t =
      -sourceSeedFieldSecond s 0 a 1 lam t*timeOnset (2*s) (τ+t)-
        2*sourceSeedFieldFirst s 0 a 1 lam t*timeOnsetFirst (2*s) (τ+t) := by
  rw [timeSourceSeed_timeSecond,timeSourceSeed_radialSecond,timeSourceSeedSecond]
  ring

end
end RHTower.D4BMJointSource

namespace RHTower.D4BMJointSource
noncomputable section
set_option autoImplicit false

private theorem sourceSeedField_zero_frequency (s a lam : ℂ) (t : ℝ) :
    -sourceSeedFieldSecond s 0 a 1 lam t-
      lam*(1-(radialUnit t:ℂ)^(2 : ℕ))*sourceSeedField s 0 a 1 lam t =
    ((2*s+1)*(2*s+2)-lam)*originalForcing s 0 a 1 1 (lam/2-(s+1)*(s+2)) t+
      4*s*sourceSeedFieldFirst s 0 a 1 lam t := by
  have h := sourceSeedField_originalWave s 0 a 1 lam t
  rw [(sourceSeedField_derivatives s 0 a 1 lam).2] at h
  dsimp only [sourceSeedFieldFirst,amplitudeRate]
  linear_combination h

/-- Explicit remaining pulse from the fixed, original ingoing onset. -/
def originalSourceOnsetPulse (s a lam : ℂ) (τ t : ℝ) : ℂ :=
  -2*sourceSeedFieldFirst s 0 a 1 lam t*
    (timeOnsetFirst (2*s) (τ+t)-2*s*timeOnset (2*s) (τ+t))

/-- The original projected mixed source is the wave of a specified field minus
one specified onset pulse. All time and radial derivatives are actual derivatives. -/
theorem timeSourceSeed_originalWave (s a lam : ℂ) (τ t : ℝ) :
    deriv (deriv (fun σ => timeSourceSeed s a lam σ t)) τ-
      deriv (deriv (timeSourceSeed s a lam τ)) t-
      lam*(1-(radialUnit t:ℂ)^(2 : ℕ))*timeSourceSeed s a lam τ t =
    ((2*s+1)*(2*s+2)-lam)*originalForcing s 0 a 1 1 (lam/2-(s+1)*(s+2)) t*
      timeOnset (2*s) (τ+t)+originalSourceOnsetPulse s a lam τ t := by
  rw [timeSourceSeed_wave]
  have h := sourceSeedField_zero_frequency s a lam t
  dsimp only [timeSourceSeed,originalSourceOnsetPulse]
  linear_combination timeOnset (2*s) (τ+t)*h

/-- The exponential bulk derivative cancels; only the derivative of the fixed transition remains. -/
theorem originalSourceOnsetPulse_eq (s a lam : ℂ) (τ t : ℝ) :
    originalSourceOnsetPulse s a lam τ t =
      -2*sourceSeedFieldFirst s 0 a 1 lam t*
        (((deriv Real.smoothTransition (τ+t):ℝ)):ℂ)*Complex.exp (2*s*((τ+t:ℝ):ℂ)) := by
  dsimp [originalSourceOnsetPulse,timeOnsetFirst,timeOnset]
  ring

/-- The explicit remainder is confined to the original ingoing transition strip. -/
theorem originalSourceOnsetPulse_zero_outside (s a lam : ℂ) (τ t : ℝ)
    (h : τ+t ∉ Set.Icc (0:ℝ) 1) : originalSourceOnsetPulse s a lam τ t = 0 := by
  rw [originalSourceOnsetPulse_eq,
    GaloisForLFunctions.HTGeometry.deriv_smoothTransition_eq_zero_of_notMem h]
  simp
end
end RHTower.D4BMJointSource

namespace RHTower.D4BMJointSource
noncomputable section
set_option autoImplicit false

theorem timeSourceSeed_zero_before_onset (s a lam : ℂ) (τ t : ℝ) (h : τ+t ≤ 0) :
    timeSourceSeed s a lam τ t = 0 := by
  simp [timeSourceSeed,timeOnset_zero_of_nonpos (2*s) h]

theorem timeSourceSeed_ads_zero (s a lam : ℂ) (τ : ℝ) : timeSourceSeed s a lam τ 0 = 0 := by
  simp [timeSourceSeed,sourceSeedField,sourceSeedPolynomial,radialUnit]

end
end RHTower.D4BMJointSource

namespace RHTower.D4BMJointSource
open GaloisForLFunctions.HTGeometry D4BMModularCore D4BMHorizon D4BMAngularSeries D4BMGlobalAngularResponse UpperHalfPlane
noncomputable section
set_option autoImplicit false

/-- The constructed original modular inverse, with its actual smooth ingoing onset. -/
def timeAngularSeedField (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t : ℝ) (z : Point) : ℂ :=
  timeSourceSeed (physicalRate q branch) a (parameter q branch) τ t*fullAngularField q branch z

private theorem parameter_eq_source (q : XiZeroCopy) (branch : Bool) :
    parameter q branch=(2*physicalRate q branch+1)*(2*physicalRate q branch+2) :=
  parameter_physicalRate q branch

private theorem timeAngularSeedField_wave (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t : ℝ) (z : Point) (hz : 0 < z 1) :
    timeFieldWave (timeAngularSeedField q branch a) τ t z =
      originalSourceOnsetPulse (physicalRate q branch) a (parameter q branch) τ t*fullAngularField q branch z-
      parameter q branch*(1-(radialUnit t:ℂ)^(2 : ℕ))*
        timeSourceSeed (physicalRate q branch) a (parameter q branch) τ t*fullSquarePotential q z := by
  have hL : scalarLaplacian (fun y =>
      timeSourceSeed (physicalRate q branch) a (parameter q branch) τ t*fullAngularField q branch y) z =
      timeSourceSeed (physicalRate q branch) a (parameter q branch) τ t*scalarLaplacian (fullAngularField q branch) z := by
    rw [scalarLaplacian_eq _ z hz,scalarLaplacian_eq _ z hz]
    apply hyperbolicLaplacian_const_mul
    have h := (contDiffAt_infty.mp (fullAngularField_smooth q branch z hz)) 2
    simpa using h
  have h := timeSourceSeed_originalWave (physicalRate q branch) a (parameter q branch) τ t
  rw [← parameter_eq_source q branch,sub_self,zero_mul,zero_mul,zero_add] at h
  unfold timeFieldWave timeAngularSeedField
  simp only [deriv_mul_const_field',deriv_mul_const_field]
  rw [hL,fullAngularField_equation q branch z hz]
  dsimp only [fullSquarePotential]
  linear_combination fullAngularField q branch z*h

private theorem timeReducedCoefficient_sourceSeed (s a : ℂ) (τ t : ℝ) :
    timeReducedCoefficient s a τ t =
      (1-(radialUnit t:ℂ)^(2 : ℕ))*timeSourceSeed s a ((2*s+1)*(2*s+2)) τ t+
      2*radialLiftFirst s 0 a 1 t*(timeOnsetFirst (2*s) (τ+t)-2*s*timeOnset (2*s) (τ+t)) := by
  have h := source_fundamental_onset_polynomial s 0 (radialUnit t)
  dsimp only [timeReducedCoefficient,reducedCoefficient,timeSourceSeed,sourceSeedField,
    sourceSeedPolynomial,radialLiftFirst,liftFirstPolynomial,amplitudeRate]
  linear_combination sourceAmplitude s 0 a 1 t*timeOnset (2*s) (τ+t)*h

/-- The explicit pulse of the full, unprojected original scalar source. -/
def fullSourceOnsetPulse (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t : ℝ) (z : Point) : ℂ :=
  originalSourceOnsetPulse (physicalRate q branch) a (parameter q branch) τ t*fullAngularField q branch z+
    2*parameter q branch*radialLiftFirst (physicalRate q branch) 0 a 1 t*
      (timeOnsetFirst (2*physicalRate q branch) (τ+t)-
        2*physicalRate q branch*timeOnset (2*physicalRate q branch) (τ+t))*fullSquarePotential q z

/-- Both wave terms contain actual time, radial, and angular derivatives. The full
literal theta source and the fixed onset pulse are identified without a response premise. -/
theorem fullSourceOnset_wave_identity (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t : ℝ) (z : Point) (hz : 0 < z 1) :
    timeFieldWave (timeAngularSeedField q branch a) τ t z-
      parameter q branch*timeFieldWave (timeLiftField q branch a) τ t z =
      -parameter q branch*timeOriginalForcing q branch a τ t z+fullSourceOnsetPulse q branch a τ t z := by
  rw [timeAngularSeedField_wave q branch a τ t z hz,
    timeOriginalForcing_gradient_absorption q branch a τ t z hz,
    timeReducedCoefficient_sourceSeed]
  rw [← parameter_eq_source q branch]
  dsimp only [fullSourceOnsetPulse]
  ring

/-- An explicit transition derivative carries the entire retained remainder. -/
theorem fullSourceOnsetPulse_transition (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t : ℝ) (z : Point) :
    fullSourceOnsetPulse q branch a τ t z =
      (-2*sourceSeedFieldFirst (physicalRate q branch) 0 a 1 (parameter q branch) t*fullAngularField q branch z+
        2*parameter q branch*radialLiftFirst (physicalRate q branch) 0 a 1 t*fullSquarePotential q z)*
      (((deriv Real.smoothTransition (τ+t):ℝ)):ℂ)*Complex.exp (2*physicalRate q branch*((τ+t:ℝ):ℂ)) := by
  rw [fullSourceOnsetPulse,originalSourceOnsetPulse_eq]
  dsimp only [timeOnsetFirst,timeOnset]
  ring

/-- Localization is in ingoing time, not compact support in the whole spacetime. -/
theorem fullSourceOnsetPulse_zero_outside (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t : ℝ) (z : Point) (h : τ+t ∉ Set.Icc (0:ℝ) 1) :
    fullSourceOnsetPulse q branch a τ t z = 0 := by
  rw [fullSourceOnsetPulse_transition,deriv_smoothTransition_eq_zero_of_notMem h]
  simp

/-- The complete original scalar source splits into two explicitly constructed wave
images and one fixed onset pulse. No angular inverse or extinction premise is supplied. -/
theorem timeOriginalForcing_full_onset_decomposition (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (τ t : ℝ) (z : UpperHalfPlane) :
    timeOriginalForcing q branch a τ t (coordinates z) =
      timeFieldWave (timeLiftField q branch a) τ t (coordinates z)-
      timeFieldWave (timeAngularSeedField q branch a) τ t (coordinates z)/parameter q branch+
      fullSourceOnsetPulse q branch a τ t (coordinates z)/parameter q branch := by
  have hp : parameter q branch ≠ 0 := by
    intro he
    have hi : (parameter q branch).im ≠ 0 := by
      cases branch
      · exact (D4BMQuadraticMixedSource.xi_resolvent_parameter_nonreal q).2
      · exact (D4BMQuadraticMixedSource.xi_resolvent_parameter_nonreal q).1
    rw [he] at hi
    exact hi rfl
  have h := fullSourceOnset_wave_identity q branch a τ t (coordinates z) z.im_pos
  field_simp [hp]
  linear_combination h

end
end RHTower.D4BMJointSource
