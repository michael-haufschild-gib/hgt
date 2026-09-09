import GaloisForLFunctions.RHTower.SelbergThetaNativeEnergy

/-!
# All real Mellin moments of the native theta source

Every tilted actual zero mode has an absolutely integrable derivative and
vanishing endpoints. Its first-order equation evaluates every real Mellin
moment of the half-density seed with the exact spectral denominator.
-/

open Complex Set Filter Topology MeasureTheory
namespace RHTower.SelbergThetaNativeMoments
open SelbergThetaSourcePhase SelbergThetaSourceVariance SelbergThetaNativeSource
noncomputable section

private theorem tilt_pos (a x : ℝ) : 0 < tiltedSource a x :=
  mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all _)

private theorem tilt_integrable (a : ℝ) : Integrable (tiltedSource a) :=
  HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource a

private theorem tilt_bound (a : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ x, tiltedSource a x ≤ C := by
  obtain ⟨C,hC0,hC⟩ := positiveProfile_power_bound ((1-a)/2)
  refine ⟨C,hC0,?_⟩
  intro x
  have hb := hC (Real.exp (2*x)) (Real.exp_pos _)
  have hx : 2*x/2=x := by ring
  have he : Real.exp ((a-1)*x)*Real.exp x = Real.exp (a*x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    tiltedSource a x = Real.exp ((a-1)*x)*positiveProfile (Real.exp (2*x)) := by
      rw [positiveProfile, Real.log_exp, hx, ← mul_assoc, he]
      rfl
    _ ≤ Real.exp ((a-1)*x)*(C*(Real.exp (2*x))^((1-a)/2)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = C := by
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      rw [show Real.exp ((a-1)*x)*(C*Real.exp (2*x*((1-a)/2))) =
        C*(Real.exp ((a-1)*x)*Real.exp (2*x*((1-a)/2))) by ring,
        ← Real.exp_add, show (a-1)*x+2*x*((1-a)/2)=0 by ring, Real.exp_zero,mul_one]

private theorem tilt_top_bound (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, tiltedSource a x ≤ C*Real.exp (-x) := by
  obtain ⟨C,hC0,hC⟩ := tilt_bound (a+1)
  refine ⟨C,hC0,?_⟩
  intro x
  have he : tiltedSource a x = Real.exp (-x)*tiltedSource (a+1) x := by
    unfold tiltedSource
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [he]
  nlinarith [hC x,Real.exp_pos (-x)]

private theorem tilt_bot_bound (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, tiltedSource a x ≤ C*Real.exp x := by
  obtain ⟨C,hC0,hC⟩ := tilt_bound (a-1)
  refine ⟨C,hC0,?_⟩
  intro x
  have he : tiltedSource a x = Real.exp x*tiltedSource (a-1) x := by
    unfold tiltedSource
    rw [← mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [he]
  nlinarith [hC x,Real.exp_pos x]

/-- Every real exponential tilt of the actual zero mode is absolutely integrable. -/
theorem weightedMode_integrable (q : XiZeroCopy) (a : ℝ) : Integrable (weightedMode q a) := by
  obtain ⟨C,_,hC⟩ := sourceRatio_bounded q
  have h := (tilt_integrable a).ofReal.mul_bdd (continuous_sourceRatio q).aestronglyMeasurable
    (Eventually.of_forall hC)
  have he : weightedMode q a = fun x => (tiltedSource a x:ℂ)*sourceRatio q x := by
    funext x
    exact weightedMode_eq q a x
  rw [he]
  exact h

private theorem weightedMode_bound (q : XiZeroCopy) (a : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖weightedMode q a x‖ ≤ C*tiltedSource a x := by
  obtain ⟨C,hC0,hC⟩ := sourceRatio_bounded q
  refine ⟨C,hC0,?_⟩
  intro x
  rw [weightedMode_eq, norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (tilt_pos a x)]
  nlinarith [hC x,tilt_pos a x]

private theorem weightedMode_top (q : XiZeroCopy) (a : ℝ) :
    Tendsto (weightedMode q a) atTop (𝓝 0) := by
  obtain ⟨C,hC0,hC⟩ := weightedMode_bound q a
  obtain ⟨B,_,hB⟩ := tilt_top_bound a
  apply squeeze_zero_norm (a := fun x => C*B*Real.exp (-x))
  · intro x
    exact (hC x).trans (by nlinarith [hB x])
  · simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (C*B)

private theorem weightedMode_bot (q : XiZeroCopy) (a : ℝ) :
    Tendsto (weightedMode q a) atBot (𝓝 0) := by
  obtain ⟨C,hC0,hC⟩ := weightedMode_bound q a
  obtain ⟨B,_,hB⟩ := tilt_bot_bound a
  apply squeeze_zero_norm (a := fun x => C*B*Real.exp x)
  · intro x
    exact (hC x).trans (by nlinarith [hB x])
  · simpa using Real.tendsto_exp_atBot.const_mul (C*B)

private theorem shift_ne_zero (q : XiZeroCopy) (a : ℝ) :
    xiSpectralPoint q+Complex.I*(a:ℂ) ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  have hn : (xiSpectralPoint q).re ≠ 0 := by
    simpa [xiSpectralPoint,Complex.mul_re,Complex.mul_im] using xi_divisor_support_im_ne_zero q.1
  apply hn
  simpa using hr

/-- All real source moments retain their exact spectral denominator and both endpoint conditions. -/
theorem weightedMode_integral (q : XiZeroCopy) (a : ℝ) :
    (∫ x, weightedMode q a x) = -(∫ x, tiltedSource a x:ℝ)/(xiSpectralPoint q+Complex.I*(a:ℂ)) := by
  let h := xiSpectralPoint q+Complex.I*(a:ℂ)
  have hu := weightedMode_integrable q a
  have hf := tilt_integrable a
  have hdRaw := integral_of_hasDerivAt_of_tendsto (weightedMode_hasDerivAt q a)
    ((hu.const_mul (-Complex.I*h)).sub (hf.ofReal.const_mul Complex.I))
    (weightedMode_bot q a) (weightedMode_top q a)
  have hd : (∫ x, -Complex.I*h*weightedMode q a x-Complex.I*(tiltedSource a x:ℂ)) = 0 := by
    simpa using! hdRaw
  have he : (∫ x, -Complex.I*h*weightedMode q a x-Complex.I*(tiltedSource a x:ℂ)) =
      -Complex.I*h*(∫ x, weightedMode q a x)-Complex.I*(∫ x, tiltedSource a x:ℝ) := by
    have hs : (∫ x, -Complex.I*h*weightedMode q a x-Complex.I*(tiltedSource a x:ℂ)) =
        (∫ x, -Complex.I*h*weightedMode q a x)-(∫ x, Complex.I*(tiltedSource a x:ℂ)) := by
      simpa using! integral_sub (hu.const_mul (-Complex.I*h)) (hf.ofReal.const_mul Complex.I)
    rw [hs,integral_const_mul,integral_const_mul,integral_complex_ofReal]
  rw [he] at hd
  apply (eq_div_iff (shift_ne_zero q a)).2
  change (∫ x, weightedMode q a x)*h = _
  linear_combination (norm := ring_nf) Complex.I*hd
  simp only [I_sq]
  ring

/-- Positive source moment in the native half-density normalization. -/
def tiltedMass (a : ℝ) : ℝ := 2*∫ x, tiltedSource a x

/-- The actual theta moment is strictly positive at every real tilt. -/
theorem tiltedMass_pos (a : ℝ) : 0 < tiltedMass a := by
  apply mul_pos (by norm_num : (0:ℝ)<2)
  apply (integral_pos_iff_support_of_nonneg (fun x => (tilt_pos a x).le) (tilt_integrable a)).2
  have he : Function.support (tiltedSource a) = univ := by
    ext x
    simp [Function.mem_support,(tilt_pos a x).ne']
  rw [he]
  simp

/-- Reflection preserves the full real-tilt theta moment. -/
theorem tiltedMass_neg (a : ℝ) : tiltedMass (-a) = tiltedMass a := by
  have he : tiltedSource (-a) = fun x => tiltedSource a (-x) := by
    funext x
    simp only [tiltedSource,thetaCuspFullSource_neg]
    congr 2
    ring
  unfold tiltedMass
  rw [he]
  congr 1
  simpa using Measure.integral_comp_mul_left (tiltedSource a) (-1:ℝ)

private theorem halfDensity_moment (v : ℝ → ℂ) (r : ℝ) :
    (∫ y in Ioi (0:ℝ), (y^2)⁻¹ •
      ((Real.exp (Real.log y/2):ℂ)*v (Real.log y/2)*(y^r:ℝ))) =
      (2:ℂ)*(∫ x, (Real.exp ((2*r-1)*x):ℂ)*v x) := by
  have hx (x : ℝ) : 2*x/2=x := by ring
  have hrange : (fun x : ℝ => Real.exp (2*x)) '' univ = Ioi (0:ℝ) := by
    ext y
    constructor
    · rintro ⟨x,_,rfl⟩
      exact Real.exp_pos _
    · intro hy
      refine ⟨Real.log y/2,mem_univ _,?_⟩
      change Real.exp (2*(Real.log y/2))=y
      rw [show 2*(Real.log y/2)=Real.log y by ring,Real.exp_log hy]
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => Real.exp (2*x)) (2*Real.exp (2*x)) x := by
    simpa [id_eq,mul_comm] using ((hasDerivAt_id x).const_mul 2).exp
  have hj : InjOn (fun x : ℝ => Real.exp (2*x)) univ := by
    intro x _ y _ h
    have he := Real.exp_injective h
    linarith
  have h := integral_image_eq_integral_abs_deriv_smul (s := univ) MeasurableSet.univ
    (fun x _ => (hd x).hasDerivWithinAt) hj
    (fun y => (y^2)⁻¹ • ((Real.exp (Real.log y/2):ℂ)*v (Real.log y/2)*(y^r:ℝ)))
  rw [hrange,Measure.restrict_univ] at h
  rw [h,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Real.log_exp,hx,
    abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) (Real.exp_pos _)),Complex.real_smul]
  have hp : (Real.exp (2*x))^r = Real.exp (2*x*r) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  rw [hp]
  have he : Real.exp (2*x)*Real.exp ((2*r-1)*x) = Real.exp x*Real.exp (2*x*r) := by
    rw [← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  have hc := congrArg (fun t : ℝ => (t:ℂ)) he
  push_cast at hc ⊢
  field_simp [(Real.exp_pos (2*x)).ne']
  linear_combination (norm := ring_nf) -(v x)*hc

/-- Exact Mellin moment of the complete positive half-density seed at every real exponent. -/
theorem positiveProfile_mellin (r : ℝ) :
    (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • ((positiveProfile y:ℂ)*(y^r:ℝ))) =
      (tiltedMass (2*r-1):ℂ) := by
  simp only [positiveProfile,Complex.ofReal_mul]
  rw [halfDensity_moment (fun x => (thetaCuspFullSource x:ℂ)) r]
  have hc : (∫ x, (Real.exp ((2*r-1)*x):ℂ)*(thetaCuspFullSource x:ℂ)) =
      ((∫ x, tiltedSource (2*r-1) x:ℝ):ℂ) := by
    simp only [tiltedSource,← Complex.ofReal_mul]
    exact integral_ofReal
  rw [hc,tiltedMass,Complex.ofReal_mul,Complex.ofReal_ofNat]

/-- Exact all-real Mellin response of the literal mode seed, including its spectral denominator. -/
theorem modeProfile_mellin (q : XiZeroCopy) (r : ℝ) :
    (∫ y in Ioi (0:ℝ), (y^2)⁻¹ • (modeProfile q y*(y^r:ℝ))) =
      -(tiltedMass (2*r-1):ℂ)/(xiSpectralPoint q+Complex.I*((2*r-1:ℝ):ℂ)) := by
  have he (y : ℝ) : modeProfile q y =
      (Real.exp (Real.log y/2):ℂ)*mode q (Real.log y/2) := by
    unfold modeProfile positiveProfile sourceRatio
    push_cast
    field_simp [(thetaCuspFullSource_pos_all (Real.log y/2)).ne']
  simp_rw [he]
  rw [halfDensity_moment]
  change (2:ℂ)*(∫ x, weightedMode q (2*r-1) x) = _
  rw [weightedMode_integral,tiltedMass]
  push_cast
  ring

end
end RHTower.SelbergThetaNativeMoments
