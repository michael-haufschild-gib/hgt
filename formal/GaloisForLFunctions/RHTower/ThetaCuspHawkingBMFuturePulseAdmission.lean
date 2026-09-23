import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularMeanGrowth
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCircleReconstruction

/-!
Absolute admission of the original future onset pulse. The exact seed and lift
horizon factors, the unchanged physical clock, and the full angular growth bound
give an integrable product majorant in original time/radius coordinates.
The outgoing null cutoff exhausts both the pulse and its original source balance.
The coordinate identity with the finite null Green action is a separate obligation.
-/
namespace RHTower.D4BMFuturePulseAdmission
open Set Filter Topology MeasureTheory
open D4BMHorizon D4BMModularCore D4BMJointSource D4BMLaplaceRadial
open D4BMGlobalAngularResponse D4BMFullAngularCircle D4BMCausalKernel D4BMNativeCircle
open D4BMFullAngularReconstruction D4BMFullAngularGrowth D4BMFullSourceAdvanced
open scoped ContDiff
noncomputable section
set_option autoImplicit false

/-- Auxiliary majorant rate inside the already proved angular/clock gap. -/
def pulseDecayExponent (q : XiZeroCopy) : ℝ := (decayExponent q+2)/2

theorem pulseDecayExponent_bounds (q : XiZeroCopy) :
    decayExponent q < pulseDecayExponent q ∧ pulseDecayExponent q < 2 := by
  have h := (decayExponent_bounds q).2
  dsimp only [pulseDecayExponent]
  constructor <;> linarith

private theorem growth_nonneg (q : XiZeroCopy) : 0 ≤ decayExponent q := by
  have h1 := (sourceGrowthExponent_bounds q).1
  have h2 := (decayExponent_bounds q).1
  linarith

/-- Compact radial profile of the original seed derivative. -/
def seedHorizonProfile (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (u : ℝ) : ℂ :=
  parameter q branch*power (2*physicalRate q branch) (1+u)*amp^(2 : ℕ)*(1+(u:ℂ))*
    ((2*physicalRate q branch+1)*(u:ℂ)+1)

/-- The actual seed derivative carries the same exact horizon exponential as the lift derivative. -/
theorem seedFirst_horizon (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (y : ℝ) :
    sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) y=
      (Real.exp (2*y):ℂ)*seedHorizonProfile q branch amp (radialUnit y) := by
  have hp : sourceSeedPolynomial (physicalRate q branch) (parameter q branch) (radialUnit y)=
      -parameter q branch*(radialUnit y:ℂ) := by
    simp only [sourceSeedPolynomial,parameter_physicalRate,D4BMQuadraticMixedSource.resolventParameter]
    ring
  have hp1 : sourceSeedFirst (physicalRate q branch) (parameter q branch) (radialUnit y)=
      -parameter q branch := by
    simp only [sourceSeedFirst,parameter_physicalRate,D4BMQuadraticMixedSource.resolventParameter]
    ring
  have he : 1-(radialUnit y:ℂ)=(Real.exp (2*y):ℂ)*(1+(radialUnit y:ℂ)) :=
    by exact_mod_cast radialUnit_one_sub y
  rw [sourceSeedFieldFirst,hp,hp1]
  simp only [sourceAmplitude,zero_mul,Complex.exp_zero,one_mul,mul_one,amplitudeRate,zero_add]
  calc
    _ = parameter q branch*power (2*physicalRate q branch) (1+radialUnit y)*amp^(2 : ℕ)*
        (1-(radialUnit y:ℂ))*((2*physicalRate q branch+1)*(radialUnit y:ℂ)+1) := by ring
    _ = _ := by rw [he]; dsimp only [seedHorizonProfile]; ring

private theorem seedHorizonProfile_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContinuousOn (seedHorizonProfile q branch amp) (Icc 0 1) := by
  intro u hu
  have hp : ContinuousAt (fun u : ℝ => power (2*physicalRate q branch) (1+u)) u :=
    (power_derivatives (2*physicalRate q branch) (by linarith [hu.1])).1.continuousAt.comp
      (continuous_const.add continuous_id).continuousAt
  have hc : ContinuousAt (fun v : ℝ => parameter q branch*power (2*physicalRate q branch) (1+v)*
      amp^(2 : ℕ)*(1+(v:ℂ))*((2*physicalRate q branch+1)*(v:ℂ)+1)) u := by fun_prop
  exact hc.continuousWithinAt

private theorem radial_pair_bound (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y < 0 →
      ‖sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) y‖+
        ‖2*radialLiftFirst (physicalRate q branch) 0 amp 1 y‖ ≤ C*Real.exp (2*y) := by
  obtain ⟨C0,h0⟩ := isCompact_Icc.exists_bound_of_continuousOn (seedHorizonProfile_continuous q branch amp)
  obtain ⟨C1,h1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (sourceHorizonProfile_continuousOn (physicalRate q branch) amp 1)
  refine ⟨max C0 0+max C1 0,add_nonneg (le_max_right _ _) (le_max_right _ _),fun y hy => ?_⟩
  have hu : radialUnit y ∈ Icc (0:ℝ) 1 := ⟨(radialUnit_bounds y hy).1.le,(radialUnit_bounds y hy).2.le⟩
  have hb0 := (h0 _ hu).trans (le_max_left C0 0)
  have hb1 := (h1 _ hu).trans (le_max_left C1 0)
  rw [seedFirst_horizon,radialLiftFirst_horizon,norm_mul,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  nlinarith [mul_le_mul_of_nonneg_left hb0 (Real.exp_pos (2*y)).le,
    mul_le_mul_of_nonneg_left hb1 (Real.exp_pos (2*y)).le]

private def clockSlope (q : XiZeroCopy) (branch : Bool) (v : ℝ) : ℂ :=
  timeOnsetFirst (2*physicalRate q branch) v-2*physicalRate q branch*timeOnset (2*physicalRate q branch) v

private theorem clockSlope_eq (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    clockSlope q branch v=((deriv Real.smoothTransition v:ℝ):ℂ)*
      Complex.exp (2*physicalRate q branch*(v:ℂ)) := by
  dsimp only [clockSlope,timeOnsetFirst,timeOnset]
  ring

private theorem clockSlope_continuous (q : XiZeroCopy) (branch : Bool) : Continuous (clockSlope q branch) := by
  have h0 : Continuous (timeOnset (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun v => (timeOnset_hasDerivAt _ v).continuousAt)
  have h1 : Continuous (timeOnsetFirst (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun v => (timeOnsetFirst_hasDerivAt _ v).continuousAt)
  exact h1.sub (h0.const_mul _)

private theorem clockSlope_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℝ,
      ‖clockSlope q branch v‖ ≤ C*Real.exp (-pulseDecayExponent q*v) := by
  have hs := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hs
  obtain ⟨B,hB,hb⟩ := timeOnset_pair_bound (2*physicalRate q branch) (pulseDecayExponent q)
    (by linarith [(pulseDecayExponent_bounds q).2])
  refine ⟨(1+‖2*physicalRate q branch‖)*B,by positivity,fun v => ?_⟩
  have h := norm_sub_le (timeOnsetFirst (2*physicalRate q branch) v)
    (2*physicalRate q branch*timeOnset (2*physicalRate q branch) v)
  rw [norm_mul] at h
  have hp := mul_le_mul_of_nonneg_left (hb v) (show 0 ≤ 1+‖2*physicalRate q branch‖ by positivity)
  change ‖timeOnsetFirst (2*physicalRate q branch) v-2*physicalRate q branch*timeOnset (2*physicalRate q branch) v‖ ≤ _
  nlinarith [norm_nonneg (timeOnset (2*physicalRate q branch) v),
    mul_nonneg (norm_nonneg (2*physicalRate q branch)) (norm_nonneg (timeOnsetFirst (2*physicalRate q branch) v))]

private theorem coefficient_formulas (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau y : ℝ) :
    onsetResponseCoefficient q branch amp tau y=
      -2*sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) y*clockSlope q branch (tau+y) ∧
    onsetSourceCoefficient q branch amp tau y=
      parameter q branch*(2*radialLiftFirst (physicalRate q branch) 0 amp 1 y)*clockSlope q branch (tau+y) := by
  rw [clockSlope_eq]
  constructor <;> dsimp only [onsetResponseCoefficient,onsetSourceCoefficient] <;> ring

private theorem coefficients_bound (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ tau y : ℝ, y < 0 →
      ‖onsetResponseCoefficient q branch amp tau y‖+‖onsetSourceCoefficient q branch amp tau y‖ ≤
        C*Real.exp (2*y)*Real.exp (-pulseDecayExponent q*(tau+y)) := by
  obtain ⟨C,hC,hc⟩ := radial_pair_bound q branch amp
  obtain ⟨B,hB,hb⟩ := clockSlope_bound q branch
  refine ⟨(2+‖parameter q branch‖)*C*B,by positivity,fun tau y hy => ?_⟩
  obtain ⟨h0,h1⟩ := coefficient_formulas q branch amp tau y
  rw [h0,h1,norm_mul,norm_mul,norm_mul,norm_mul,norm_neg,Complex.norm_ofNat]
  have hp := hc y hy
  have ht := hb (tau+y)
  have hsum : 2*‖sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) y‖+
      ‖parameter q branch‖*‖2*radialLiftFirst (physicalRate q branch) 0 amp 1 y‖ ≤
        (2+‖parameter q branch‖)*(C*Real.exp (2*y)) := by
    have hh := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2+‖parameter q branch‖ by positivity)
    nlinarith [norm_nonneg (2*radialLiftFirst (physicalRate q branch) 0 amp 1 y),
      mul_nonneg (norm_nonneg (parameter q branch))
        (norm_nonneg (sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) y))]
  have hm := mul_le_mul hsum ht (norm_nonneg _)
    (show 0 ≤ (2+‖parameter q branch‖)*(C*Real.exp (2*y)) by positivity)
  nlinarith only [hm]

private def circleKernel (F : ℝ → ℂ) (h x y : ℝ) : ℂ :=
  ((if |x-y| ≤ h then F (Real.arcosh (invariant h x y)) else 0)-
    (if |x+y| ≤ h then F (Real.arcosh (invariant h x (-y))) else 0))/2

private theorem circleKernel_measurable (F : ℝ → ℂ) (hF : Continuous F) (x : ℝ) :
    Measurable (fun p : ℝ × ℝ => circleKernel F p.1 x p.2) := by
  classical
  have one_cone (b : Bool) : Measurable (fun p : ℝ × ℝ =>
      if |x-(if b then -p.2 else p.2)| ≤ p.1 then
        F (Real.arcosh (invariant p.1 x (if b then -p.2 else p.2))) else 0) := by
    let y : ℝ × ℝ → ℝ := fun p => if b then -p.2 else p.2
    have hy : Continuous y := by
      cases b <;> simp only [y,Bool.false_eq_true,↓reduceIte] <;> fun_prop
    have hi : Continuous (fun p : ℝ × ℝ => invariant p.1 x (y p)) := by
      unfold invariant
      exact (Real.continuous_cosh.comp continuous_fst |>.add
        ((Real.continuous_sinh.comp hy).const_mul (Real.sinh x))).div
        ((Real.continuous_cosh.comp hy).const_mul (Real.cosh x))
        (fun p => mul_ne_zero (Real.cosh_pos x).ne' (Real.cosh_pos (y p)).ne')
    have hr : Continuous (fun p : ℝ × ℝ => Real.arcosh (max 1 (invariant p.1 x (y p)))) :=
      Real.continuousOn_arcosh.comp_continuous (continuous_const.max hi)
        (fun p => show 1 ≤ max 1 (invariant p.1 x (y p)) from le_max_left _ _)
    have hs : MeasurableSet {p : ℝ × ℝ | |x-y p| ≤ p.1} :=
      (isClosed_le (continuous_const.sub hy |>.abs) continuous_fst).measurableSet
    have he : Measurable (fun p : ℝ × ℝ =>
        if |x-y p| ≤ p.1 then F (Real.arcosh (max 1 (invariant p.1 x (y p)))) else 0) :=
      Measurable.ite hs (hF.comp hr).measurable measurable_const
    convert! he using 1
    funext p
    change (if |x-y p| ≤ p.1 then F (Real.arcosh (invariant p.1 x (y p))) else 0) =
      (if |x-y p| ≤ p.1 then F (Real.arcosh (max 1 (invariant p.1 x (y p)))) else 0)
    by_cases hc : |x-y p| ≤ p.1
    · simp only [if_pos hc,max_eq_right (invariant_causal ⟨p.1,x,y p,hc⟩)]
    · rw [if_neg hc,if_neg hc]
  have h1 := one_cone false
  have h2 := one_cone true
  simpa only [Bool.false_eq_true,if_false,if_true,sub_neg_eq_add,circleKernel,Pi.sub_apply]
    using (h1.sub h2).div_const (2:ℂ)

private theorem circleKernel_bound (F : ℝ → ℂ) (C gamma : ℝ) (hC : 0 ≤ C)
    (hg : 0 ≤ gamma) (hF : ∀ d : ℝ, 0 ≤ d → ‖F d‖ ≤ C*Real.exp (gamma*d))
    (h x y : ℝ) : ‖circleKernel F h x y‖ ≤ C*Real.exp (gamma*h) := by
  have cone_bound (y : ℝ) :
      ‖if |x-y| ≤ h then F (Real.arcosh (invariant h x y)) else 0‖ ≤ C*Real.exp (gamma*h) := by
    split_ifs with hc
    · have hz := invariant_causal ⟨h,x,y,hc⟩
      have hd := Real.arcosh_nonneg hz
      have hh := (abs_nonneg (x-y)).trans hc
      have hb := invariant_le_cosh_time h x y
      rw [← Real.cosh_arcosh hz] at hb
      have hr : Real.arcosh (invariant h x y) ≤ h := by
        simpa only [abs_of_nonneg hd,abs_of_nonneg hh] using Real.cosh_le_cosh.mp hb
      exact (hF _ hd).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr hg)) hC)
    · simp only [norm_zero]
      positivity
  have h1 := cone_bound y
  have h2 := cone_bound (-y)
  simp only [sub_neg_eq_add] at h2
  dsimp only [circleKernel]
  rw [norm_div,Complex.norm_ofNat]
  exact (div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)).trans (by linarith)

private theorem angular_pair_bound (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h x y : ℝ, 0 ≤ h →
      ‖angularDirichletKernel q branch h x y X k‖+‖nativeDirichletCausalKernel q h x y X k‖ ≤
        C*Real.exp (decayExponent q*h) := by
  obtain ⟨B,hB,hb⟩ := angularMean_growth q branch X k
  obtain ⟨C,hC,hc⟩ := kernel_growth q
  refine ⟨B+C*Real.exp (sourceGrowthExponent q*|k|),by positivity,fun h x y hh => ?_⟩
  have hm : ‖angularDirichletKernel q branch h x y X k‖ ≤ B*Real.exp (decayExponent q*h) :=
    circleKernel_bound (fun d => angularMean q branch d X k) B (decayExponent q) hB
      (growth_nonneg q) (fun d hd => (le_add_of_nonneg_right (norm_nonneg _)).trans (hb d hd)) h x y
  have hn := hc h x y X k hh
  have he : Real.exp (sourceGrowthExponent q*(h+|k|)) ≤
      Real.exp (sourceGrowthExponent q*|k|)*Real.exp (decayExponent q*h) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [(decayExponent_bounds q).1]
  have hn1 := hn.trans (mul_le_mul_of_nonneg_left he hC)
  nlinarith only [hm,hn1]

/-- Both actual pulse channels retain the original direct and image gates. -/
theorem kernel_two_channels (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau y h x X k : ℝ) :
    onsetDirichletKernel q branch amp tau y h x y X k=
      onsetResponseCoefficient q branch amp tau y*angularDirichletKernel q branch h x y X k+
      onsetSourceCoefficient q branch amp tau y*nativeDirichletCausalKernel q h x y X k := by
  dsimp only [onsetDirichletKernel,angularDirichletKernel,nativeDirichletCausalKernel,
    nativeRiemannKernel,angularKernel]
  by_cases hd : |x-y| ≤ h <;> by_cases hi : |x+y| ≤ h <;>
    simp only [hd,hi,↓reduceIte,onsetAngularMean_eq] <;> ring

/-- Original unprojected pulse evaluated at future source time and radius. -/
def density (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) (p : ℝ × ℝ) : ℂ :=
  onsetDirichletKernel q branch amp (tau+p.1) p.2 p.1 x p.2 X k

private theorem density_measurable (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) :
    Measurable (density q branch amp tau x X k) := by
  have hseed : Continuous (sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch)) :=
    continuous_iff_continuousAt.mpr (fun y => (sourceSeedFieldFirst_hasDerivAt _ _ _ _ _ y).continuousAt)
  have hlift : Continuous (radialLiftFirst (physicalRate q branch) 0 amp 1) :=
    continuous_iff_continuousAt.mpr (fun y => (radialLiftFirst_hasDerivAt _ _ _ _ y).continuousAt)
  have hclock : Continuous (fun p : ℝ × ℝ => clockSlope q branch (tau+p.1+p.2)) :=
    (clockSlope_continuous q branch).comp (by fun_prop)
  have h0 : Continuous (fun p : ℝ × ℝ => -2*
      sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) p.2*
        clockSlope q branch (tau+p.1+p.2)) :=
    ((hseed.comp continuous_snd).const_mul (-2)).mul hclock
  have h1 : Continuous (fun p : ℝ × ℝ => parameter q branch*
      (2*radialLiftFirst (physicalRate q branch) 0 amp 1 p.2)*clockSlope q branch (tau+p.1+p.2)) :=
    (((hlift.comp continuous_snd).const_mul 2).const_mul (parameter q branch)).mul hclock
  have hM := circleKernel_measurable (fun d => angularMean q branch d X k)
    (angularMean_smooth q branch X k).continuous x
  have hN := circleKernel_measurable (fun d => mean q d X k) (mean_radial_smooth q X k).continuous x
  have he : density q branch amp tau x X k = fun p : ℝ × ℝ =>
      (-2*sourceSeedFieldFirst (physicalRate q branch) 0 amp 1 (parameter q branch) p.2*
        clockSlope q branch (tau+p.1+p.2))*circleKernel (fun d => angularMean q branch d X k) p.1 x p.2+
      (parameter q branch*(2*radialLiftFirst (physicalRate q branch) 0 amp 1 p.2)*
        clockSlope q branch (tau+p.1+p.2))*circleKernel (fun d => mean q d X k) p.1 x p.2 := by
    funext p
    rw [density,kernel_two_channels,(coefficient_formulas q branch amp (tau+p.1) p.2).1,
      (coefficient_formulas q branch amp (tau+p.1) p.2).2]
    rfl
  rw [he]
  exact (h0.measurable.mul hM).add (h1.measurable.mul hN)

/-- Original horizon decay and the strict clock/angular gap give an integrable product. -/
theorem density_bound (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ tau x h y : ℝ, 0 < h → y < 0 →
      ‖density q branch amp tau x X k (h,y)‖ ≤ C*Real.exp (-pulseDecayExponent q*tau)*
        (Real.exp ((decayExponent q-pulseDecayExponent q)*h)*Real.exp ((2-pulseDecayExponent q)*y)) := by
  obtain ⟨B,hB,hb⟩ := coefficients_bound q branch amp
  obtain ⟨C,hC,hc⟩ := angular_pair_bound q branch X k
  refine ⟨B*C,mul_nonneg hB hC,fun tau x h y hh hy => ?_⟩
  have hs := hb (tau+h) y hy
  have hk := hc h x y hh.le
  have hm := mul_le_mul hs hk (by positivity)
    (show 0 ≤ B*Real.exp (2*y)*Real.exp (-pulseDecayExponent q*(tau+h+y)) by positivity)
  rw [density,kernel_two_channels]
  have hn := norm_add_le
    (onsetResponseCoefficient q branch amp (tau+h) y*angularDirichletKernel q branch h x y X k)
    (onsetSourceCoefficient q branch amp (tau+h) y*nativeDirichletCausalKernel q h x y X k)
  simp only [norm_mul] at hn
  have hp : ‖onsetResponseCoefficient q branch amp (tau+h) y*angularDirichletKernel q branch h x y X k+
      onsetSourceCoefficient q branch amp (tau+h) y*nativeDirichletCausalKernel q h x y X k‖ ≤
      (B*Real.exp (2*y)*Real.exp (-pulseDecayExponent q*(tau+h+y)))*
        (C*Real.exp (decayExponent q*h)) := by
    nlinarith [mul_nonneg (norm_nonneg (onsetResponseCoefficient q branch amp (tau+h) y))
      (norm_nonneg (nativeDirichletCausalKernel q h x y X k)),
      mul_nonneg (norm_nonneg (onsetSourceCoefficient q branch amp (tau+h) y))
        (norm_nonneg (angularDirichletKernel q branch h x y X k))]
  refine hp.trans_eq ?_
  calc
    _ = (B*C)*(Real.exp (2*y)*Real.exp (-pulseDecayExponent q*(tau+h+y))*
        Real.exp (decayExponent q*h)) := by ring
    _ = _ := by
      simp only [mul_assoc,← Real.exp_add]
      congr 2
      ring

private theorem majorant_integrable (q : XiZeroCopy) (D : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => D*
      (Real.exp ((decayExponent q-pulseDecayExponent q)*p.1)*
        Real.exp ((2-pulseDecayExponent q)*p.2))) (Ioi 0 ×ˢ Iio 0) := by
  have hc := pulseDecayExponent_bounds q
  have hh := integrableOn_exp_mul_Ioi (show decayExponent q-pulseDecayExponent q < 0 by linarith) 0
  have hy := (integrableOn_exp_mul_Iic (show 0 < 2-pulseDecayExponent q by linarith) 0).mono_set Iio_subset_Iic_self
  rw [IntegrableOn,Measure.volume_eq_prod,← Measure.prod_restrict]
  exact (hh.mul_prod hy).const_mul D

/-- Absolute admission of the actual two-channel onset pulse, with no matching premise. -/
theorem density_integrable (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) :
    IntegrableOn (density q branch amp tau x X k) (Ioi 0 ×ˢ Iio 0) := by
  obtain ⟨C,hC,hb⟩ := density_bound q branch amp X k
  have hm := majorant_integrable q (C*Real.exp (-pulseDecayExponent q*tau))
  apply hm.mono' (density_measurable q branch amp tau x X k).aestronglyMeasurable.restrict
  exact (ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Iio)).mpr
    (Eventually.of_forall (fun p hp => hb tau x p.1 p.2 hp.1 hp.2))

/-- Absolutely convergent future action of the unchanged full onset pulse. -/
def response (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) : ℂ :=
  ∫ p in Ioi 0 ×ˢ Iio 0, density q branch amp tau x X k p

theorem response_fubini (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) :
    response q branch amp tau x X k =
      ∫ h in Ioi 0, ∫ y in Iio 0, onsetDirichletKernel q branch amp (tau+h) y h x y X k := by
  have hi := density_integrable q branch amp tau x X k
  rw [response,Measure.volume_eq_prod]
  exact setIntegral_prod _ (by simpa only [Measure.volume_eq_prod] using hi)

/-- Original future region cut at outgoing source coordinate `tau+h-y=L`. -/
def futureRegion (tau L : ℝ) : Set (ℝ × ℝ) :=
  (Ioi 0 ×ˢ Iio 0) ∩ {p | tau+p.1-p.2 ≤ L}

private theorem futureRegion_measurable (tau L : ℝ) : MeasurableSet (futureRegion tau L) := by
  exact (measurableSet_Ioi.prod measurableSet_Iio).inter
    (isClosed_le (show Continuous (fun p : ℝ × ℝ => tau+p.1-p.2) by fun_prop)
      continuous_const).measurableSet

private theorem futureRegion_integral_limit (f : ℝ × ℝ → ℂ) (tau : ℝ)
    (hf : IntegrableOn f (Ioi 0 ×ˢ Iio 0)) :
    Tendsto (fun L => ∫ p in futureRegion tau L, f p) atTop
      (𝓝 (∫ p in Ioi 0 ×ˢ Iio 0, f p)) := by
  have hu : (⋃ L : ℝ, futureRegion tau L)=Ioi 0 ×ˢ Iio 0 := by
    ext p
    constructor
    · intro hp
      obtain ⟨L,hL⟩ := mem_iUnion.mp hp
      exact hL.1
    · intro hp
      refine mem_iUnion.mpr ⟨tau+p.1-p.2,hp,?_⟩
      change tau+p.1-p.2 ≤ tau+p.1-p.2
      rfl
  have hm : Monotone (futureRegion tau) := by
    intro L M hLM p hp
    exact ⟨hp.1,hp.2.trans hLM⟩
  have h := tendsto_setIntegral_of_monotone (futureRegion_measurable tau) hm
    (show IntegrableOn f (⋃ L : ℝ, futureRegion tau L) by rw [hu]; exact hf)
  simpa only [hu] using h

/-- Finite outgoing cut of the independently defined original pulse action. -/
def truncatedResponse (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k L : ℝ) : ℂ :=
  ∫ p in futureRegion tau L, density q branch amp tau x X k p

/-- The null-coordinate cutoff exhausts the admitted original pulse integral. -/
theorem truncatedResponse_limit (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) :
    Tendsto (truncatedResponse q branch amp tau x X k) atTop
      (𝓝 (response q branch amp tau x X k)) :=
  futureRegion_integral_limit _ tau (density_integrable q branch amp tau x X k)

/-- The same outgoing cut admits the original pulse-minus-source balance.
Identifying this cut with the finite null Green action is a separate coordinate identity. -/
theorem sourceBalance_limit (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (tau x X k : ℝ) :
    Tendsto (fun L => ∫ p in futureRegion tau L,
      density q branch amp tau x X k p-
        parameter q branch*D4BMFullSourceAdvanced.density q branch amp tau x X k p) atTop
      (𝓝 (response q branch amp tau x X k-
        parameter q branch*D4BMFullSourceAdvanced.response q branch amp tau x X k)) := by
  have hP := density_integrable q branch amp tau x X k
  have hQ := D4BMFullSourceAdvanced.density_integrable q branch amp tau x X k
  have hi := hP.sub (hQ.const_mul (parameter q branch))
  have h := futureRegion_integral_limit _ tau hi
  dsimp only [Pi.sub_apply] at h
  simpa only [integral_sub hP (hQ.const_mul (parameter q branch)),integral_const_mul,
    response,D4BMFullSourceAdvanced.response] using h

end
end RHTower.D4BMFuturePulseAdmission
