import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureSeedHorizonCap
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCapRadialMemory

/-! The literal full seed cap has a distinct normal trace from the source cap.
Its base coefficient is the full Goursat coefficient, so the full response and
the retained half-square channel must remain together throughout the cap limit. -/

set_option autoImplicit false
open Set MeasureTheory Filter Topology

namespace RHTower.D4BMFullSeedCapRadialMemory
open D4BMFutureSeedHorizon D4BMCapNormalTrace D4BMCapRadialMemory
open D4BMFullAngularCircle D4BMFullAngularGrowth D4BMGlobalAngularResponse
open D4BMHorizon D4BMModularCore
noncomputable section

private theorem scale_pos (x : ℝ) : 0 < capScale x :=
  div_pos (Real.exp_pos x) (Real.cosh_pos x)

private theorem scale_limit : Tendsto capScale atBot (𝓝 (0 : ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 2*x) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id
  have he := Real.tendsto_exp_atBot.comp ht
  have hc (x : ℝ) : capScale x = 1-radialUnit x := by
    rw [capScale, radialUnit, ← Real.cosh_add_sinh x]
    field_simp [(Real.cosh_pos x).ne']
    ring
  have hform : capScale = fun x => 2*Real.exp (2*x)/(1+Real.exp (2*x)) := by
    funext x
    rw [eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (2*x))), hc]
    have hh := radialUnit_one_sub x
    nlinarith
  rw [hform]
  simpa only [Function.comp_def, Pi.div_apply, mul_zero, add_zero, zero_div]
    using! (he.const_mul 2).div (tendsto_const_nhds.add he)
      (by norm_num : (1 : ℝ)+0 ≠ 0)

/-- The literal full seed circle at a cap delay. The `max` is retained in the
definition; it is removed only under the physical nonnegative-delay hypothesis. -/
private def fullHorizonMean (q : XiZeroCopy) (branch : Bool) (x h X k : ℝ) : ℂ :=
  angularMean q branch (Real.arcosh (max 1 (1+capScale x*(Real.exp h-1)))) X k

private theorem fullHorizonMean_eq_kernel (q : XiZeroCopy) (branch : Bool)
    (x h X k : ℝ) (hh : 0 ≤ h) :
    fullHorizonMean q branch x h X k =
      angularMean q branch (Real.arcosh (1+capScale x*(Real.exp h-1))) X k := by
  have hz : 1 ≤ 1+capScale x*(Real.exp h-1) := by
    have he := Real.one_le_exp_iff.mpr hh
    have hp := scale_pos x
    nlinarith
  rw [fullHorizonMean, max_eq_right hz]

private theorem fullHorizonMean_continuous (q : XiZeroCopy) (branch : Bool)
    (x X k : ℝ) : Continuous (fun h => fullHorizonMean q branch x h X k) := by
  apply (angularMean_smooth q branch X k).continuous.comp
  exact Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
    (fun z => le_max_left 1 z)

private def normalizedFullMean (q : XiZeroCopy) (branch : Bool) (x X k h : ℝ) : ℂ :=
  (fullHorizonMean q branch x h X k-fullAngularField q branch ![X, Real.exp k]) /
    (capScale x : ℂ)

/-- The actual Goursat coefficient, not the source-only cap coefficient, is
the normalized full seed limit. -/
private theorem normalizedFullMean_limit (q : XiZeroCopy) (branch : Bool)
    (X k h : ℝ) (hh : 0 < h) :
    Tendsto (fun x => normalizedFullMean q branch x X k h) atBot
      (𝓝 ((parameter q branch*
        (fullAngularField q branch ![X, Real.exp k]+fullSquarePotential q ![X, Real.exp k])/2)*
        ((Real.exp h-1 : ℝ) : ℂ))) := by
  let K := fun z => angularMean q branch (Real.arcosh z) X k
  have hd := (D4BMFullAngularGoursat.fullAngularKernel_right_derivative q branch X k).mono
    Ioi_subset_Ici_self
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (by simp : (1 : ℝ) ∉ Ioi (1 : ℝ))).mp hd
  have hz : Tendsto (fun x => 1+capScale x*(Real.exp h-1)) atBot (𝓝[Ioi 1] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [zero_mul, add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add
        (scale_limit.mul_const (Real.exp h-1))
    · filter_upwards with x
      have he := Real.one_lt_exp_iff.mpr hh
      have hp := scale_pos x
      change 1 < 1+capScale x*(Real.exp h-1)
      nlinarith
  have ht := (hs.comp hz).mul_const (((Real.exp h-1 : ℝ) : ℂ))
  convert! ht using 1
  funext x
  rw [normalizedFullMean, fullHorizonMean_eq_kernel q branch x h X k hh.le]
  simp only [Function.comp_apply, slope_def_module, add_sub_cancel_left, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one]
  have hc : (capScale x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (scale_pos x).ne'
  have he : (Real.exp h : ℂ)-1 ≠ 0 := by
    exact_mod_cast (ne_of_gt (sub_pos.mpr (Real.one_lt_exp_iff.mpr hh)))
  have hK : angularMean q branch (Real.arcosh 1) X k =
      fullAngularField q branch ![X, Real.exp k] := by
    simpa only [Real.arcosh_zero] using angularMean_zero q branch X k
  rw [hK]
  field_simp [hc, he]

private theorem normalWeight_continuous (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    Continuous (normalWeight q branch v) := by
  have h0 := timeOnsetSecond_continuous (2*physicalRate q branch)
  have h1 : Continuous (timeOnsetFirst (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr
      (fun u => (timeOnsetFirst_hasDerivAt _ u).continuousAt)
  exact ((h0.comp (continuous_const.add continuous_id)).mul
    (continuous_const.sub (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)))).add
    ((h1.comp (continuous_const.add continuous_id)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)))

private theorem normalWeight_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v h : ℝ, 0 ≤ h →
      ‖normalWeight q branch v h‖ ≤ B*Real.exp (-decayExponent q*(v+h)) := by
  obtain ⟨B, hB, hb⟩ := onset_derivative_bound q branch
  refine ⟨B, hB, fun v h hh => ?_⟩
  have he : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have he1 : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold normalWeight
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
  rw [show (1 : ℂ)-(Real.exp (-h) : ℂ) = ((1-Real.exp (-h) : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr he1)]
  have h0 := norm_nonneg (timeOnsetFirst (2*physicalRate q branch) (v+h))
  have h1 := norm_nonneg (timeOnsetSecond (2*physicalRate q branch) (v+h))
  nlinarith [hb (v+h)]

private theorem decay_gt_one (q : XiZeroCopy) : 1 < decayExponent q :=
  lt_of_le_of_lt (sourceGrowthExponent_bounds q).1 (decayExponent_bounds q).1

private def fullKernelMajorant (q : XiZeroCopy) (h : ℝ) : ℝ :=
  Real.exp ((1-decayExponent q)*h)+
    Real.exp ((strictGrowthExponent q-decayExponent q)*h)

private theorem fullKernelMajorant_integrable (q : XiZeroCopy) :
    IntegrableOn (fullKernelMajorant q) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (sub_neg.mpr (decay_gt_one q)) 0).add
    (integrableOn_exp_mul_Ioi (sub_neg.mpr (strictGrowthExponent_bounds q).2) 0)

private def fullNormalDensity (q : XiZeroCopy) (branch : Bool)
    (v x X k h : ℝ) : ℂ :=
  normalWeight q branch v h*normalizedFullMean q branch x X k h

private theorem fullNormalDensity_continuous (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) : Continuous (fullNormalDensity q branch v x X k) :=
  (normalWeight_continuous q branch v).mul
    ((fullHorizonMean_continuous q branch x X k).sub continuous_const).div_const _

private theorem fullNormalDensity_bound (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h : ℝ, capScale x ≤ 1 → 0 ≤ h →
      ‖fullNormalDensity q branch v x X k h‖ ≤ C*fullKernelMajorant q h := by
  obtain ⟨B, hB, hb⟩ := normalWeight_bound q branch
  obtain ⟨C, hC, hc⟩ := fullAngularKernel_scaled_bound q branch X k
  refine ⟨B*C*Real.exp (-decayExponent q*v), by positivity, fun x h hx hh => ?_⟩
  rw [fullNormalDensity, norm_mul]
  have hp := hc (capScale x) h (scale_pos x) hx hh
  rw [normalizedFullMean, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (scale_pos x)]
  rw [fullHorizonMean_eq_kernel q branch x h X k hh]
  have hmean :
      ‖fullHorizonMean q branch x h X k-fullAngularField q branch ![X, Real.exp k]‖ /
          capScale x ≤ C*(Real.exp h+Real.exp (strictGrowthExponent q*h)) := by
    rw [div_le_iff₀ (scale_pos x)]
    nlinarith [hp]
  calc
    _ ≤ (B*Real.exp (-decayExponent q*(v+h)))*
        (C*(Real.exp h+Real.exp (strictGrowthExponent q*h))) :=
      mul_le_mul (hb v h hh) hmean (norm_nonneg _) (by positivity)
    _ = _ := by
      have he1 : Real.exp (-decayExponent q*(v+h))*Real.exp h =
          Real.exp (-decayExponent q*v)*Real.exp ((1-decayExponent q)*h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      have he2 : Real.exp (-decayExponent q*(v+h))*Real.exp (strictGrowthExponent q*h) =
          Real.exp (-decayExponent q*v)*
            Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (B*C)*(Real.exp (-decayExponent q*(v+h))*Real.exp h+
          Real.exp (-decayExponent q*(v+h))*Real.exp (strictGrowthExponent q*h)) := by ring
        _ = _ := by rw [he1, he2]; dsimp [fullKernelMajorant]; ring

private theorem fullNormalDensity_integrable (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) (hx : capScale x ≤ 1) :
    IntegrableOn (fullNormalDensity q branch v x X k) (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := fullNormalDensity_bound q branch v X k
  apply ((fullKernelMajorant_integrable q).const_mul C).mono'
    (fullNormalDensity_continuous q branch v x X k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact hb x h hx hh.le

private theorem normalWeight_integrable (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    IntegrableOn (normalWeight q branch v) (Ioi 0) := by
  obtain ⟨B, hB, hb⟩ := normalWeight_bound q branch
  have hd : 0 < decayExponent q := by linarith [decay_gt_one q]
  apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hd) 0).const_mul
    (B*Real.exp (-decayExponent q*v))).mono'
    (normalWeight_continuous q branch v).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have he : (B*Real.exp (-decayExponent q*v))*Real.exp (-decayExponent q*h) =
      B*Real.exp (-decayExponent q*(v+h)) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact hb v h hh.le

/-- The normal arm of the literal full seed. This is a different object from
the source cap normal arm because its numerator is the full angular response. -/
private def fullNormalArm (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ), normalWeight q branch v h*fullHorizonMean q branch x h X k

private theorem fullNormalDensity_integral (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) (hx : capScale x ≤ 1) :
    (∫ h in Ioi (0 : ℝ), fullNormalDensity q branch v x X k h) =
      fullNormalArm q branch v x X k/(capScale x : ℂ) := by
  have hc : (capScale x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (scale_pos x).ne'
  have hd := fullNormalDensity_integrable q branch v x X k hx
  have hn := normalWeight_integrable q branch v
  have he : fullNormalArm q branch v x X k =
      (capScale x : ℂ)*(∫ h in Ioi (0 : ℝ), fullNormalDensity q branch v x X k h) := by
    change (∫ h in Ioi (0 : ℝ), normalWeight q branch v h*
      fullHorizonMean q branch x h X k) = _
    calc
      _ = ∫ h in Ioi (0 : ℝ), ((capScale x : ℂ)*fullNormalDensity q branch v x X k h+
          normalWeight q branch v h*fullAngularField q branch ![X, Real.exp k]) := by
        apply integral_congr_ae
        filter_upwards with h
        dsimp [fullNormalDensity, normalizedFullMean]
        field_simp [hc]
        ring
      _ = _ := by
        rw [integral_add (hd.const_mul (capScale x : ℂ))
          (hn.mul_const (fullAngularField q branch ![X, Real.exp k])), integral_const_mul,
          integral_mul_const, normalWeight_future_integral, zero_mul, add_zero]
  apply (eq_div_iff hc).mpr
  rw [he]
  ring

/-- Dominated convergence for the literal full seed normal arm. Its coefficient
retains the full response and half-square channels and is the direct DCT input
for the two-arm seed-cap radial trace. -/
theorem fullNormalArm_div_scale_ingoing (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    Tendsto (fun x => fullNormalArm q branch v x X k/(capScale x : ℂ)) atBot
      (𝓝 ((parameter q branch*
        (fullAngularField q branch ![X, Real.exp k]+fullSquarePotential q ![X, Real.exp k])/2)*
        sourceMemory q branch v)) := by
  obtain ⟨C, hC, hb⟩ := fullNormalDensity_bound q branch v X k
  have hsmall : ∀ᶠ x in atBot, capScale x ≤ 1 :=
    (scale_limit.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun x hx => hx.le)
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0 : ℝ))) (fun h => C*fullKernelMajorant q h)
    (Filter.Eventually.of_forall
      (fun x => (fullNormalDensity_continuous q branch v x X k).aestronglyMeasurable))
    (by
      filter_upwards [hsmall] with x hx
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      exact hb x h hx hh.le)
    ((fullKernelMajorant_integrable q).const_mul C)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      exact (normalizedFullMean_limit q branch X k h hh).const_mul
        (normalWeight q branch v h))
  have he : (∫ h in Ioi (0 : ℝ), normalWeight q branch v h*
      ((parameter q branch*(fullAngularField q branch ![X, Real.exp k]+
        fullSquarePotential q ![X, Real.exp k])/2)*((Real.exp h-1 : ℝ) : ℂ))) =
      (parameter q branch*(fullAngularField q branch ![X, Real.exp k]+
        fullSquarePotential q ![X, Real.exp k])/2)*sourceMemory q branch v := by
    calc
      _ = ∫ h in Ioi (0 : ℝ),
          (parameter q branch*(fullAngularField q branch ![X, Real.exp k]+
            fullSquarePotential q ![X, Real.exp k])/2)*
            (normalWeight q branch v h*((Real.exp h : ℂ)-1)) := by
        apply integral_congr_ae
        filter_upwards with h
        push_cast
        ring
      _ = _ := by rw [integral_const_mul, normalWeight_first_moment]
  rw [he] at ht
  apply ht.congr'
  filter_upwards [hsmall] with x hx
  exact fullNormalDensity_integral q branch v x X k hx

/-- The full seed arm is kept as the literal full angular characteristic integral.
The source cap cannot stand in for this object: its horizon mean has a different
characteristic coefficient. -/
private def fullSeedDensity (q : XiZeroCopy) (branch : Bool)
    (v x X k h : ℝ) : ℂ :=
  timeOnsetFirst (2*physicalRate q branch) (v+h)*fullHorizonMean q branch x h X k

private theorem scale_le_two (x : ℝ) : capScale x ≤ 2 := by
  rw [capScale, div_le_iff₀ (Real.cosh_pos x), ← Real.cosh_add_sinh x]
  have hp : 0 < Real.exp (-x) := Real.exp_pos _
  rw [← Real.cosh_sub_sinh x] at hp
  linarith

private theorem fullHorizon_radius_bound (x h : ℝ) (hh : 0 ≤ h) :
    Real.arcosh (max 1 (1+capScale x*(Real.exp h-1))) ≤ h+Real.log 4 := by
  have he : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr hh
  have hb : 0 ≤ capScale x := (scale_pos x).le
  have hs := scale_le_two x
  have hz : 1 ≤ 1+capScale x*(Real.exp h-1) := by nlinarith
  rw [max_eq_right hz]
  have hZ : 1+capScale x*(Real.exp h-1) ≤ 2*Real.exp h := by nlinarith
  have hp : 0 ≤ h+Real.log 4 :=
    add_nonneg hh (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
  have hc : 2*Real.exp h ≤ Real.cosh (h+Real.log 4) := by
    rw [Real.cosh_eq, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    linarith [Real.exp_pos (-(h+Real.log 4))]
  have ht := Real.cosh_le_cosh.mp ((Real.cosh_arcosh hz).trans_le (hZ.trans hc))
  simpa only [abs_of_nonneg (Real.arcosh_nonneg hz), abs_of_nonneg hp] using ht

private theorem fullHorizonMean_growth (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h X k : ℝ, 0 ≤ h →
      ‖fullHorizonMean q branch x h X k‖ ≤
        C*Real.exp (strictGrowthExponent q*(h+|k|)) := by
  obtain ⟨C,hC,hb⟩ := angularMean_strict_growth q branch
  have ha : 0 ≤ strictGrowthExponent q := by
    linarith [(sourceGrowthExponent_bounds q).1, (strictGrowthExponent_bounds q).1]
  refine ⟨C*Real.exp (strictGrowthExponent q*Real.log 4), by positivity,
    fun x h X k hh => ?_⟩
  have hd : 1 ≤ max 1 (1+capScale x*(Real.exp h-1)) := le_max_left _ _
  have hm := hb (Real.arcosh (max 1 (1+capScale x*(Real.exp h-1))))
    (Real.arcosh_nonneg hd)
  rw [fullHorizonMean] 
  calc
    _ ≤ C*Real.exp (strictGrowthExponent q*
        (Real.arcosh (max 1 (1+capScale x*(Real.exp h-1)))+|k|)) :=
      (le_add_of_nonneg_right (norm_nonneg _)).trans hm
    _ ≤ C*Real.exp (strictGrowthExponent q*((h+Real.log 4)+|k|)) := by
      have hr : Real.arcosh (max 1 (1+capScale x*(Real.exp h-1)))+|k| ≤
          (h+Real.log 4)+|k| := by
        linarith [fullHorizon_radius_bound x h hh]
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hr ha)) hC
    _ = _ := by
      rw [show strictGrowthExponent q*((h+Real.log 4)+|k|) =
        strictGrowthExponent q*Real.log 4+strictGrowthExponent q*(h+|k|) by ring,
        Real.exp_add]
      ring

private theorem fullSeedDensity_continuous (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) : Continuous (fullSeedDensity q branch v x X k) :=
  ((continuous_iff_continuousAt.mpr
    (fun u => (timeOnsetFirst_hasDerivAt _ u).continuousAt)).comp
      (continuous_const.add continuous_id)).mul
    (fullHorizonMean_continuous q branch x X k)

private theorem fullSeedDensity_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k h : ℝ, 0 ≤ h →
      ‖fullSeedDensity q branch v x X k h‖ ≤
        (C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|))*
          Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
  obtain ⟨B,hB,hb⟩ := onset_derivative_bound q branch
  obtain ⟨C,hC,hc⟩ := fullHorizonMean_growth q branch
  refine ⟨B*C, mul_nonneg hB hC, fun v x X k h hh => ?_⟩
  have hfirst : ‖timeOnsetFirst (2*physicalRate q branch) (v+h)‖ ≤
      B*Real.exp (-decayExponent q*(v+h)) := by
    linarith [hb (v+h), norm_nonneg (timeOnsetSecond (2*physicalRate q branch) (v+h))]
  rw [fullSeedDensity, norm_mul]
  calc
    _ ≤ (B*Real.exp (-decayExponent q*(v+h)))*
        (C*Real.exp (strictGrowthExponent q*(h+|k|))) :=
      mul_le_mul hfirst (hc x h X k hh) (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (-decayExponent q*(v+h))*
          Real.exp (strictGrowthExponent q*(h+|k|)) =
          Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|)*
            Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (B*C)*(Real.exp (-decayExponent q*(v+h))*
            Real.exp (strictGrowthExponent q*(h+|k|))) := by ring
        _ = _ := by rw [he]

private theorem fullSeedMajorant_integrable (q : XiZeroCopy) (C : ℝ) :
    IntegrableOn (fun h => C*Real.exp ((strictGrowthExponent q-decayExponent q)*h))
      (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (sub_neg.mpr (strictGrowthExponent_bounds q).2) 0).const_mul C

private theorem fullSeedDensity_integrable (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    IntegrableOn (fullSeedDensity q branch v x X k) (Ioi 0) := by
  obtain ⟨C,hC,hb⟩ := fullSeedDensity_bound q branch
  apply (fullSeedMajorant_integrable q
    (C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|))).mono'
    (fullSeedDensity_continuous q branch v x X k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact hb v x X k h hh.le

private def fullSeedArm (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ), fullSeedDensity q branch v x X k h

private theorem fullSeedArm_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k : ℝ,
      ‖fullSeedArm q branch v x X k‖ ≤
        C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|) := by
  obtain ⟨C,hC,hb⟩ := fullSeedDensity_bound q branch
  have hp : 0 < decayExponent q-strictGrowthExponent q :=
    sub_pos.mpr (strictGrowthExponent_bounds q).2
  refine ⟨C/(decayExponent q-strictGrowthExponent q), div_nonneg hC hp.le,
    fun v x X k => ?_⟩
  let D := C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|)
  have hi := fullSeedDensity_integrable q branch v x X k
  calc
    _ ≤ ∫ h in Ioi (0 : ℝ), ‖fullSeedDensity q branch v x X k h‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Ioi (0 : ℝ), D*Real.exp ((strictGrowthExponent q-decayExponent q)*h) :=
      setIntegral_mono_on hi.norm (fullSeedMajorant_integrable q D) measurableSet_Ioi
        (fun h hh => hb v x X k h hh.le)
    _ = _ := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (by linarith : strictGrowthExponent q-decayExponent q < 0)]
      simp only [mul_zero, Real.exp_zero]
      dsimp only [D]
      rw [show strictGrowthExponent q-decayExponent q =
        -(decayExponent q-strictGrowthExponent q) by ring]
      simp only [neg_div_neg_eq]
      ring

/-! The following change of delay is the literal Peierls transport.  It is
duplicated here deliberately: substituting the source-cap transport would erase
the full Goursat coefficient from the seed arm. -/
private def fullDelayFlow (b h : ℝ) : ℝ := Real.log ((b+Real.exp h-1)/b)
private def fullDelayJac (b h : ℝ) : ℝ := Real.exp h/(b+Real.exp h-1)
private def fullDelaySlope (b h : ℝ) : ℝ := (b+Real.exp h-1)⁻¹-b⁻¹
private def fullJacSlope (b h : ℝ) : ℝ := -Real.exp h/(b+Real.exp h-1)^2
private def fullDelaySecondSlope (b h : ℝ) : ℝ :=
  -(b+Real.exp h-1)⁻¹ ^ 2+b⁻¹ ^ 2
private def fullJacSecondSlope (b h : ℝ) : ℝ :=
  2*Real.exp h/(b+Real.exp h-1)^3

private theorem fullDelay_den_pos (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    0 < b+Real.exp h-1 := by
  have he := Real.one_le_exp_iff.mpr hh
  linarith

private theorem fullDelay_exp (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    Real.exp (fullDelayFlow b h) = (b+Real.exp h-1)/b :=
  Real.exp_log (div_pos (fullDelay_den_pos b h hb hh) hb)

private theorem fullDelay_pos (b h : ℝ) (hb : 0 < b) (hh : 0 < h) :
    0 < fullDelayFlow b h := by
  apply Real.log_pos
  rw [lt_div_iff₀ hb]
  have he := Real.one_lt_exp_iff.mpr hh
  linarith

private theorem fullDelay_h_derivative (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    HasDerivAt (fullDelayFlow b) (fullDelayJac b h) h := by
  have hd := (((Real.hasDerivAt_exp h).const_add b).sub_const 1).div_const b
  have hl := hd.log (div_ne_zero (fullDelay_den_pos b h hb hh).ne' hb.ne')
  convert! hl using 1
  dsimp [fullDelayJac]
  field_simp

private theorem fullDelay_b_derivative (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    HasDerivAt (fun a => fullDelayFlow a h) (fullDelaySlope b h) b := by
  have hd := (((hasDerivAt_id b).add_const (Real.exp h)).sub_const 1).div
    (hasDerivAt_id b) hb.ne'
  have hl := hd.log (div_ne_zero (fullDelay_den_pos b h hb hh).ne' hb.ne')
  convert! hl using 1
  dsimp [fullDelaySlope]
  field_simp [hb.ne', (fullDelay_den_pos b h hb hh).ne']

private theorem fullJac_b_derivative (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    HasDerivAt (fun a => fullDelayJac a h) (fullJacSlope b h) b := by
  have hd := (hasDerivAt_const b (Real.exp h)).div
    (((hasDerivAt_id b).add_const (Real.exp h)).sub_const 1)
      (fullDelay_den_pos b h hb hh).ne'
  convert! hd using 1
  simp only [fullJacSlope, zero_mul, mul_one, zero_sub, id_eq]

private theorem fullDelaySlope_b_derivative (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    HasDerivAt (fun a => fullDelaySlope a h) (fullDelaySecondSlope b h) b := by
  have hden : HasDerivAt (fun a : ℝ => a+Real.exp h-1) 1 b := by
    simpa using ((hasDerivAt_id b).add_const (Real.exp h)).sub_const 1
  have hinv := hden.inv (fullDelay_den_pos b h hb hh).ne'
  have hbinv := hasDerivAt_inv hb.ne'
  have hfun : (fun a : ℝ => fullDelaySlope a h) =ᶠ[𝓝 b]
      ((fun a => a+Real.exp h-1)⁻¹-fun a : ℝ => a⁻¹) :=
    Filter.Eventually.of_forall (fun a => rfl)
  have hval : fullDelaySecondSlope b h =
      -1/(b+Real.exp h-1)^2- -(b^2)⁻¹ := by
    rw [fullDelaySecondSlope]
    field_simp [(fullDelay_den_pos b h hb hh).ne', hb.ne']
    ring
  exact (hinv.sub hbinv).congr_of_eventuallyEq hfun |>.congr_deriv hval.symm

private theorem fullJacSlope_b_derivative (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    HasDerivAt (fun a => fullJacSlope a h) (fullJacSecondSlope b h) b := by
  have hden : HasDerivAt (fun a : ℝ => a+Real.exp h-1) 1 b := by
    simpa using ((hasDerivAt_id b).add_const (Real.exp h)).sub_const 1
  have hinv := hden.inv (fullDelay_den_pos b h hb hh).ne'
  have hsquare := hinv.mul hinv
  have hfun : (fun a : ℝ => fullJacSlope a h) =ᶠ[𝓝 b]
      (fun y => -Real.exp h*
        ((fun a => a+Real.exp h-1)⁻¹*(fun a => a+Real.exp h-1)⁻¹) y) :=
    Filter.Eventually.of_forall (fun a => by
      simp only [fullJacSlope, Pi.mul_apply]
      rw [div_eq_mul_inv, ← inv_pow, pow_two]
      simp only [Pi.inv_apply])
  have hval : fullJacSecondSlope b h =
      -Real.exp h*(-1/(b+Real.exp h-1)^2*
        (fun a => a+Real.exp h-1)⁻¹ b+
        (fun a => a+Real.exp h-1)⁻¹ b*(-1/(b+Real.exp h-1)^2)) := by
    change 2*Real.exp h/(b+Real.exp h-1)^3 =
      -Real.exp h*(-1/(b+Real.exp h-1)^2*
        (b+Real.exp h-1)⁻¹+(b+Real.exp h-1)⁻¹*
          (-1/(b+Real.exp h-1)^2))
    field_simp [(fullDelay_den_pos b h hb hh).ne']
    ring
  exact (hsquare.const_mul (-Real.exp h)).congr_of_eventuallyEq hfun |>.congr_deriv hval.symm

private theorem fullDelay_image (b : ℝ) (hb : 0 < b) :
    fullDelayFlow b '' Ioi 0 = Ioi 0 := by
  apply Set.Subset.antisymm
  · rintro y ⟨h,hh,rfl⟩
    exact fullDelay_pos b h hb hh
  · intro y hy
    let t := Real.log (1+b*(Real.exp y-1))
    have hyE : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy
    have ha : 1 < 1+b*(Real.exp y-1) := by nlinarith
    have ht : 0 < t := Real.log_pos ha
    refine ⟨t,ht,?_⟩
    apply Real.exp_injective
    rw [fullDelay_exp b t hb ht.le,
      show Real.exp t = 1+b*(Real.exp y-1) from Real.exp_log (by linarith)]
    field_simp
    ring

private theorem fullDelay_inj (b : ℝ) (hb : 0 < b) :
    Set.InjOn (fullDelayFlow b) (Ioi 0) := by
  intro h hh t ht he
  have hf := congrArg Real.exp he
  rw [fullDelay_exp b h hb hh.le, fullDelay_exp b t hb ht.le] at hf
  have hd := (div_left_inj' hb.ne').mp hf
  exact Real.exp_injective (by linarith)

private theorem fullDelay_local_bounds (b h : ℝ) (hb : b ∈ Ioo (1/2 : ℝ) 2)
    (hh : 0 ≤ h) :
    0 < b ∧ 0 < fullDelayJac b h ∧ fullDelayJac b h ≤ 2 ∧
      |fullDelaySlope b h| ≤ 4 ∧ |fullJacSlope b h| ≤ 4 ∧
        h-Real.log 2 ≤ fullDelayFlow b h := by
  have hb0 : 0 < b := by linarith [hb.1]
  have he : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr hh
  have hd := fullDelay_den_pos b h hb0 hh
  have hdi : (b+Real.exp h-1)⁻¹ ≤ 2 := by
    rw [← one_div, div_le_iff₀ hd]
    linarith [hb.1]
  have hbi : b⁻¹ ≤ 2 := by
    rw [← one_div, div_le_iff₀ hb0]
    linarith [hb.1]
  have hj0 : 0 < fullDelayJac b h := div_pos (Real.exp_pos h) hd
  have hj2 : fullDelayJac b h ≤ 2 := by
    dsimp [fullDelayJac]
    rw [div_le_iff₀ hd]
    linarith [hb.1]
  have hs : |fullDelaySlope b h| ≤ 4 := by
    apply (abs_sub _ _).trans
    rw [abs_of_pos (inv_pos.mpr hd), abs_of_pos (inv_pos.mpr hb0)]
    linarith
  have hjs : |fullJacSlope b h| ≤ 4 := by
    rw [fullJacSlope, abs_div, abs_neg, abs_of_pos (Real.exp_pos h),
      abs_of_nonneg (sq_nonneg _)]
    rw [div_le_iff₀ (sq_pos_of_pos hd)]
    have hhalf : (1/2 : ℝ) ≤ b+Real.exp h-1 := by linarith [hb.1]
    nlinarith
  refine ⟨hb0,hj0,hj2,hs,hjs,?_⟩
  rw [← Real.exp_le_exp, fullDelay_exp b h hb0 hh, Real.exp_sub,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [le_div_iff₀ hb0]
  have hp := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hb.2.le)
  nlinarith

private theorem fullDelay_second_local_bounds (b h : ℝ) (hb : b ∈ Ioo (1/2 : ℝ) 2)
    (hh : 0 ≤ h) :
    |fullDelaySecondSlope b h| ≤ 8 ∧ |fullJacSecondSlope b h| ≤ 16 := by
  have hb0 : 0 < b := by linarith [hb.1]
  have he : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr hh
  have hd : 0 < b+Real.exp h-1 := fullDelay_den_pos b h hb0 hh
  have hdi : (b+Real.exp h-1)⁻¹ ≤ 2 := by
    rw [← one_div, div_le_iff₀ hd]
    linarith [hb.1]
  have hbi : b⁻¹ ≤ 2 := by
    rw [← one_div, div_le_iff₀ hb0]
    linarith [hb.1]
  have hdisq : (b+Real.exp h-1)⁻¹ ^ 2 ≤ 4 := by
    have hp := mul_nonneg (sub_nonneg.mpr hdi)
      (by positivity : 0 ≤ (b+Real.exp h-1)⁻¹+2)
    nlinarith
  have hbisq : b⁻¹ ^ 2 ≤ 4 := by
    have hp := mul_nonneg (sub_nonneg.mpr hbi) (by positivity : 0 ≤ b⁻¹+2)
    nlinarith
  constructor
  · rw [fullDelaySecondSlope]
    calc
      _ ≤ |-(b+Real.exp h-1)⁻¹ ^ 2|+|b⁻¹ ^ 2| := abs_add _ _
      _ = (b+Real.exp h-1)⁻¹ ^ 2+b⁻¹ ^ 2 := by
        rw [abs_neg, abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
      _ ≤ 8 := by linarith
  · have hj : Real.exp h/(b+Real.exp h-1) ≤ 2 := by
      rw [div_le_iff₀ hd]
      linarith [hb.1]
    have hform : fullJacSecondSlope b h =
        2*(Real.exp h/(b+Real.exp h-1))*(b+Real.exp h-1)⁻¹ ^ 2 := by
      rw [fullJacSecondSlope]
      field_simp
      ring
    rw [hform, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)),
      abs_of_nonneg hj, abs_of_nonneg (sq_nonneg _)]
    nlinarith

private def fullMovedDensity (q : XiZeroCopy) (branch : Bool)
    (v x X k b h : ℝ) : ℂ :=
  timeOnsetFirst (2*physicalRate q branch) (v+fullDelayFlow b h)*
    (fullDelayJac b h : ℂ)*fullHorizonMean q branch x h X k

private def fullMovedDerivative (q : XiZeroCopy) (branch : Bool)
    (v x X k b h : ℝ) : ℂ :=
  (timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullDelaySlope b h : ℂ)*(fullDelayJac b h : ℂ)+
    timeOnsetFirst (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullJacSlope b h : ℂ))*fullHorizonMean q branch x h X k

/-! This is the literal second delay derivative.  The angular kernel is held at
the base circle; every derivative displayed here is a derivative of the exact
time/Jacobian transport. -/
private def fullMovedSecondDerivative (q : XiZeroCopy) (branch : Bool)
    (v x X k b h : ℝ) : ℂ :=
  (timeOnsetThird (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullDelaySlope b h : ℂ)^2*(fullDelayJac b h : ℂ)+
    timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullDelaySecondSlope b h : ℂ)*(fullDelayJac b h : ℂ)+
    2*timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullDelaySlope b h : ℂ)*(fullJacSlope b h : ℂ)+
    timeOnsetFirst (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullJacSecondSlope b h : ℂ))*fullHorizonMean q branch x h X k

private theorem fullMovedDensity_derivative (q : XiZeroCopy) (branch : Bool)
    (v x X k b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    HasDerivAt (fun a => fullMovedDensity q branch v x X k a h)
      (fullMovedDerivative q branch v x X k b h) b := by
  have hg := (timeOnsetFirst_hasDerivAt (2*physicalRate q branch)
    (v+fullDelayFlow b h)).scomp b
      ((fullDelay_b_derivative b h hb hh).const_add v)
  have hj := (fullJac_b_derivative b h hb hh).ofReal_comp
  convert! (hg.mul hj).mul_const (fullHorizonMean q branch x h X k) using 1
  simp only [fullMovedDerivative, Complex.real_smul, Function.comp_apply]
  ring

private theorem fullMovedDerivative_derivative (q : XiZeroCopy) (branch : Bool)
    (v x X k b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    HasDerivAt (fun a => fullMovedDerivative q branch v x X k a h)
      (fullMovedSecondDerivative q branch v x X k b h) b := by
  have hg2 := (timeOnsetSecond_hasDerivAt (2*physicalRate q branch)
    (v+fullDelayFlow b h)).scomp b
      ((fullDelay_b_derivative b h hb hh).const_add v)
  have hs := (fullDelaySlope_b_derivative b h hb hh).ofReal_comp
  have hj := (fullJac_b_derivative b h hb hh).ofReal_comp
  have hg1 := (timeOnsetFirst_hasDerivAt (2*physicalRate q branch)
    (v+fullDelayFlow b h)).scomp b
      ((fullDelay_b_derivative b h hb hh).const_add v)
  have hjs := (fullJacSlope_b_derivative b h hb hh).ofReal_comp
  convert! (((hg2.mul hs).mul hj).add (hg1.mul hjs)).mul_const
    (fullHorizonMean q branch x h X k) using 1
  simp only [fullMovedSecondDerivative, Complex.real_smul, Function.comp_apply]
  ring

private theorem fullMovedDerivative_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k b h : ℝ, b ∈ Ioo (1/2 : ℝ) 2 → 0 ≤ h →
      ‖fullMovedDerivative q branch v x X k b h‖ ≤
        C*Real.exp (-decayExponent q*(v-Real.log 2)+strictGrowthExponent q*|k|)*
          Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
  obtain ⟨B,hB,hb⟩ := onset_derivative_bound q branch
  obtain ⟨C,hC,hc⟩ := fullHorizonMean_growth q branch
  refine ⟨8*B*C, by positivity, fun v x X k b h hbl hh => ?_⟩
  obtain ⟨hb0,hj0,hj2,hs,hjs,hflow⟩ := fullDelay_local_bounds b h hbl hh
  have hg1 := norm_nonneg (timeOnsetFirst (2*physicalRate q branch) (v+fullDelayFlow b h))
  have hg2 := norm_nonneg (timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h))
  have hm : ‖timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullDelaySlope b h : ℂ)*(fullDelayJac b h : ℂ)+
      timeOnsetFirst (2*physicalRate q branch) (v+fullDelayFlow b h)*
        (fullJacSlope b h : ℂ)‖ ≤
      8*B*Real.exp (-decayExponent q*(v+fullDelayFlow b h)) := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hj0]
    have ha := mul_le_mul_of_nonneg_left hs hg2
    have hb' := mul_le_mul_of_nonneg_left hjs hg1
    have hj := mul_le_mul ha hj2 (le_of_lt hj0) (by positivity)
    nlinarith [hb (v+fullDelayFlow b h)]
  have he : Real.exp (-decayExponent q*(v+fullDelayFlow b h)) ≤
      Real.exp (-decayExponent q*(v-Real.log 2+h)) := by
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonpos_left hflow
      (neg_nonpos.mpr (lt_of_le_of_lt (sourceGrowthExponent_bounds q).1
        (decayExponent_bounds q).1).le)
    linarith
  rw [fullMovedDerivative, norm_mul]
  calc
    _ ≤ (8*B*Real.exp (-decayExponent q*(v+fullDelayFlow b h)))*
        (C*Real.exp (strictGrowthExponent q*(h+|k|))) :=
      mul_le_mul hm (hc x h X k hh) (norm_nonneg _) (by positivity)
    _ ≤ (8*B*Real.exp (-decayExponent q*(v-Real.log 2+h)))*
        (C*Real.exp (strictGrowthExponent q*(h+|k|))) := by gcongr
    _ = _ := by
      have hexp : Real.exp (-decayExponent q*(v-Real.log 2+h))*
          Real.exp (strictGrowthExponent q*(h+|k|)) =
          Real.exp (-decayExponent q*(v-Real.log 2)+strictGrowthExponent q*|k|)*
            Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (8*B*C)*(Real.exp (-decayExponent q*(v-Real.log 2+h))*
            Real.exp (strictGrowthExponent q*(h+|k|))) := by ring
        _ = _ := by rw [hexp]

private theorem fullDelay_one (h : ℝ) :
    fullDelayFlow 1 h = h ∧ fullDelayJac 1 h = 1 ∧
      fullDelaySlope 1 h = Real.exp (-h)-1 ∧ fullJacSlope 1 h = -Real.exp (-h) := by
  have he := (Real.exp_pos h).ne'
  simp [fullDelayFlow, fullDelayJac, fullDelaySlope, fullJacSlope, Real.exp_neg]
  field_simp

private theorem fullDelay_second_one (h : ℝ) :
    fullDelaySecondSlope 1 h = 1-Real.exp (-2*h) ∧
      fullJacSecondSlope 1 h = 2*Real.exp (-2*h) := by
  have he2 : Real.exp (2*h) = Real.exp h ^ 2 := by
    rw [show 2*h = h+h by ring, Real.exp_add]
  have hneg : -2*h = -(2*h) := by ring
  constructor <;>
    simp [fullDelaySecondSlope, fullJacSecondSlope, hneg, Real.exp_neg, he2] <;>
    field_simp <;>
    ring

private theorem fullMovedDensity_one (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) :
    fullMovedDensity q branch v x X k 1 = fullSeedDensity q branch v x X k := by
  funext h
  rw [fullMovedDensity, (fullDelay_one h).1, (fullDelay_one h).2.1]
  simp only [Complex.ofReal_one, mul_one, fullSeedDensity]

private theorem fullMovedDerivative_one (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) :
    fullMovedDerivative q branch v x X k 1 =
      fun h => -normalWeight q branch v h*fullHorizonMean q branch x h X k := by
  funext h
  rw [fullMovedDerivative, (fullDelay_one h).1, (fullDelay_one h).2.1,
    (fullDelay_one h).2.2.1, (fullDelay_one h).2.2.2]
  simp only [normalWeight, Complex.ofReal_one, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

private theorem fullMovedDensity_measurable (q : XiZeroCopy) (branch : Bool)
    (v x X k b : ℝ) (hb : 0 < b) :
    AEStronglyMeasurable (fullMovedDensity q branch v x X k b)
      (volume.restrict (Ioi 0)) := by
  have hf : ContinuousOn (fullDelayFlow b) (Ioi 0) := fun h hh =>
    (fullDelay_h_derivative b h hb hh.le).continuousAt.continuousWithinAt
  have hj : ContinuousOn (fullDelayJac b) (Ioi 0) :=
    Real.continuous_exp.continuousOn.div
      ((continuous_const.add Real.continuous_exp).sub continuous_const).continuousOn
      (fun h hh => (fullDelay_den_pos b h hb hh.le).ne')
  have hg : ContinuousOn (fun h => timeOnsetFirst (2*physicalRate q branch)
      (v+fullDelayFlow b h)) (Ioi 0) :=
    (continuous_iff_continuousAt.mpr
      (fun u => (timeOnsetFirst_hasDerivAt _ u).continuousAt)).comp_continuousOn
        (continuousOn_const.add hf)
  exact ((hg.mul (Complex.continuous_ofReal.comp_continuousOn hj)).mul
    (fullHorizonMean_continuous q branch x X k).continuousOn).aestronglyMeasurable
      measurableSet_Ioi

private theorem fullMovedDerivative_measurable (q : XiZeroCopy) (branch : Bool)
    (v x X k b : ℝ) (hb : 0 < b) :
    AEStronglyMeasurable (fullMovedDerivative q branch v x X k b)
      (volume.restrict (Ioi 0)) := by
  have hf : ContinuousOn (fullDelayFlow b) (Ioi 0) := fun h hh =>
    (fullDelay_h_derivative b h hb hh.le).continuousAt.continuousWithinAt
  have hj : ContinuousOn (fullDelayJac b) (Ioi 0) :=
    Real.continuous_exp.continuousOn.div
      ((continuous_const.add Real.continuous_exp).sub continuous_const).continuousOn
      (fun h hh => (fullDelay_den_pos b h hb hh.le).ne')
  have hs : ContinuousOn (fullDelaySlope b) (Ioi 0) := by
    change ContinuousOn (fun h => (b+Real.exp h-1)⁻¹-b⁻¹) (Ioi 0)
    exact (((continuousOn_const.add Real.continuous_exp.continuousOn).sub
      continuousOn_const).inv₀ (fun h hh => (fullDelay_den_pos b h hb hh.le).ne')).sub
        (continuousOn_const.inv₀ (fun _ _ => hb.ne'))
  have hjs : ContinuousOn (fullJacSlope b) (Ioi 0) := by
    change ContinuousOn (fun h => -Real.exp h/(b+Real.exp h-1)^2) (Ioi 0)
    exact (Real.continuous_exp.continuousOn.div
      (((continuousOn_const.add Real.continuous_exp.continuousOn).sub
        continuousOn_const).pow 2)
      (fun h hh => pow_ne_zero 2 (fullDelay_den_pos b h hb hh.le).ne')).neg
  have hg1 : ContinuousOn (fun h => timeOnsetFirst (2*physicalRate q branch)
      (v+fullDelayFlow b h)) (Ioi 0) :=
    (continuous_iff_continuousAt.mpr
      (fun u => (timeOnsetFirst_hasDerivAt _ u).continuousAt)).comp_continuousOn
        (continuousOn_const.add hf)
  have hg2 : ContinuousOn (fun h => timeOnsetSecond (2*physicalRate q branch)
      (v+fullDelayFlow b h)) (Ioi 0) :=
    (timeOnsetSecond_continuous _).comp_continuousOn (continuousOn_const.add hf)
  simpa only [fullMovedDerivative] using
    (((hg2.mul (Complex.continuous_ofReal.comp_continuousOn hs)).mul
      (Complex.continuous_ofReal.comp_continuousOn hj)).add
      (hg1.mul (Complex.continuous_ofReal.comp_continuousOn hjs))).mul
        (fullHorizonMean_continuous q branch x X k).continuousOn).aestronglyMeasurable
          measurableSet_Ioi

private theorem fullMovedDensity_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k b h : ℝ, b ∈ Ioo (1/2 : ℝ) 2 → 0 ≤ h →
      ‖fullMovedDensity q branch v x X k b h‖ ≤
        C*Real.exp (-decayExponent q*(v-Real.log 2)+strictGrowthExponent q*|k|)*
          Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
  obtain ⟨B,hB,hb⟩ := onset_derivative_bound q branch
  obtain ⟨C,hC,hc⟩ := fullHorizonMean_growth q branch
  refine ⟨2*B*C, by positivity, fun v x X k b h hbl hh => ?_⟩
  obtain ⟨hb0,hj0,hj2,hs,hjs,hflow⟩ := fullDelay_local_bounds b h hbl hh
  have hg : ‖timeOnsetFirst (2*physicalRate q branch) (v+fullDelayFlow b h)‖ ≤
      B*Real.exp (-decayExponent q*(v+fullDelayFlow b h)) := by
    linarith [hb (v+fullDelayFlow b h),
      norm_nonneg (timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h))]
  have he : Real.exp (-decayExponent q*(v+fullDelayFlow b h)) ≤
      Real.exp (-decayExponent q*(v-Real.log 2+h)) := by
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonpos_left hflow
      (neg_nonpos.mpr (lt_of_le_of_lt (sourceGrowthExponent_bounds q).1
        (decayExponent_bounds q).1).le)
    linarith
  rw [fullMovedDensity, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hj0]
  calc
    _ ≤ (B*Real.exp (-decayExponent q*(v+fullDelayFlow b h)))*2*
        (C*Real.exp (strictGrowthExponent q*(h+|k|))) := by gcongr
    _ ≤ (B*Real.exp (-decayExponent q*(v-Real.log 2+h)))*2*
        (C*Real.exp (strictGrowthExponent q*(h+|k|))) := by gcongr
    _ = _ := by
      have hexp : Real.exp (-decayExponent q*(v-Real.log 2+h))*
          Real.exp (strictGrowthExponent q*(h+|k|)) =
          Real.exp (-decayExponent q*(v-Real.log 2)+strictGrowthExponent q*|k|)*
            Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (2*B*C)*(Real.exp (-decayExponent q*(v-Real.log 2+h))*
            Real.exp (strictGrowthExponent q*(h+|k|))) := by ring
        _ = _ := by rw [hexp]

private theorem fullMovedSecondDerivative_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k b h : ℝ, b ∈ Ioo (1/2 : ℝ) 2 → 0 ≤ h →
      ‖fullMovedSecondDerivative q branch v x X k b h‖ ≤
        C*Real.exp (-decayExponent q*(v-Real.log 2)+strictGrowthExponent q*|k|)*
          Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
  obtain ⟨B₁,hB₁,hb₁⟩ := onset_derivative_bound q branch
  obtain ⟨B₂,hB₂,hb₂⟩ := onset_second_derivative_bound q branch
  obtain ⟨C,hC,hc⟩ := fullHorizonMean_growth q branch
  refine ⟨96*(B₁+B₂)*C, by positivity, fun v x X k b h hbl hh => ?_⟩
  obtain ⟨hb0,hj0,hj2,hs,hjs,hflow⟩ := fullDelay_local_bounds b h hbl hh
  obtain ⟨hss,hjss⟩ := fullDelay_second_local_bounds b h hbl hh
  let D := (B₁+B₂)*Real.exp (-decayExponent q*(v+fullDelayFlow b h))
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hg1 : ‖timeOnsetFirst (2*physicalRate q branch) (v+fullDelayFlow b h)‖ ≤ D := by
    calc
      _ ≤ B₁*Real.exp (-decayExponent q*(v+fullDelayFlow b h)) := by
        linarith [hb₁ (v+fullDelayFlow b h),
          norm_nonneg (timeOnsetSecond (2*physicalRate q branch)
            (v+fullDelayFlow b h))]
      _ ≤ D := by dsimp only [D]; gcongr
  have hg2 : ‖timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)‖ ≤ D := by
    calc
      _ ≤ B₁*Real.exp (-decayExponent q*(v+fullDelayFlow b h)) := by
        linarith [hb₁ (v+fullDelayFlow b h),
          norm_nonneg (timeOnsetFirst (2*physicalRate q branch)
            (v+fullDelayFlow b h))]
      _ ≤ D := by dsimp only [D]; gcongr
  have hg3 : ‖timeOnsetThird (2*physicalRate q branch) (v+fullDelayFlow b h)‖ ≤ D := by
    calc
      _ ≤ B₂*Real.exp (-decayExponent q*(v+fullDelayFlow b h)) := by
        linarith [hb₂ (v+fullDelayFlow b h),
          norm_nonneg (timeOnsetSecond (2*physicalRate q branch)
            (v+fullDelayFlow b h))]
      _ ≤ D := by dsimp only [D]; gcongr
  have hs2 : |fullDelaySlope b h|^2 ≤ 16 := by
    have hp := mul_nonneg (sub_nonneg.mpr hs)
      (by positivity : 0 ≤ |fullDelaySlope b h|+4)
    nlinarith
  have ht1 : ‖timeOnsetThird (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullDelaySlope b h : ℂ)^2*(fullDelayJac b h : ℂ)‖ ≤ 32*D := by
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hj0]
    calc
      _ ≤ D*16*2 := by gcongr
      _ = 32*D := by ring
  have ht2 : ‖timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullDelaySecondSlope b h : ℂ)*(fullDelayJac b h : ℂ)‖ ≤ 16*D := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hj0]
    calc
      _ ≤ D*8*2 := by gcongr
      _ = 16*D := by ring
  have ht3 : ‖2*timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullDelaySlope b h : ℂ)*(fullJacSlope b h : ℂ)‖ ≤ 32*D := by
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs]
    calc
      _ ≤ 2*D*4*4 := by gcongr
      _ = 32*D := by ring
  have ht4 : ‖timeOnsetFirst (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullJacSecondSlope b h : ℂ)‖ ≤ 16*D := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ D*16 := by gcongr
      _ = 16*D := by ring
  have hm : ‖timeOnsetThird (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullDelaySlope b h : ℂ)^2*(fullDelayJac b h : ℂ)+
    timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullDelaySecondSlope b h : ℂ)*(fullDelayJac b h : ℂ)+
    2*timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullDelaySlope b h : ℂ)*(fullJacSlope b h : ℂ)+
    timeOnsetFirst (2*physicalRate q branch) (v+fullDelayFlow b h)*
      (fullJacSecondSlope b h : ℂ)‖ ≤ 96*D := by
    calc
      _ ≤ ‖timeOnsetThird (2*physicalRate q branch) (v+fullDelayFlow b h)*
          (fullDelaySlope b h : ℂ)^2*(fullDelayJac b h : ℂ)+
        timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)*
          (fullDelaySecondSlope b h : ℂ)*(fullDelayJac b h : ℂ)+
        2*timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)*
          (fullDelaySlope b h : ℂ)*(fullJacSlope b h : ℂ)‖+
        ‖timeOnsetFirst (2*physicalRate q branch) (v+fullDelayFlow b h)*
          (fullJacSecondSlope b h : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖timeOnsetThird (2*physicalRate q branch) (v+fullDelayFlow b h)*
          (fullDelaySlope b h : ℂ)^2*(fullDelayJac b h : ℂ)+
        timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)*
          (fullDelaySecondSlope b h : ℂ)*(fullDelayJac b h : ℂ)‖+
        ‖2*timeOnsetSecond (2*physicalRate q branch) (v+fullDelayFlow b h)*
          (fullDelaySlope b h : ℂ)*(fullJacSlope b h : ℂ)‖)+
        ‖timeOnsetFirst (2*physicalRate q branch) (v+fullDelayFlow b h)*
          (fullJacSecondSlope b h : ℂ)‖ := by
          gcongr
          exact norm_add_le _ _
      _ ≤ 96*D := by linarith
  have he : Real.exp (-decayExponent q*(v+fullDelayFlow b h)) ≤
      Real.exp (-decayExponent q*(v-Real.log 2+h)) := by
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonpos_left hflow
      (neg_nonpos.mpr (lt_of_le_of_lt (sourceGrowthExponent_bounds q).1
        (decayExponent_bounds q).1).le)
    linarith
  rw [fullMovedSecondDerivative, norm_mul]
  calc
    _ ≤ (96*D)*(C*Real.exp (strictGrowthExponent q*(h+|k|))) :=
      mul_le_mul hm (hc x h X k hh) (norm_nonneg _) (by positivity)
    _ ≤ (96*((B₁+B₂)*Real.exp (-decayExponent q*(v-Real.log 2+h))))*
        (C*Real.exp (strictGrowthExponent q*(h+|k|))) := by
      dsimp only [D]
      gcongr
    _ = _ := by
      have hexp : Real.exp (-decayExponent q*(v-Real.log 2+h))*
          Real.exp (strictGrowthExponent q*(h+|k|)) =
          Real.exp (-decayExponent q*(v-Real.log 2)+strictGrowthExponent q*|k|)*
            Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (96*(B₁+B₂)*C)*(Real.exp (-decayExponent q*(v-Real.log 2+h))*
            Real.exp (strictGrowthExponent q*(h+|k|))) := by ring
        _ = _ := by rw [hexp]

private theorem fullMovedDensity_integrable (q : XiZeroCopy) (branch : Bool)
    (v x X k b : ℝ) (hb : b ∈ Ioo (1/2 : ℝ) 2) :
    IntegrableOn (fullMovedDensity q branch v x X k b) (Ioi 0) := by
  obtain ⟨C,hC,hm⟩ := fullMovedDensity_bound q branch
  let B := C*Real.exp (-decayExponent q*(v-Real.log 2)+strictGrowthExponent q*|k|)
  apply (fullSeedMajorant_integrable q B).mono'
    (fullMovedDensity_measurable q branch v x X k b (by linarith [hb.1]))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact hm v x X k b h hb hh.le

/-! The first parameter differentiation is available on the entire literal
delay neighbourhood, not only at the base scale.  This is what permits the
second differentiation below. -/
private theorem fullMovedIntegral_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (v x X k b : ℝ) (hb : b ∈ Ioo (1/2 : ℝ) 2) :
    HasDerivAt (fun a => ∫ h in Ioi (0 : ℝ), fullMovedDensity q branch v x X k a h)
      (∫ h in Ioi (0 : ℝ), fullMovedDerivative q branch v x X k b h) b := by
  obtain ⟨C,hC,hm⟩ := fullMovedDerivative_bound q branch
  let B := C*Real.exp (-decayExponent q*(v-Real.log 2)+strictGrowthExponent q*|k|)
  have hn : Ioo (1/2 : ℝ) 2 ∈ 𝓝 b := Ioo_mem_nhds hb.1 hb.2
  have hmeas : ∀ᶠ a in 𝓝 b, AEStronglyMeasurable
      (fullMovedDensity q branch v x X k a) (volume.restrict (Ioi 0)) := by
    filter_upwards [hn] with a ha
    exact fullMovedDensity_measurable q branch v x X k a (by linarith [ha.1])
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun a h => fullMovedDensity q branch v x X k a h)
    (F' := fun a h => fullMovedDerivative q branch v x X k a h)
    (bound := fun h => B*Real.exp ((strictGrowthExponent q-decayExponent q)*h))
    hn hmeas (fullMovedDensity_integrable q branch v x X k b hb)
    (fullMovedDerivative_measurable q branch v x X k b (by linarith [hb.1]))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      intro a ha
      exact hm v x X k a h ha hh.le)
    (fullSeedMajorant_integrable q B)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      intro a ha
      exact fullMovedDensity_derivative q branch v x X k a h
        (by linarith [ha.1]) hh.le)).2

private theorem fullMovedIntegral_derivative (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    HasDerivAt (fun b => ∫ h in Ioi (0 : ℝ), fullMovedDensity q branch v x X k b h)
      (-fullNormalArm q branch v x X k) 1 := by
  obtain ⟨C,hC,hb⟩ := fullMovedDerivative_bound q branch
  let B := C*Real.exp (-decayExponent q*(v-Real.log 2)+strictGrowthExponent q*|k|)
  have hn : Ioo (1/2 : ℝ) 2 ∈ 𝓝 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hm : ∀ᶠ b in 𝓝 (1 : ℝ), AEStronglyMeasurable
      (fullMovedDensity q branch v x X k b) (volume.restrict (Ioi 0)) := by
    filter_upwards [hn] with b hb
    exact fullMovedDensity_measurable q branch v x X k b (by linarith [hb.1])
  have hi : IntegrableOn (fullMovedDensity q branch v x X k 1) (Ioi 0) := by
    rw [fullMovedDensity_one]
    exact fullSeedDensity_integrable q branch v x X k
  have hm' : AEStronglyMeasurable (fullMovedDerivative q branch v x X k 1)
      (volume.restrict (Ioi 0)) := by
    rw [fullMovedDerivative_one]
    exact ((normalWeight_continuous q branch v).mul
      (fullHorizonMean_continuous q branch x X k)).neg.aestronglyMeasurable
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun b h => fullMovedDensity q branch v x X k b h)
    (F' := fun b h => fullMovedDerivative q branch v x X k b h)
    (bound := fun h => B*Real.exp ((strictGrowthExponent q-decayExponent q)*h))
    hn hm hi hm'
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      intro b hbl
      exact hb v x X k b h hbl hh.le)
    (fullSeedMajorant_integrable q B)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      intro b hbl
      exact fullMovedDensity_derivative q branch v x X k b h
        (by linarith [hbl.1]) hh.le)).2
  simpa only [fullMovedDerivative_one, integral_neg, fullNormalArm] using hd

private theorem scale_derivative (x : ℝ) :
    HasDerivAt capScale (capScale x*(2-capScale x)) x := by
  have hd := (Real.hasDerivAt_exp x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  convert! hd using 1
  dsimp [capScale]
  rw [← Real.cosh_add_sinh x]
  field_simp
  ring

private theorem scale_second_derivative (x : ℝ) :
    HasDerivAt (fun y => capScale y*(2-capScale y))
      (2*capScale x*(2-capScale x)*(1-capScale x)) x := by
  have hs := scale_derivative x
  convert! hs.mul ((hasDerivAt_const x 2).sub hs) using 1
  dsimp
  ring

private theorem scale_ratio_base_hasDerivAt (x y : ℝ) :
    HasDerivAt (fun z => capScale z/capScale x)
      (capScale y*(2-capScale y)/capScale x) y := by
  have hx : capScale x ≠ 0 := (scale_pos x).ne'
  convert! (scale_derivative y).div_const (capScale x) using 1

private theorem scale_ratio_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => capScale y/capScale x) (2-capScale x) x := by
  have hx : capScale x ≠ 0 := (scale_pos x).ne'
  convert! scale_ratio_base_hasDerivAt x x using 1
  field_simp [hx]

private theorem scale_ratio_derivative_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => deriv (fun z => capScale z/capScale x) y)
      (2*(2-capScale x)*(1-capScale x)) x := by
  have hfun : (fun y => deriv (fun z => capScale z/capScale x) y) =
      fun y => capScale y*(2-capScale y)/capScale x := by
    funext y
    exact (scale_ratio_base_hasDerivAt x y).deriv
  rw [hfun]
  convert! (scale_second_derivative x).div_const (capScale x) using 1
  field_simp [(scale_pos x).ne']

private theorem fullHorizonMean_moved (q : XiZeroCopy) (branch : Bool)
    (x y X k h : ℝ) (hh : 0 ≤ h) :
    fullHorizonMean q branch x (fullDelayFlow (capScale x/capScale y) h) X k =
      fullHorizonMean q branch y h X k := by
  rw [fullHorizonMean, fullDelay_exp _ _
    (div_pos (scale_pos x) (scale_pos y)) hh]
  congr 3
  field_simp [(scale_pos x).ne', (scale_pos y).ne']
  ring

private theorem fullSeedArm_moved (q : XiZeroCopy) (branch : Bool) (v x y X k : ℝ) :
    fullSeedArm q branch v x X k =
      ∫ h in Ioi (0 : ℝ), fullMovedDensity q branch v y X k
        (capScale x/capScale y) h := by
  let b := capScale x/capScale y
  have hb : 0 < b := div_pos (scale_pos x) (scale_pos y)
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun h (hh : h ∈ Ioi (0 : ℝ)) =>
      (fullDelay_h_derivative b h hb hh.le).hasDerivWithinAt)
    (fullDelay_inj b hb) (fullSeedDensity q branch v x X k)
  rw [fullDelay_image b hb] at hi
  change (∫ h in Ioi (0 : ℝ), fullSeedDensity q branch v x X k h) = _
  rw [hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h hh
  change |fullDelayJac b h| • fullSeedDensity q branch v x X k (fullDelayFlow b h) = _
  rw [abs_of_pos (show 0 < fullDelayJac b h from
    div_pos (Real.exp_pos h) (fullDelay_den_pos b h hb hh.le)), Complex.real_smul]
  rw [fullSeedDensity, show b = capScale x/capScale y from rfl,
    fullHorizonMean_moved q branch x y X k h hh.le]
  dsimp [fullMovedDensity]
  ring

private theorem fullSeedArm_normal_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    HasDerivAt (fun y => fullSeedArm q branch v y X k)
      (-((2-capScale x : ℝ) : ℂ)*fullNormalArm q branch v x X k) x := by
  have hk : HasDerivAt (fun y => capScale y/capScale x) (2-capScale x) x := by
    convert! (scale_derivative x).div_const (capScale x) using 1
    field_simp [(scale_pos x).ne']
  have ht := (fullMovedIntegral_derivative q branch v x X k).scomp_of_eq x hk
    (by simp only [div_self (scale_pos x).ne'] : (1 : ℝ) = capScale x/capScale x)
  convert! ht using 1
  · funext y
    exact fullSeedArm_moved q branch v y x X k
  · simp only [Complex.real_smul]
    ring

private def fullSeedTimeDensity (q : XiZeroCopy) (branch : Bool)
    (v x X k h : ℝ) : ℂ :=
  timeOnsetSecond (2*physicalRate q branch) (v+h)*fullHorizonMean q branch x h X k

private theorem fullSeedTimeDensity_continuous (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) : Continuous (fullSeedTimeDensity q branch v x X k) :=
  ((timeOnsetSecond_continuous _).comp (continuous_const.add continuous_id)).mul
    (fullHorizonMean_continuous q branch x X k)

private theorem fullSeedTimeDensity_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k h : ℝ, 0 ≤ h →
      ‖fullSeedTimeDensity q branch v x X k h‖ ≤
        (C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|))*
          Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
  obtain ⟨B,hB,hb⟩ := onset_derivative_bound q branch
  obtain ⟨C,hC,hc⟩ := fullHorizonMean_growth q branch
  refine ⟨B*C, mul_nonneg hB hC, fun v x X k h hh => ?_⟩
  have hsecond : ‖timeOnsetSecond (2*physicalRate q branch) (v+h)‖ ≤
      B*Real.exp (-decayExponent q*(v+h)) := by
    linarith [hb (v+h), norm_nonneg (timeOnsetFirst (2*physicalRate q branch) (v+h))]
  rw [fullSeedTimeDensity, norm_mul]
  calc
    _ ≤ (B*Real.exp (-decayExponent q*(v+h)))*
        (C*Real.exp (strictGrowthExponent q*(h+|k|))) :=
      mul_le_mul hsecond (hc x h X k hh) (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (-decayExponent q*(v+h))*
          Real.exp (strictGrowthExponent q*(h+|k|)) =
          Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|)*
            Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (B*C)*(Real.exp (-decayExponent q*(v+h))*
            Real.exp (strictGrowthExponent q*(h+|k|))) := by ring
        _ = _ := by rw [he]

private theorem fullSeedTimeDensity_integrable (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    IntegrableOn (fullSeedTimeDensity q branch v x X k) (Ioi 0) := by
  obtain ⟨C,hC,hb⟩ := fullSeedTimeDensity_bound q branch
  apply (fullSeedMajorant_integrable q
    (C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|))).mono'
    (fullSeedTimeDensity_continuous q branch v x X k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact hb v x X k h hh.le

private def fullSeedTimeArm (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ), fullSeedTimeDensity q branch v x X k h

private theorem fullSeedArm_time_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    HasDerivAt (fun w => fullSeedArm q branch w x X k)
      (fullSeedTimeArm q branch v x X k) v := by
  obtain ⟨C,hC,hb⟩ := fullSeedTimeDensity_bound q branch
  let B := C*Real.exp (-decayExponent q*(v-1)+strictGrowthExponent q*|k|)
  have hn : Ioo (v-1) (v+1) ∈ 𝓝 v := Ioo_mem_nhds (by linarith) (by linarith)
  have hm (w : ℝ) : Continuous (fullSeedDensity q branch w x X k) :=
    fullSeedDensity_continuous q branch w x X k
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w h => fullSeedDensity q branch w x X k h)
    (F' := fun w h => fullSeedTimeDensity q branch w x X k h)
    (bound := fun h => B*Real.exp ((strictGrowthExponent q-decayExponent q)*h))
    hn
    (Filter.Eventually.of_forall (fun w => (hm w).aestronglyMeasurable))
    (fullSeedDensity_integrable q branch v x X k)
    (fullSeedTimeDensity_continuous q branch v x X k).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      intro w hw
      apply (hb w x X k h hh.le).trans
      dsimp only [B]
      have he : -decayExponent q*w+strictGrowthExponent q*|k| ≤
          -decayExponent q*(v-1)+strictGrowthExponent q*|k| := by
        have hd := mul_le_mul_of_nonpos_left hw.1.le
          (neg_nonpos.mpr (lt_of_le_of_lt (sourceGrowthExponent_bounds q).1
            (decayExponent_bounds q).1).le)
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC) (Real.exp_pos _).le)
    (fullSeedMajorant_integrable q B)
    (by
      filter_upwards with h
      intro w hw
      simpa only [fullSeedDensity, fullSeedTimeDensity, add_comm] using
        (HasDerivAt.comp_const_add h w
          (timeOnsetFirst_hasDerivAt (2*physicalRate q branch) (h+w))).mul_const
          (fullHorizonMean q branch x h X k))).2

/-! The literal second original-time density retains the third onset jet. -/
private def fullSeedTimeSecondDensity (q : XiZeroCopy) (branch : Bool)
    (v x X k h : ℝ) : ℂ :=
  timeOnsetThird (2*physicalRate q branch) (v+h)*fullHorizonMean q branch x h X k

private theorem fullSeedTimeSecondDensity_continuous (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) : Continuous (fullSeedTimeSecondDensity q branch v x X k) :=
  ((timeOnsetThird_continuous _).comp (continuous_const.add continuous_id)).mul
    (fullHorizonMean_continuous q branch x X k)

private theorem fullSeedTimeSecondDensity_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k h : ℝ, 0 ≤ h →
      ‖fullSeedTimeSecondDensity q branch v x X k h‖ ≤
        (C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|))*
          Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
  obtain ⟨B,hB,hb⟩ := onset_second_derivative_bound q branch
  obtain ⟨C,hC,hc⟩ := fullHorizonMean_growth q branch
  refine ⟨B*C, mul_nonneg hB hC, fun v x X k h hh => ?_⟩
  have hthird : ‖timeOnsetThird (2*physicalRate q branch) (v+h)‖ ≤
      B*Real.exp (-decayExponent q*(v+h)) := by
    linarith [hb (v+h),
      norm_nonneg (timeOnsetSecond (2*physicalRate q branch) (v+h))]
  rw [fullSeedTimeSecondDensity, norm_mul]
  calc
    _ ≤ (B*Real.exp (-decayExponent q*(v+h)))*
        (C*Real.exp (strictGrowthExponent q*(h+|k|))) :=
      mul_le_mul hthird (hc x h X k hh) (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (-decayExponent q*(v+h))*
          Real.exp (strictGrowthExponent q*(h+|k|)) =
          Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|)*
            Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (B*C)*(Real.exp (-decayExponent q*(v+h))*
            Real.exp (strictGrowthExponent q*(h+|k|))) := by ring
        _ = _ := by rw [he]

private theorem fullSeedTimeSecondDensity_integrable (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    IntegrableOn (fullSeedTimeSecondDensity q branch v x X k) (Ioi 0) := by
  obtain ⟨C,hC,hb⟩ := fullSeedTimeSecondDensity_bound q branch
  apply (fullSeedMajorant_integrable q
    (C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|))).mono'
    (fullSeedTimeSecondDensity_continuous q branch v x X k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact hb v x X k h hh.le

private def fullSeedTimeSecondArm (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ), fullSeedTimeSecondDensity q branch v x X k h

private theorem fullSeedTimeArm_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    HasDerivAt (fun w => fullSeedTimeArm q branch w x X k)
      (fullSeedTimeSecondArm q branch v x X k) v := by
  obtain ⟨C,hC,hb⟩ := fullSeedTimeSecondDensity_bound q branch
  let B := C*Real.exp (-decayExponent q*(v-1)+strictGrowthExponent q*|k|)
  have hn : Ioo (v-1) (v+1) ∈ 𝓝 v := Ioo_mem_nhds (by linarith) (by linarith)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w h => fullSeedTimeDensity q branch w x X k h)
    (F' := fun w h => fullSeedTimeSecondDensity q branch w x X k h)
    (bound := fun h => B*Real.exp ((strictGrowthExponent q-decayExponent q)*h))
    hn
    (Filter.Eventually.of_forall (fun w =>
      (fullSeedTimeDensity_continuous q branch w x X k).aestronglyMeasurable))
    (fullSeedTimeDensity_integrable q branch v x X k)
    (fullSeedTimeSecondDensity_continuous q branch v x X k).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      intro w hw
      apply (hb w x X k h hh.le).trans
      dsimp only [B]
      have he : -decayExponent q*w+strictGrowthExponent q*|k| ≤
          -decayExponent q*(v-1)+strictGrowthExponent q*|k| := by
        have hd := mul_le_mul_of_nonpos_left hw.1.le
          (neg_nonpos.mpr (lt_of_le_of_lt (sourceGrowthExponent_bounds q).1
            (decayExponent_bounds q).1).le)
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC) (Real.exp_pos _).le)
    (fullSeedMajorant_integrable q B)
    (by
      filter_upwards with h
      intro w hw
      simpa only [fullSeedTimeDensity, fullSeedTimeSecondDensity, add_comm] using
        (HasDerivAt.comp_const_add h w
          (timeOnsetSecond_hasDerivAt (2*physicalRate q branch) (h+w))).mul_const
          (fullHorizonMean q branch x h X k))).2

/-- B2 two-jet prerequisite: second original-time derivative of the actual
full seed arm, retaining the full response-plus-square angular coefficient. -/
theorem fullSeedArm_time_second_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    HasDerivAt (fun w => deriv (fun z => fullSeedArm q branch z x X k) w)
      (fullSeedTimeSecondArm q branch v x X k) v := by
  have hfun : (fun w => deriv (fun z => fullSeedArm q branch z x X k) w) =
      fun w => fullSeedTimeArm q branch w x X k := by
    funext w
    exact (fullSeedArm_time_hasDerivAt q branch w x X k).deriv
  rw [hfun]
  exact fullSeedTimeArm_hasDerivAt q branch v x X k

private theorem setIntegral_comp_add_right (f : ℝ → ℂ) (v : ℝ) :
    (∫ h in Ioi (0 : ℝ), f (h+v)) = ∫ u in Ioi v, f u := by
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun u : ℝ => (Ioi v).indicator f u) v]
  refine integral_congr_ae ?_
  filter_upwards with h
  simp only [Set.indicator_apply, Set.mem_Ioi]
  by_cases hh : (0 : ℝ) < h
  · rw [if_pos hh, if_pos (by linarith)]
  · rw [if_neg hh, if_neg (by linarith)]

private theorem onsetFirst_zero_nonpos (s : ℂ) (u : ℝ) (hu : u ≤ 0) :
    timeOnsetFirst s u = 0 := by
  have hm : IsLocalMin Real.smoothTransition u := by
    apply Filter.Eventually.of_forall
    intro t
    simpa only [Real.smoothTransition.zero_of_nonpos hu] using
      Real.smoothTransition.nonneg t
  simp only [timeOnsetFirst, hm.deriv_eq_zero, Real.smoothTransition.zero_of_nonpos hu,
    Complex.ofReal_zero, mul_zero, zero_add, zero_mul]

private theorem fullSeedArm_eq_original_arm (q : XiZeroCopy) (branch : Bool)
    (tau x X k : ℝ) :
    fullSeedArm q branch (tau+x) x X k =
      ∫ u in Ioi (0 : ℝ), timeOnsetFirst (2*physicalRate q branch) u*
        D4BMFutureSeedHorizon.halfKernel q branch tau x u X k := by
  let F : ℝ → ℂ := fun u => timeOnsetFirst (2*physicalRate q branch) u*
    D4BMFutureSeedHorizon.halfKernel q branch tau x u X k
  have hshift := setIntegral_comp_add_right F (tau+x)
  have hdelay : (∫ h in Ioi (0 : ℝ), F (h+(tau+x))) =
      fullSeedArm q branch (tau+x) x X k := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro h hh
    dsimp only [F]
    rw [show h+(tau+x) = tau+x+h by ring,
      D4BMFutureSeedHorizon.halfKernel_at_delay q branch tau x h X k hh.le]
    simp only [fullSeedArm, fullSeedDensity, fullHorizonMean, capScale]
  rw [hdelay] at hshift
  rw [← hshift]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
    ← MeasureTheory.integral_indicator measurableSet_Ioi]
  refine integral_congr_ae ?_
  filter_upwards with u
  simp only [Set.indicator_apply, Set.mem_Ioi]
  by_cases hv : 0 ≤ tau+x
  · by_cases hu : tau+x < u
    · rw [if_pos hu, if_pos (by linarith)]
    · have hzero : F u = 0 := by
        dsimp only [F, D4BMFutureSeedHorizon.halfKernel]
        rw [if_neg (by linarith)]
        ring
      rw [if_neg hu, if_pos (by linarith), hzero]
  · by_cases hu : (0 : ℝ) < u
    · rw [if_pos hu, if_pos (by linarith)]
    · have hzero : F u = 0 := by
        dsimp only [F]
        rw [onsetFirst_zero_nonpos _ u (by linarith)]
        ring
      rw [if_neg hu, if_pos (by linarith), hzero]

/-- Exact two-arm realization of the specified seed cap.  This is the bridge
from its original causal definition to the literal delay arms differentiated
above; no source-cap arm is substituted. -/
theorem seedCapField_eq_fullSeedArms (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (tau x X k : ℝ) :
    D4BMFutureSeedHorizon.seedCapField q branch amp tau x X k =
      -D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
        (fullSeedArm q branch (tau+x) x X k-
          fullSeedArm q branch (tau-x) (-x) X k) := by
  have h := D4BMFutureSeedHorizon.seedCapField_arms q branch amp tau x X k
  change D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
      (∫ u in Ioi (0 : ℝ), timeOnsetFirst (2*physicalRate q branch) u*
        D4BMFutureSeedHorizon.halfKernel q branch tau x u X k)-
      D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
        (∫ u in Ioi (0 : ℝ), timeOnsetFirst (2*physicalRate q branch) u*
          D4BMFutureSeedHorizon.halfKernel q branch tau (-x) u X k) =
        -D4BMFutureSeedHorizon.seedCapField q branch amp tau x X k at h
  rw [← fullSeedArm_eq_original_arm q branch tau x X k,
    ← fullSeedArm_eq_original_arm q branch tau (-x) X k] at h
  have h' := congrArg Neg.neg h
  simp only [neg_neg] at h'
  rw [← h']
  ring

/-- Normal trace of the direct literal seed arm.  The coefficient is the
full Goursat response-plus-square coefficient, not the source-cap contact. -/
theorem fullSeedArm_normal_div_scale_ingoing (q : XiZeroCopy) (branch : Bool)
    (v X k : ℝ) :
    Tendsto (fun x => deriv (fun y => fullSeedArm q branch v y X k) x/
      (capScale x : ℂ)) atBot
      (𝓝 ((-2 : ℂ)*(parameter q branch*
        (fullAngularField q branch ![X, Real.exp k]+
          fullSquarePotential q ![X, Real.exp k])/2)*sourceMemory q branch v)) := by
  have hc : Tendsto (fun x => -((2-capScale x : ℝ) : ℂ)) atBot (𝓝 (-2 : ℂ)) := by
    have hs : Tendsto (fun x => 2-capScale x) atBot (𝓝 (2 : ℝ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (2 : ℝ))).sub scale_limit
    simpa only [Complex.ofReal_ofNat, Function.comp_def] using!
      ((Complex.continuous_ofReal.tendsto (2 : ℝ)).comp hs).neg
  have ht := hc.mul (fullNormalArm_div_scale_ingoing q branch v X k)
  have he (x : ℝ) : deriv (fun y => fullSeedArm q branch v y X k) x/
      (capScale x : ℂ) =
      -((2-capScale x : ℝ) : ℂ)*
        (fullNormalArm q branch v x X k/(capScale x : ℂ)) := by
    rw [(fullSeedArm_normal_hasDerivAt q branch v x X k).deriv]
    field_simp [Complex.ofReal_ne_zero.mpr (scale_pos x).ne']
  simpa only [he, mul_assoc] using ht

private theorem fullHorizonMean_normal_continuous (q : XiZeroCopy) (branch : Bool)
    (h X k : ℝ) : Continuous (fun x => fullHorizonMean q branch x h X k) := by
  apply (angularMean_smooth q branch X k).continuous.comp
  have hs : Continuous capScale := continuous_iff_continuousAt.mpr
    (fun x => (scale_derivative x).continuousAt)
  apply Real.continuousOn_arcosh.comp_continuous
  · exact continuous_const.max
      (continuous_const.add (hs.mul continuous_const))
  · intro z
    exact le_max_left _ _

private theorem fullSeedDensity_joint_continuous (q : XiZeroCopy) (branch : Bool)
    (X k h : ℝ) :
    Continuous (fun p : ℝ × ℝ => fullSeedDensity q branch p.1 p.2 X k h) := by
  have ht : Continuous (fun p : ℝ × ℝ => timeOnsetFirst (2*physicalRate q branch)
      (p.1+h)) := (continuous_iff_continuousAt.mpr
        (fun u => (timeOnsetFirst_hasDerivAt _ u).continuousAt)).comp
          (continuous_fst.add continuous_const)
  have hm : Continuous (fun p : ℝ × ℝ => fullHorizonMean q branch p.2 h X k) :=
    (fullHorizonMean_normal_continuous q branch h X k).comp continuous_snd
  exact ht.mul hm

private theorem fullSeedTimeDensity_joint_continuous (q : XiZeroCopy) (branch : Bool)
    (X k h : ℝ) :
    Continuous (fun p : ℝ × ℝ => fullSeedTimeDensity q branch p.1 p.2 X k h) := by
  have ht : Continuous (fun p : ℝ × ℝ => timeOnsetSecond (2*physicalRate q branch)
      (p.1+h)) := (timeOnsetSecond_continuous _).comp (continuous_fst.add continuous_const)
  have hm : Continuous (fun p : ℝ × ℝ => fullHorizonMean q branch p.2 h X k) :=
    (fullHorizonMean_normal_continuous q branch h X k).comp continuous_snd
  exact ht.mul hm

private theorem fullSeedArm_joint_continuous (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    Continuous (fun p : ℝ × ℝ => fullSeedArm q branch p.1 p.2 X k) := by
  obtain ⟨C,hC,hb⟩ := fullSeedDensity_bound q branch
  apply continuous_iff_continuousAt.mpr
  intro p
  let B := C*Real.exp (-decayExponent q*(p.1-1)+strictGrowthExponent q*|k|)
  apply continuousAt_of_dominated (μ := volume.restrict (Ioi (0 : ℝ)))
    (bound := fun h => B*Real.exp ((strictGrowthExponent q-decayExponent q)*h))
  · exact Eventually.of_forall (fun z =>
      (fullSeedDensity_continuous q branch z.1 z.2 X k).aestronglyMeasurable)
  · have hn : ∀ᶠ z : ℝ × ℝ in 𝓝 p, p.1-1 < z.1 :=
      continuous_fst.continuousAt.eventually (Ioi_mem_nhds (by linarith : p.1-1 < p.1))
    filter_upwards [hn] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    apply (hb z.1 z.2 X k h hh.le).trans
    have he : Real.exp (-decayExponent q*z.1+strictGrowthExponent q*|k|) ≤
        Real.exp (-decayExponent q*(p.1-1)+strictGrowthExponent q*|k|) := by
      apply Real.exp_le_exp.mpr
      have hd := mul_le_mul_of_nonpos_left hz.le
        (neg_nonpos.mpr (lt_of_le_of_lt (sourceGrowthExponent_bounds q).1
          (decayExponent_bounds q).1).le)
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he hC) (Real.exp_pos _).le
  · exact fullSeedMajorant_integrable q B
  · exact Eventually.of_forall (fun h =>
      (fullSeedDensity_joint_continuous q branch X k h).continuousAt)

private theorem fullSeedTimeArm_joint_continuous (q : XiZeroCopy) (branch : Bool)
    (X k : ℝ) : Continuous (fun p : ℝ × ℝ => fullSeedTimeArm q branch p.1 p.2 X k) := by
  obtain ⟨C,hC,hb⟩ := fullSeedTimeDensity_bound q branch
  apply continuous_iff_continuousAt.mpr
  intro p
  let B := C*Real.exp (-decayExponent q*(p.1-1)+strictGrowthExponent q*|k|)
  apply continuousAt_of_dominated (μ := volume.restrict (Ioi (0 : ℝ)))
    (bound := fun h => B*Real.exp ((strictGrowthExponent q-decayExponent q)*h))
  · exact Eventually.of_forall (fun z =>
      (fullSeedTimeDensity_continuous q branch z.1 z.2 X k).aestronglyMeasurable)
  · have hn : ∀ᶠ z : ℝ × ℝ in 𝓝 p, p.1-1 < z.1 :=
      continuous_fst.continuousAt.eventually (Ioi_mem_nhds (by linarith : p.1-1 < p.1))
    filter_upwards [hn] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    apply (hb z.1 z.2 X k h hh.le).trans
    have he : Real.exp (-decayExponent q*z.1+strictGrowthExponent q*|k|) ≤
        Real.exp (-decayExponent q*(p.1-1)+strictGrowthExponent q*|k|) := by
      apply Real.exp_le_exp.mpr
      have hd := mul_le_mul_of_nonpos_left hz.le
        (neg_nonpos.mpr (lt_of_le_of_lt (sourceGrowthExponent_bounds q).1
          (decayExponent_bounds q).1).le)
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he hC) (Real.exp_pos _).le
  · exact fullSeedMajorant_integrable q B
  · exact Eventually.of_forall (fun h =>
      (fullSeedTimeDensity_joint_continuous q branch X k h).continuousAt)

private def fullSeedNormalDensity (q : XiZeroCopy) (branch : Bool)
    (v x X k h : ℝ) : ℂ :=
  normalWeight q branch v h*fullHorizonMean q branch x h X k

private theorem fullSeedNormalDensity_continuous (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) : Continuous (fullSeedNormalDensity q branch v x X k) :=
  (normalWeight_continuous q branch v).mul (fullHorizonMean_continuous q branch x X k)

private theorem fullSeedNormalDensity_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k h : ℝ, 0 ≤ h →
      ‖fullSeedNormalDensity q branch v x X k h‖ ≤
        (C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|))*
          Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
  obtain ⟨B,hB,hb⟩ := normalWeight_bound q branch
  obtain ⟨C,hC,hc⟩ := fullHorizonMean_growth q branch
  refine ⟨B*C, mul_nonneg hB hC, fun v x X k h hh => ?_⟩
  rw [fullSeedNormalDensity, norm_mul]
  calc
    _ ≤ (B*Real.exp (-decayExponent q*(v+h)))*
        (C*Real.exp (strictGrowthExponent q*(h+|k|))) :=
      mul_le_mul (hb v h hh) (hc x h X k hh) (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (-decayExponent q*(v+h))*
          Real.exp (strictGrowthExponent q*(h+|k|)) =
          Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|)*
            Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = (B*C)*(Real.exp (-decayExponent q*(v+h))*
            Real.exp (strictGrowthExponent q*(h+|k|))) := by ring
        _ = _ := by rw [he]

private theorem fullSeedNormalDensity_joint_continuous (q : XiZeroCopy) (branch : Bool)
    (X k h : ℝ) :
    Continuous (fun p : ℝ × ℝ => fullSeedNormalDensity q branch p.1 p.2 X k h) := by
  have hn : Continuous (fun p : ℝ × ℝ => normalWeight q branch p.1 h) := by
    unfold normalWeight
    have h2 : Continuous (fun p : ℝ × ℝ => timeOnsetSecond (2*physicalRate q branch)
        (p.1+h)) := (timeOnsetSecond_continuous _).comp
          (continuous_fst.add continuous_const)
    have h1 : Continuous (fun p : ℝ × ℝ => timeOnsetFirst (2*physicalRate q branch)
        (p.1+h)) := (continuous_iff_continuousAt.mpr
          (fun u => (timeOnsetFirst_hasDerivAt _ u).continuousAt)).comp
            (continuous_fst.add continuous_const)
    exact (h2.mul
      (continuous_const.sub (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp continuous_neg)))).add
      (h1.mul (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp continuous_neg)))
  have hm : Continuous (fun p : ℝ × ℝ => fullHorizonMean q branch p.2 h X k) :=
    (fullHorizonMean_normal_continuous q branch h X k).comp continuous_snd
  exact hn.mul hm

private theorem fullNormalArm_joint_continuous (q : XiZeroCopy) (branch : Bool)
    (X k : ℝ) : Continuous (fun p : ℝ × ℝ => fullNormalArm q branch p.1 p.2 X k) := by
  obtain ⟨C,hC,hb⟩ := fullSeedNormalDensity_bound q branch
  apply continuous_iff_continuousAt.mpr
  intro p
  let B := C*Real.exp (-decayExponent q*(p.1-1)+strictGrowthExponent q*|k|)
  apply continuousAt_of_dominated (μ := volume.restrict (Ioi (0 : ℝ)))
    (bound := fun h => B*Real.exp ((strictGrowthExponent q-decayExponent q)*h))
  · exact Eventually.of_forall (fun z =>
      (fullSeedNormalDensity_continuous q branch z.1 z.2 X k).aestronglyMeasurable)
  · have hn : ∀ᶠ z : ℝ × ℝ in 𝓝 p, p.1-1 < z.1 :=
      continuous_fst.continuousAt.eventually (Ioi_mem_nhds (by linarith : p.1-1 < p.1))
    filter_upwards [hn] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    apply (hb z.1 z.2 X k h hh.le).trans
    have he : Real.exp (-decayExponent q*z.1+strictGrowthExponent q*|k|) ≤
        Real.exp (-decayExponent q*(p.1-1)+strictGrowthExponent q*|k|) := by
      apply Real.exp_le_exp.mpr
      have hd := mul_le_mul_of_nonpos_left hz.le
        (neg_nonpos.mpr (lt_of_le_of_lt (sourceGrowthExponent_bounds q).1
          (decayExponent_bounds q).1).le)
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he hC) (Real.exp_pos _).le
  · exact fullSeedMajorant_integrable q B
  · exact Eventually.of_forall (fun h =>
      (fullSeedNormalDensity_joint_continuous q branch X k h).continuousAt)

private theorem fullJoint_from_partials (f a b : ℝ → ℝ → ℂ)
    (ha : ∀ v x, HasDerivAt (fun t => f t x) (a v x) v)
    (hb : ∀ v x, HasDerivAt (fun y => f v y) (b v x) x)
    (ca : Continuous (Function.uncurry a)) (cb : Continuous (Function.uncurry b))
    (v x : ℝ) :
    HasFDerivAt (Function.uncurry f)
      ((ContinuousLinearMap.toSpanSingleton ℝ (a v x)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ (b v x))) (v,x) := by
  have d1 : ∀ᶠ p : ℝ × ℝ in 𝓝 (v,x), HasFDerivAt (fun t => f t p.2)
      (ContinuousLinearMap.toSpanSingleton ℝ (a p.1 p.2)) p.1 :=
    Eventually.of_forall (fun p => (ha p.1 p.2).hasFDerivAt)
  have d2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (v,x), HasFDerivAt (fun y => f p.1 y)
      (ContinuousLinearMap.toSpanSingleton ℝ (b p.1 p.2)) p.2 :=
    Eventually.of_forall (fun p => (hb p.1 p.2).hasFDerivAt)
  have c1 : ContinuousAt (fun p : ℝ × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
      (a p.1 p.2)) (v,x) :=
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ).continuous.comp ca).continuousAt
  have c2 : ContinuousAt (fun p : ℝ × ℝ => ContinuousLinearMap.toSpanSingleton ℝ
      (b p.1 p.2)) (v,x) :=
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ).continuous.comp cb).continuousAt
  exact (hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ) (u := (v,x)) (f := f)
    (f₁ := fun v x => ContinuousLinearMap.toSpanSingleton ℝ (a v x))
    (f₂ := fun v x => ContinuousLinearMap.toSpanSingleton ℝ (b v x))
    d1 d2 c1 c2).hasFDerivAt

private theorem fullSeedArm_joint_hasFDerivAt (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ => fullSeedArm q branch p.1 p.2 X k)
      ((ContinuousLinearMap.toSpanSingleton ℝ (fullSeedTimeArm q branch v x X k)).coprod
        (ContinuousLinearMap.toSpanSingleton ℝ
          (-((2-capScale x : ℝ) : ℂ)*fullNormalArm q branch v x X k))) (v,x) := by
  have hn : Continuous (fun p : ℝ × ℝ =>
      -((2-capScale p.2 : ℝ) : ℂ)*fullNormalArm q branch p.1 p.2 X k) := by
    have hs : Continuous capScale := continuous_iff_continuousAt.mpr
      (fun x => (scale_derivative x).continuousAt)
    exact (Complex.continuous_ofReal.comp
      (continuous_const.sub (hs.comp continuous_snd))).neg.mul
        (fullNormalArm_joint_continuous q branch X k)
  exact fullJoint_from_partials (fun v x => fullSeedArm q branch v x X k)
    (fun v x => fullSeedTimeArm q branch v x X k)
    (fun v x => -((2-capScale x : ℝ) : ℂ)*fullNormalArm q branch v x X k)
    (fun v x => fullSeedArm_time_hasDerivAt q branch v x X k)
    (fun v x => fullSeedArm_normal_hasDerivAt q branch v x X k)
    (fullSeedTimeArm_joint_continuous q branch X k) hn v x

private theorem fullSeedArm_image_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    HasDerivAt (fun y => fullSeedArm q branch (v-2*y) (-y) X k)
      (-2*fullSeedTimeArm q branch (v-2*x) (-x) X k+
        ((2-capScale (-x) : ℝ) : ℂ)*fullNormalArm q branch (v-2*x) (-x) X k) x := by
  have hp := (((hasDerivAt_id x).const_mul (2 : ℝ)).const_sub v).prodMk (hasDerivAt_neg x)
  have hd := (fullSeedArm_joint_hasFDerivAt q branch (v-2*x) (-x) X k).comp_hasDerivAt x hp
  convert! hd using 1
  simp only [ContinuousLinearMap.coprod_apply, ContinuousLinearMap.toSpanSingleton_apply,
    Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat,
    mul_one, neg_mul, mul_neg]
  ring

/-- Both literal seed arms contribute before the ingoing limit is taken. -/
theorem seedCapField_ingoing_normal_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v x X k : ℝ) :
    HasDerivAt (fun y => D4BMFutureSeedHorizon.seedCapField q branch amp (v-y) y X k)
      (-D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
        (-((2-capScale x : ℝ) : ℂ)*fullNormalArm q branch v x X k+
          2*fullSeedTimeArm q branch (v-2*x) (-x) X k-
          ((2-capScale (-x) : ℝ) : ℂ)*fullNormalArm q branch (v-2*x) (-x) X k)) x := by
  have hd := ((fullSeedArm_normal_hasDerivAt q branch v x X k).sub
    (fullSeedArm_image_hasDerivAt q branch v x X k)).const_mul
      (-D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp)
  convert! hd using 1
  · funext y
    rw [seedCapField_eq_fullSeedArms q branch amp (v-y) y X k]
    rw [show v-y+y = v by ring, show v-y-y = v-2*y by ring]
  · ring

private theorem fullSeedTimeArm_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k : ℝ,
      ‖fullSeedTimeArm q branch v x X k‖ ≤
        C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|) := by
  obtain ⟨C,hC,hb⟩ := fullSeedTimeDensity_bound q branch
  have hp : 0 < decayExponent q-strictGrowthExponent q :=
    sub_pos.mpr (strictGrowthExponent_bounds q).2
  refine ⟨C/(decayExponent q-strictGrowthExponent q), div_nonneg hC hp.le,
    fun v x X k => ?_⟩
  let D := C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|)
  have hi := fullSeedTimeDensity_integrable q branch v x X k
  calc
    _ ≤ ∫ h in Ioi (0 : ℝ), ‖fullSeedTimeDensity q branch v x X k h‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Ioi (0 : ℝ), D*Real.exp ((strictGrowthExponent q-decayExponent q)*h) :=
      setIntegral_mono_on hi.norm (fullSeedMajorant_integrable q D) measurableSet_Ioi
        (fun h hh => hb v x X k h hh.le)
    _ = _ := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (by linarith : strictGrowthExponent q-decayExponent q < 0)]
      simp only [mul_zero, Real.exp_zero]
      dsimp only [D]
      rw [show strictGrowthExponent q-decayExponent q =
        -(decayExponent q-strictGrowthExponent q) by ring]
      simp only [neg_div_neg_eq]
      ring

private theorem fullSeedNormalDensity_integrable (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    IntegrableOn (fullSeedNormalDensity q branch v x X k) (Ioi 0) := by
  obtain ⟨C,hC,hb⟩ := fullSeedNormalDensity_bound q branch
  apply (fullSeedMajorant_integrable q
    (C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|))).mono'
    (fullSeedNormalDensity_continuous q branch v x X k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact hb v x X k h hh.le

/-! Time derivative of the literal transported normal weight. -/
private def normalTimeWeight (q : XiZeroCopy) (branch : Bool) (v h : ℝ) : ℂ :=
  timeOnsetThird (2*physicalRate q branch) (v+h)*(1-(Real.exp (-h) : ℂ))+
    timeOnsetSecond (2*physicalRate q branch) (v+h)*(Real.exp (-h) : ℂ)

private theorem normalTimeWeight_continuous (q : XiZeroCopy) (branch : Bool)
    (v : ℝ) : Continuous (normalTimeWeight q branch v) := by
  have h3 := timeOnsetThird_continuous (2*physicalRate q branch)
  have h2 := timeOnsetSecond_continuous (2*physicalRate q branch)
  exact ((h3.comp (continuous_const.add continuous_id)).mul
    (continuous_const.sub (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp continuous_neg)))).add
    ((h2.comp (continuous_const.add continuous_id)).mul
      (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)))

private theorem normalWeight_time_derivative (q : XiZeroCopy) (branch : Bool)
    (v h : ℝ) :
    HasDerivAt (fun w => normalWeight q branch w h)
      (normalTimeWeight q branch v h) v := by
  have h2 := (timeOnsetSecond_hasDerivAt (2*physicalRate q branch) (v+h)).scomp v
    (hasDerivAt_id v |>.add_const h)
  have h1 := (timeOnsetFirst_hasDerivAt (2*physicalRate q branch) (v+h)).scomp v
    (hasDerivAt_id v |>.add_const h)
  convert! h2.mul_const (1-(Real.exp (-h) : ℂ)) |>.add
    (h1.mul_const (Real.exp (-h) : ℂ)) using 1
  simp only [normalWeight, normalTimeWeight, Complex.real_smul, Function.comp_apply]
  ring

private theorem normalTimeWeight_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v h : ℝ, 0 ≤ h →
      ‖normalTimeWeight q branch v h‖ ≤ B*Real.exp (-decayExponent q*(v+h)) := by
  obtain ⟨B,hB,hb⟩ := onset_second_derivative_bound q branch
  refine ⟨B,hB,fun v h hh => ?_⟩
  have he : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have he1 : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold normalTimeWeight
  apply (norm_add_le _ _).trans
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
  rw [show (1 : ℂ)-(Real.exp (-h) : ℂ) = ((1-Real.exp (-h) : ℝ) : ℂ) by
    push_cast; rfl]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr he1)]
  have h2 := norm_nonneg (timeOnsetSecond (2*physicalRate q branch) (v+h))
  have h3 := norm_nonneg (timeOnsetThird (2*physicalRate q branch) (v+h))
  nlinarith [hb (v+h)]

private def fullNormalTimeDensity (q : XiZeroCopy) (branch : Bool)
    (v x X k h : ℝ) : ℂ :=
  normalTimeWeight q branch v h*fullHorizonMean q branch x h X k

private theorem fullNormalTimeDensity_continuous (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) : Continuous (fullNormalTimeDensity q branch v x X k) :=
  (normalTimeWeight_continuous q branch v).mul
    (fullHorizonMean_continuous q branch x X k)

private theorem fullNormalTimeDensity_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k h : ℝ, 0 ≤ h →
      ‖fullNormalTimeDensity q branch v x X k h‖ ≤
        (C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|))*
          Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
  obtain ⟨B,hB,hb⟩ := normalTimeWeight_bound q branch
  obtain ⟨C,hC,hc⟩ := fullHorizonMean_growth q branch
  refine ⟨B*C,mul_nonneg hB hC,fun v x X k h hh => ?_⟩
  rw [fullNormalTimeDensity,norm_mul]
  calc
    _ ≤ (B*Real.exp (-decayExponent q*(v+h)))*
        (C*Real.exp (strictGrowthExponent q*(h+|k|))) :=
      mul_le_mul (hb v h hh) (hc x h X k hh) (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (-decayExponent q*(v+h))*
          Real.exp (strictGrowthExponent q*(h+|k|)) =
          Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|)*
            Real.exp ((strictGrowthExponent q-decayExponent q)*h) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      calc
        _ = (B*C)*(Real.exp (-decayExponent q*(v+h))*
            Real.exp (strictGrowthExponent q*(h+|k|))) := by ring
        _ = _ := by rw [he]

private theorem fullNormalTimeDensity_integrable (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    IntegrableOn (fullNormalTimeDensity q branch v x X k) (Ioi 0) := by
  obtain ⟨C,hC,hb⟩ := fullNormalTimeDensity_bound q branch
  apply (fullSeedMajorant_integrable q
    (C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|))).mono'
    (fullNormalTimeDensity_continuous q branch v x X k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact hb v x X k h hh.le

private def fullNormalTimeArm (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ), fullNormalTimeDensity q branch v x X k h

private theorem fullNormalArm_time_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    HasDerivAt (fun w => fullNormalArm q branch w x X k)
      (fullNormalTimeArm q branch v x X k) v := by
  obtain ⟨C,hC,hb⟩ := fullNormalTimeDensity_bound q branch
  let B := C*Real.exp (-decayExponent q*(v-1)+strictGrowthExponent q*|k|)
  have hn : Ioo (v-1) (v+1) ∈ 𝓝 v := Ioo_mem_nhds (by linarith) (by linarith)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun w h => normalWeight q branch w h*fullHorizonMean q branch x h X k)
    (F' := fun w h => fullNormalTimeDensity q branch w x X k h)
    (bound := fun h => B*Real.exp ((strictGrowthExponent q-decayExponent q)*h))
    hn
    (Filter.Eventually.of_forall (fun w =>
      (fullSeedNormalDensity_continuous q branch w x X k).aestronglyMeasurable))
    (fullSeedNormalDensity_integrable q branch v x X k)
    (fullNormalTimeDensity_continuous q branch v x X k).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      intro w hw
      apply (hb w x X k h hh.le).trans
      dsimp only [B]
      have he : -decayExponent q*w+strictGrowthExponent q*|k| ≤
          -decayExponent q*(v-1)+strictGrowthExponent q*|k| := by
        have hd := mul_le_mul_of_nonpos_left hw.1.le
          (neg_nonpos.mpr (lt_of_le_of_lt (sourceGrowthExponent_bounds q).1
            (decayExponent_bounds q).1).le)
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC) (Real.exp_pos _).le)
    (fullSeedMajorant_integrable q B)
    (by
      filter_upwards with h
      intro w hw
      simpa only [fullNormalTimeDensity] using
        (normalWeight_time_derivative q branch w h).mul_const
          (fullHorizonMean q branch x h X k))).2

/-- B2 two-jet prerequisite: time derivative of the literal normal derivative
of the full seed arm. -/
theorem fullSeedArm_time_normal_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    HasDerivAt (fun w => deriv (fun y => fullSeedArm q branch w y X k) x)
      (-((2-capScale x : ℝ) : ℂ)*fullNormalTimeArm q branch v x X k) v := by
  have hfun : (fun w => deriv (fun y => fullSeedArm q branch w y X k) x) =
      fun w => -((2-capScale x : ℝ) : ℂ)*fullNormalArm q branch w x X k := by
    funext w
    exact (fullSeedArm_normal_hasDerivAt q branch w x X k).deriv
  rw [hfun]
  convert! (fullNormalArm_time_hasDerivAt q branch v x X k).const_mul
    (-((2-capScale x : ℝ) : ℂ)) using 1
  ring

/-! The second literal normal density.  It is obtained by evaluating the
second transported delay derivative at its physical base scale. -/
private def fullSecondNormalDensity (q : XiZeroCopy) (branch : Bool)
    (v x X k h : ℝ) : ℂ :=
  (timeOnsetThird (2*physicalRate q branch) (v+h)*
      ((Real.exp (-h)-1 : ℝ) : ℂ)^2+
    timeOnsetSecond (2*physicalRate q branch) (v+h)*
      ((1-Real.exp (-2*h) : ℝ) : ℂ)+
    2*timeOnsetSecond (2*physicalRate q branch) (v+h)*
      ((Real.exp (-h)-1 : ℝ) : ℂ)*(-Real.exp (-h) : ℂ)+
    timeOnsetFirst (2*physicalRate q branch) (v+h)*
      ((2*Real.exp (-2*h) : ℝ) : ℂ))*fullHorizonMean q branch x h X k

private theorem fullSecondNormalDensity_continuous (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) : Continuous (fullSecondNormalDensity q branch v x X k) := by
  have h1 : Continuous (fun h : ℝ => timeOnsetFirst (2*physicalRate q branch) (v+h)) :=
    (continuous_iff_continuousAt.mpr
      (fun u => (timeOnsetFirst_hasDerivAt _ u).continuousAt)).comp
        (continuous_const.add continuous_id)
  have h2 : Continuous (fun h : ℝ => timeOnsetSecond (2*physicalRate q branch) (v+h)) :=
    (timeOnsetSecond_continuous _).comp (continuous_const.add continuous_id)
  have h3 : Continuous (fun h : ℝ => timeOnsetThird (2*physicalRate q branch) (v+h)) :=
    (timeOnsetThird_continuous _).comp (continuous_const.add continuous_id)
  have e1 : Continuous (fun h : ℝ => ((Real.exp (-h)-1 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp
      ((Real.continuous_exp.comp continuous_neg).sub continuous_const))
  have e2 : Continuous (fun h : ℝ => ((1-Real.exp (-2*h) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_const.sub (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg)))
  have e3 : Continuous (fun h : ℝ => (-Real.exp (-h) : ℂ)) :=
    (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).neg
  have e4 : Continuous (fun h : ℝ => ((2*Real.exp (-2*h) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_exp.comp
        ((continuous_const.mul continuous_id).neg)))
  simpa only [fullSecondNormalDensity] using
    (((((h3.mul (e1.pow 2)).add (h2.mul e2)).add
      (((continuous_const.mul h2).mul e1).mul e3)).add (h1.mul e4)).mul
        (fullHorizonMean_continuous q branch x X k))

private theorem fullMovedSecondDerivative_one (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    fullMovedSecondDerivative q branch v x X k 1 =
      fullSecondNormalDensity q branch v x X k := by
  funext h
  rw [fullMovedSecondDerivative, (fullDelay_one h).1, (fullDelay_one h).2.1,
    (fullDelay_one h).2.2.1, (fullDelay_one h).2.2.2,
    (fullDelay_second_one h).1, (fullDelay_second_one h).2]
  simp only [Complex.ofReal_one, Complex.ofReal_sub, Complex.ofReal_neg,
    Complex.ofReal_ofNat, mul_one]
  ring

private def fullSecondNormalArm (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ), fullSecondNormalDensity q branch v x X k h

private theorem fullMovedIntegral_second_derivative (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    HasDerivAt (fun b => deriv (fun a => ∫ h in Ioi (0 : ℝ),
      fullMovedDensity q branch v x X k a h) b)
      (fullSecondNormalArm q branch v x X k) 1 := by
  obtain ⟨C,hC,hb⟩ := fullMovedSecondDerivative_bound q branch
  let B := C*Real.exp (-decayExponent q*(v-Real.log 2)+strictGrowthExponent q*|k|)
  have hn : Ioo (1/2 : ℝ) 2 ∈ 𝓝 (1 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hmeas : ∀ᶠ b in 𝓝 (1 : ℝ), AEStronglyMeasurable
      (fullMovedDerivative q branch v x X k b) (volume.restrict (Ioi 0)) := by
    filter_upwards [hn] with b hb
    exact fullMovedDerivative_measurable q branch v x X k b (by linarith [hb.1])
  have hi : IntegrableOn (fullMovedDerivative q branch v x X k 1) (Ioi 0) := by
    rw [fullMovedDerivative_one]
    simpa only [fullSeedNormalDensity] using
      (fullSeedNormalDensity_integrable q branch v x X k).neg
  have hm' : AEStronglyMeasurable (fullMovedSecondDerivative q branch v x X k 1)
      (volume.restrict (Ioi 0)) := by
    rw [fullMovedSecondDerivative_one]
    exact (fullSecondNormalDensity_continuous q branch v x X k).aestronglyMeasurable
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun b h => fullMovedDerivative q branch v x X k b h)
    (F' := fun b h => fullMovedSecondDerivative q branch v x X k b h)
    (bound := fun h => B*Real.exp ((strictGrowthExponent q-decayExponent q)*h))
    hn hmeas hi hm'
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      intro b hbl
      exact hb v x X k b h hbl hh.le)
    (fullSeedMajorant_integrable q B)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      intro b hbl
      exact fullMovedDerivative_derivative q branch v x X k b h
        (by linarith [hbl.1]) hh.le)).2
  have he : (fun b => deriv (fun a => ∫ h in Ioi (0 : ℝ),
      fullMovedDensity q branch v x X k a h) b) =ᶠ[𝓝 (1 : ℝ)]
      fun b => ∫ h in Ioi (0 : ℝ), fullMovedDerivative q branch v x X k b h := by
    filter_upwards [hn] with b hb
    exact (fullMovedIntegral_hasDerivAt q branch v x X k b hb).deriv
  have hh := hd.congr_of_eventuallyEq he
  simpa only [fullMovedSecondDerivative_one, fullSecondNormalArm] using hh

/-- B2 two-jet prerequisite for the literal combined-cap/current chain:
`fullSeedArm` has its actual second normal derivative.  The proof
differentiates only exact delay transport; the radial `arcosh` corner is never
differentiated.  It supplies no cap/contact holonomy identification. -/
theorem fullSeedArm_normal_second_hasDerivAt (q : XiZeroCopy) (branch : Bool)
    (v x X k : ℝ) :
    HasDerivAt (fun y => deriv (fun z => fullSeedArm q branch v z X k) y)
      (((2-capScale x : ℝ) : ℂ)^2*fullSecondNormalArm q branch v x X k-
        ((2*(2-capScale x)*(1-capScale x) : ℝ) : ℂ)*
          fullNormalArm q branch v x X k) x := by
  let I : ℝ → ℂ := fun b => ∫ h in Ioi (0 : ℝ),
    fullMovedDensity q branch v x X k b h
  let I' : ℝ → ℂ := fun b => ∫ h in Ioi (0 : ℝ),
    fullMovedDerivative q branch v x X k b h
  let g : ℝ → ℝ := fun y => capScale y/capScale x
  have hg : g x = 1 := by
    dsimp only [g]
    exact div_self (scale_pos x).ne'
  have hI' : HasDerivAt I' (fullSecondNormalArm q branch v x X k) 1 := by
    simpa only [I, I'] using fullMovedIntegral_second_derivative q branch v x X k
  have hI'one : I' 1 = -fullNormalArm q branch v x X k := by
    have hnew := (fullMovedIntegral_hasDerivAt q branch v x X k 1
      (by norm_num : (1 : ℝ) ∈ Ioo (1/2 : ℝ) 2)).deriv
    have hold := (fullMovedIntegral_derivative q branch v x X k).deriv
    simpa only [I, I'] using hnew.symm.trans hold
  have hg' : HasDerivAt g (2-capScale x) x := by
    simpa only [g] using scale_ratio_hasDerivAt x
  have hI'comp : HasDerivAt (fun y => I' (g y))
      (((2-capScale x : ℝ) : ℂ)*fullSecondNormalArm q branch v x X k) x := by
    have h := hI'.scomp x hg'
    convert! h using 1
    simp only [Complex.real_smul]
    ring
  have hgg' : HasDerivAt (fun y => (deriv g y : ℂ))
      ((2*(2-capScale x)*(1-capScale x) : ℝ) : ℂ) x := by
    simpa only [g] using (scale_ratio_derivative_hasDerivAt x).ofReal_comp
  have hproduct := hI'comp.mul hgg'
  have hproduct' : HasDerivAt (fun y => I' (g y)*(deriv g y : ℂ))
      (((2-capScale x : ℝ) : ℂ)^2*fullSecondNormalArm q branch v x X k-
        ((2*(2-capScale x)*(1-capScale x) : ℝ) : ℂ)*
          fullNormalArm q branch v x X k) x := by
    convert! hproduct using 1
    · rw [hg, hI'one]
      simp only [Complex.real_smul]
      ring
  have hgt : Tendsto g (𝓝 x) (𝓝 (1 : ℝ)) := by
    have hc : ContinuousAt g x := by
      simpa only [g] using hg'.continuousAt
    rw [hg] at hc
    exact hc.tendsto
  have hgin : ∀ᶠ y in 𝓝 x, g y ∈ Ioo (1/2 : ℝ) 2 :=
    hgt.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  have hderiv : (fun y => deriv (fun z => I (g z)) y) =ᶠ[𝓝 x]
      fun y => I' (g y)*(deriv g y : ℂ) := by
    filter_upwards [hgin] with y hy
    have hcomp := (fullMovedIntegral_hasDerivAt q branch v x X k (g y) hy).scomp y
      (scale_ratio_base_hasDerivAt x y)
    have hbase := scale_ratio_base_hasDerivAt x y
    rw [hbase.deriv]
    convert! hcomp.deriv using 1
    simp only [I, I', Complex.real_smul]
    ring
  have hsecond := hproduct'.congr_of_eventuallyEq hderiv
  have hseed : (fun y => deriv (fun z => fullSeedArm q branch v z X k) y) =
      fun y => deriv (fun z => I (g z)) y := by
    funext y
    congr 1
    funext z
    exact fullSeedArm_moved q branch v z x X k
  rw [hseed]
  exact hsecond

private theorem fullNormalArm_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k : ℝ,
      ‖fullNormalArm q branch v x X k‖ ≤
        C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|) := by
  obtain ⟨C,hC,hb⟩ := fullSeedNormalDensity_bound q branch
  have hp : 0 < decayExponent q-strictGrowthExponent q :=
    sub_pos.mpr (strictGrowthExponent_bounds q).2
  refine ⟨C/(decayExponent q-strictGrowthExponent q), div_nonneg hC hp.le,
    fun v x X k => ?_⟩
  let D := C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|)
  have hi := fullSeedNormalDensity_integrable q branch v x X k
  calc
    _ ≤ ∫ h in Ioi (0 : ℝ), ‖fullSeedNormalDensity q branch v x X k h‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ h in Ioi (0 : ℝ), D*Real.exp ((strictGrowthExponent q-decayExponent q)*h) :=
      setIntegral_mono_on hi.norm (fullSeedMajorant_integrable q D) measurableSet_Ioi
        (fun h hh => hb v x X k h hh.le)
    _ = _ := by
      rw [integral_const_mul,
        integral_exp_mul_Ioi (by linarith : strictGrowthExponent q-decayExponent q < 0)]
      simp only [mul_zero, Real.exp_zero]
      dsimp only [D]
      rw [show strictGrowthExponent q-decayExponent q =
        -(decayExponent q-strictGrowthExponent q) by ring]
      simp only [neg_div_neg_eq]
      ring

private theorem image_exponential_over_scale (q : XiZeroCopy) (x : ℝ) :
    Real.exp ((2*decayExponent q)*x)/capScale x =
      (Real.exp ((2*decayExponent q)*x)+
        Real.exp ((2*decayExponent q-2)*x))/2 := by
  have he : Real.exp ((2*decayExponent q)*x)*Real.exp (-x)/Real.exp x =
      Real.exp ((2*decayExponent q-2)*x) := by
    rw [← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [capScale, div_div_eq_mul_div, Real.cosh_eq]
  rw [show Real.exp ((2*decayExponent q)*x)*
      ((Real.exp x+Real.exp (-x))/2)/Real.exp x =
      (Real.exp ((2*decayExponent q)*x)+
        Real.exp ((2*decayExponent q)*x)*Real.exp (-x)/Real.exp x)/2 by
        field_simp [(Real.exp_pos x).ne']]
  rw [he]

private theorem scale_complement (x : ℝ) : 2-capScale (-x) = capScale x := by
  unfold capScale
  rw [Real.cosh_neg, Real.cosh_eq]
  field_simp
  ring

private theorem image_div_scale_ingoing_of_bound (q : XiZeroCopy) (branch : Bool)
    (arm : ℝ → ℝ → ℝ → ℝ → ℂ)
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k : ℝ,
      ‖arm v x X k‖ ≤ C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|))
    (v X k : ℝ) :
    Tendsto (fun x => arm (v-2*x) (-x) X k/(capScale x : ℂ)) atBot (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := hbound
  have hd : 1 < decayExponent q := by
    linarith [(sourceGrowthExponent_bounds q).1, (decayExponent_bounds q).1]
  have h0 := Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_pos (by linarith : 0 < 2*decayExponent q)).mpr tendsto_id)
  have h1 := Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_pos (by linarith : 0 < 2*decayExponent q-2)).mpr tendsto_id)
  let D := C*Real.exp (-decayExponent q*v+strictGrowthExponent q*|k|)
  have hbnd (x : ℝ) : ‖arm (v-2*x) (-x) X k/(capScale x : ℂ)‖ ≤
      D*((Real.exp ((2*decayExponent q)*x)+
        Real.exp ((2*decayExponent q-2)*x))/2) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (scale_pos x)]
    have hb' := hb (v-2*x) (-x) X k
    rw [show -decayExponent q*(v-2*x)+strictGrowthExponent q*|k| =
      (-decayExponent q*v+strictGrowthExponent q*|k|)+(2*decayExponent q)*x by ring,
      Real.exp_add] at hb'
    calc
      _ ≤ D*Real.exp ((2*decayExponent q)*x)/capScale x :=
        div_le_div_of_nonneg_right (by simpa only [D,mul_assoc] using hb') (scale_pos x).le
      _ = _ := by rw [mul_div_assoc, image_exponential_over_scale]
  apply squeeze_zero_norm hbnd
  simpa only [Function.comp_def, id_eq, zero_add, zero_div, mul_zero] using
    ((h0.add h1).div_const 2).const_mul D

private theorem fullSeedTimeArm_image_div_scale_ingoing (q : XiZeroCopy) (branch : Bool)
    (v X k : ℝ) :
    Tendsto (fun x => fullSeedTimeArm q branch (v-2*x) (-x) X k/
      (capScale x : ℂ)) atBot (𝓝 0) :=
  image_div_scale_ingoing_of_bound q branch
    (fun v x X k => fullSeedTimeArm q branch v x X k)
    (fullSeedTimeArm_bound q branch) v X k

private theorem fullNormalArm_image_div_scale_ingoing (q : XiZeroCopy) (branch : Bool)
    (v X k : ℝ) :
    Tendsto (fun x => fullNormalArm q branch (v-2*x) (-x) X k/
      (capScale x : ℂ)) atBot (𝓝 0) :=
  image_div_scale_ingoing_of_bound q branch
    (fun v x X k => fullNormalArm q branch v x X k)
    (fullNormalArm_bound q branch) v X k

private theorem fullSeedArm_image_deriv_div_scale_ingoing (q : XiZeroCopy) (branch : Bool)
    (v X k : ℝ) :
    Tendsto (fun x => deriv (fun y => fullSeedArm q branch (v-2*y) (-y) X k) x/
      (capScale x : ℂ)) atBot (𝓝 0) := by
  have htime := (fullSeedTimeArm_image_div_scale_ingoing q branch v X k).const_mul (-2 : ℂ)
  have hc : Tendsto (fun x => ((2-capScale (-x) : ℝ) : ℂ)) atBot (𝓝 0) := by
    rw [show (fun x : ℝ => ((2-capScale (-x) : ℝ) : ℂ)) =
      fun x => (capScale x : ℂ) by funext x; rw [scale_complement]]
    simpa only [Function.comp_def] using
      (Complex.continuous_ofReal.tendsto 0).comp scale_limit
  have hnormal := hc.mul (fullNormalArm_image_div_scale_ingoing q branch v X k)
  have he (x : ℝ) : deriv (fun y => fullSeedArm q branch (v-2*y) (-y) X k) x/
      (capScale x : ℂ) =
      (-2 : ℂ)*(fullSeedTimeArm q branch (v-2*x) (-x) X k/(capScale x : ℂ))+
        ((2-capScale (-x) : ℝ) : ℂ)*
          (fullNormalArm q branch (v-2*x) (-x) X k/(capScale x : ℂ)) := by
    rw [(fullSeedArm_image_hasDerivAt q branch v x X k).deriv]
    field_simp [Complex.ofReal_ne_zero.mpr (scale_pos x).ne']
  simpa only [he, mul_zero, zero_add] using htime.add hnormal

/-- The literal two-arm seed cap has its complete physical normal trace.  This
is the full-seed contribution required by the combined cyclic Peierls cap;
the remaining comparison is against the source cap and left-QNM contact. -/
theorem seedCapField_ingoing_normal_div_scale (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v X k : ℝ) :
    Tendsto (fun x => deriv (fun y => D4BMFutureSeedHorizon.seedCapField q branch amp
      (v-y) y X k) x/(capScale x : ℂ)) atBot
      (𝓝 (2*D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
        (parameter q branch*(fullAngularField q branch ![X, Real.exp k]+
          fullSquarePotential q ![X, Real.exp k])/2)*sourceMemory q branch v)) := by
  have hdirect := (fullSeedArm_normal_div_scale_ingoing q branch v X k).const_mul
    (-D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp)
  have himage := (fullSeedArm_image_deriv_div_scale_ingoing q branch v X k).const_mul
    (D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp)
  have he (x : ℝ) : deriv (fun y => D4BMFutureSeedHorizon.seedCapField q branch amp
      (v-y) y X k) x/(capScale x : ℂ) =
      -D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
        (deriv (fun y => fullSeedArm q branch v y X k) x/(capScale x : ℂ))+
      D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
        (deriv (fun y => fullSeedArm q branch (v-2*y) (-y) X k) x/
          (capScale x : ℂ)) := by
    rw [(seedCapField_ingoing_normal_hasDerivAt q branch amp v x X k).deriv]
    field_simp [Complex.ofReal_ne_zero.mpr (scale_pos x).ne']
    ring
  rw [show (2 : ℂ)*D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
      (parameter q branch*(fullAngularField q branch ![X, Real.exp k]+
        fullSquarePotential q ![X, Real.exp k])/2)*sourceMemory q branch v =
      -D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
        ((-2 : ℂ)*(parameter q branch*(fullAngularField q branch ![X, Real.exp k]+
          fullSquarePotential q ![X, Real.exp k])/2)*sourceMemory q branch v)+
      D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*0 by ring]
  simpa only [he, mul_zero, add_zero] using hdirect.add himage

private theorem sourceCap_ingoing_normal_div_scale (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v X k : ℝ) :
    Tendsto (fun x => deriv (fun y => D4BMFutureHorizon.capBoundaryField q branch amp
      (v-y) y X k) x/(capScale x : ℂ)) atBot
      (𝓝 (D4BMFutureHorizon.liftTraceCoefficient q branch amp*
        D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]*
          sourceMemory q branch v)) := by
  have ht := ((D4BMCapRadialMemory.boundaryArm_scaled_normal_ingoing q branch v X k).sub
    (D4BMCapNormalTrace.boundaryArm_image_div_scale_ingoing q branch v X k)).const_mul
      (-D4BMFutureHorizon.liftTraceCoefficient q branch amp)
  have he (x : ℝ) : deriv (fun y => D4BMFutureHorizon.capBoundaryField q branch amp
      (v-y) y X k) x/(capScale x : ℂ) =
      -D4BMFutureHorizon.liftTraceCoefficient q branch amp*
        (deriv (fun y => D4BMFutureHorizon.boundaryArm q branch v y X k) x/
          (capScale x : ℂ)-
          deriv (fun y => D4BMFutureHorizon.boundaryArm q branch (v-2*y) (-y) X k) x/
            (capScale x : ℂ)) := by
    rw [(D4BMCapNormalTrace.capBoundaryField_ingoing_normal_hasDerivAt q branch amp
      v x X k).deriv,
      (D4BMCapNormalTrace.boundaryArm_normal_hasDerivAt q branch v x X k).deriv,
      (D4BMCapNormalTrace.boundaryArm_image_hasDerivAt q branch v x X k).deriv]
    ring
  simpa only [he, sub_zero, neg_mul, mul_neg, neg_neg, mul_assoc] using ht

/-- The actual combined cyclic Peierls cap has one explicit, unrenormalized
physical normal coefficient.  Its equality or inequality with the left-QNM
contact is now the remaining HB-B2 decision point. -/
theorem combinedCap_ingoing_normal_div_scale (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v X k : ℝ) :
    Tendsto (fun x => deriv (fun y =>
      D4BMFutureSeedHorizon.seedCapField q branch amp (v-y) y X k-
        parameter q branch*D4BMFutureHorizon.capBoundaryField q branch amp (v-y) y X k) x/
        (capScale x : ℂ)) atBot
      (𝓝 ((2*D4BMFutureSeedHorizon.seedTraceCoefficient q branch amp*
        (parameter q branch*(fullAngularField q branch ![X,Real.exp k]+
          fullSquarePotential q ![X,Real.exp k])/2)*sourceMemory q branch v)-
        parameter q branch*(D4BMFutureHorizon.liftTraceCoefficient q branch amp*
          D4BMHorizon.scalarLaplacian (fullSquarePotential q) ![X,Real.exp k]*
            sourceMemory q branch v))) := by
  have hs := seedCapField_ingoing_normal_div_scale q branch amp v X k
  have hc := (sourceCap_ingoing_normal_div_scale q branch amp v X k).const_mul
    (parameter q branch)
  have he (x : ℝ) : deriv (fun y =>
      D4BMFutureSeedHorizon.seedCapField q branch amp (v-y) y X k-
        parameter q branch*D4BMFutureHorizon.capBoundaryField q branch amp (v-y) y X k) x/
        (capScale x : ℂ) =
      deriv (fun y => D4BMFutureSeedHorizon.seedCapField q branch amp (v-y) y X k) x/
        (capScale x : ℂ)-parameter q branch*
          (deriv (fun y => D4BMFutureHorizon.capBoundaryField q branch amp (v-y) y X k) x/
            (capScale x : ℂ)) := by
    rw [(seedCapField_ingoing_normal_hasDerivAt q branch amp v x X k).deriv,
      (D4BMCapNormalTrace.capBoundaryField_ingoing_normal_hasDerivAt q branch amp v x X k).deriv]
    field_simp [Complex.ofReal_ne_zero.mpr (scale_pos x).ne']
    ring
  simpa only [he] using hs.sub hc

end
end RHTower.D4BMFullSeedCapRadialMemory
