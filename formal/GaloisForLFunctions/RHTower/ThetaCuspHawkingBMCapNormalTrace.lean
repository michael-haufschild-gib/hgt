import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFutureHorizonCap
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceOnsetDerivativeBound
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Actual differentiated traces of the original full-theta cap.

The unchanged onset's first two derivatives satisfy the source-admission decay bound.
A bijective delay substitution fixes the theta mean and transfers the normal derivative
to the onset and its Jacobian. The resulting normal weight is an exact source derivative
with zero endpoint contribution. This proves the original arm's normal derivative and
its zero ingoing trace. Both original cap arms are retained in the actual time derivative;
its horizon limit is exactly the original source lift's time contact.

Angular differentiation of the cap integral, the full cap's radial derivative in the
ingoing radius, other causal corrections, and complete nonlinear current cancellation
are not established by this leaf.
-/

set_option autoImplicit false
open Set MeasureTheory Filter Topology

namespace RHTower.D4BMCapNormalTrace
open D4BMFutureHorizon D4BMFullSourceAdvanced D4BMNativeCircle
open D4BMJointSource D4BMModularCore
noncomputable section

private theorem decay_pos (q : XiZeroCopy) : 0 < decayExponent q := by
  have h := (sourceGrowthExponent_bounds q).1
  have hc := (decayExponent_bounds q).1
  linarith

private theorem shifted_second (v : ℂ) (c u : ℝ) :
    timeOnsetSecond v u = Complex.exp (-(c:ℂ)*(u:ℂ))*
      (timeOnsetSecond (v+c) u-2*c*timeOnsetFirst (v+c) u+
        (c:ℂ)^2*timeOnset (v+c) u) := by
  unfold timeOnsetSecond timeOnsetFirst timeOnset
  have he : Complex.exp (-(c:ℂ)*(u:ℂ))*Complex.exp ((v+c)*(u:ℂ)) =
      Complex.exp (v*(u:ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  calc
    _ = Complex.exp (v*(u:ℂ))*
        (((deriv (deriv Real.smoothTransition) u:ℝ):ℂ)+
          2*v*((deriv Real.smoothTransition u:ℝ):ℂ)+v^2*(Real.smoothTransition u:ℂ)) := by ring
    _ = _ := by rw [← he]; ring

/-- The original onset's first two derivatives share the source-admitted decay exponent. -/
theorem onset_derivative_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ u : ℝ,
      ‖timeOnsetFirst (2*physicalRate q branch) u‖+
        ‖timeOnsetSecond (2*physicalRate q branch) u‖ ≤ B*Real.exp (-decayExponent q*u) := by
  let v := 2*physicalRate q branch
  let c := decayExponent q
  have hv : v.re ≤ -c := by
    have h := currentRate_re_lt q branch
    change (2*physicalRate q branch).re < -2 at h
    dsimp [v,c]
    linarith [(decayExponent_bounds q).2]
  have hc : 0 ≤ c := (decay_pos q).le
  have hvc : (v+c).re ≤ 0 := by simp only [Complex.add_re,Complex.ofReal_re]; linarith
  obtain ⟨B,hB,hb⟩ := timeOnset_pair_bound v c hv
  obtain ⟨D,hD,hd⟩ := timeOnset_derivative_pair_bound (v+c) hvc
  obtain ⟨A,hA,ha⟩ := timeOnset_pair_bound (v+c) 0 (by simpa using hvc)
  refine ⟨B+D+2*c*D+c^2*A,by positivity,fun u => ?_⟩
  have h0 : ‖timeOnset (v+c) u‖ ≤ A := by
    have h := ha u
    simp only [neg_zero,zero_mul,Real.exp_zero,mul_one] at h
    linarith [norm_nonneg (timeOnsetFirst (v+c) u)]
  have h1 : ‖timeOnsetFirst (v+c) u‖ ≤ D := by linarith [hd u,norm_nonneg (timeOnsetSecond (v+c) u)]
  have h2 : ‖timeOnsetSecond (v+c) u‖ ≤ D := by linarith [hd u,norm_nonneg (timeOnsetFirst (v+c) u)]
  have hs : ‖timeOnsetSecond v u‖ ≤ Real.exp (-c*u)*(D+2*c*D+c^2*A) := by
    rw [shifted_second v c u,norm_mul,Complex.norm_exp]
    have he : (-(c:ℂ)*(u:ℂ)).re = -c*u := by simp
    rw [he]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    calc
      _ ≤ ‖timeOnsetSecond (v+c) u‖+‖2*(c:ℂ)*timeOnsetFirst (v+c) u‖+
          ‖(c:ℂ)^2*timeOnset (v+c) u‖ := (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ D+2*c*D+c^2*A := by
        simp only [norm_mul,norm_pow,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
        gcongr
  have hf : ‖timeOnsetFirst v u‖ ≤ B*Real.exp (-c*u) := by
    linarith [hb u,norm_nonneg (timeOnset v u)]
  change ‖timeOnsetFirst v u‖+‖timeOnsetSecond v u‖ ≤ _
  nlinarith

private theorem first_continuous (s : ℂ) : Continuous (timeOnsetFirst s) :=
  continuous_iff_continuousAt.mpr (fun u => (timeOnsetFirst_hasDerivAt s u).continuousAt)

private theorem mean_continuous (q : XiZeroCopy) (x X k : ℝ) :
    Continuous (fun h => horizonMean q x h X k) := by
  change Continuous (fun h => mean q (Real.arcosh (max 1
    (1+(Real.exp x/Real.cosh x)*(Real.exp h-1)))) X k)
  have hc : Continuous (fun z : ℝ => mean q (Real.arcosh (max 1 z)) X k) := by
    apply (mean_radial_smooth q X k).continuous.comp
    exact Real.continuousOn_arcosh.comp_continuous (continuous_const.max continuous_id)
      (fun z => le_max_left 1 z)
  exact hc.comp (continuous_const.add ((Real.continuous_exp.sub continuous_const).const_mul _))

/-- Exact onset weight after transferring the normal derivative to source time. -/
def normalWeight (q : XiZeroCopy) (branch : Bool) (v h : ℝ) : ℂ :=
  timeOnsetSecond (2*physicalRate q branch) (v+h)*(1-(Real.exp (-h):ℂ))+
    timeOnsetFirst (2*physicalRate q branch) (v+h)*(Real.exp (-h):ℂ)

private def sourceWeight (q : XiZeroCopy) (branch normal : Bool) (v h : ℝ) : ℂ :=
  if normal then normalWeight q branch v h else timeOnsetSecond (2*physicalRate q branch) (v+h)

private theorem weight_continuous (q : XiZeroCopy) (branch normal : Bool) (v : ℝ) :
    Continuous (sourceWeight q branch normal v) := by
  have h0 := timeOnsetSecond_continuous (2*physicalRate q branch)
  have h1 := first_continuous (2*physicalRate q branch)
  cases normal
  · exact h0.comp (continuous_const.add continuous_id)
  · exact ((h0.comp (continuous_const.add continuous_id)).mul
      (continuous_const.sub (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)))).add
      ((h1.comp (continuous_const.add continuous_id)).mul
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)))

private theorem weight_bound (q : XiZeroCopy) (branch normal : Bool) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ v h : ℝ, 0 ≤ h →
      ‖sourceWeight q branch normal v h‖ ≤ B*Real.exp (-decayExponent q*(v+h)) := by
  obtain ⟨B,hB,hb⟩ := onset_derivative_bound q branch
  refine ⟨B,hB,fun v h hh => ?_⟩
  have he : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have he1 : Real.exp (-h) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  cases normal
  · change ‖timeOnsetSecond (2*physicalRate q branch) (v+h)‖ ≤ _
    linarith [hb (v+h),norm_nonneg (timeOnsetFirst (2*physicalRate q branch) (v+h))]
  · change ‖normalWeight q branch v h‖ ≤ _
    unfold normalWeight
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg he]
    rw [show (1:ℂ)-(Real.exp (-h):ℂ) = ((1-Real.exp (-h):ℝ):ℂ) by push_cast; rfl]
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr he1)]
    have hN0 := norm_nonneg (timeOnsetFirst (2*physicalRate q branch) (v+h))
    have hN1 := norm_nonneg (timeOnsetSecond (2*physicalRate q branch) (v+h))
    nlinarith [hb (v+h)]

private def weightedDensity (q : XiZeroCopy) (branch normal : Bool) (v x X k h : ℝ) : ℂ :=
  sourceWeight q branch normal v h*horizonMean q x h X k

private theorem density_continuous (q : XiZeroCopy) (branch normal : Bool) (v x X k : ℝ) :
    Continuous (weightedDensity q branch normal v x X k) :=
  (weight_continuous q branch normal v).mul (mean_continuous q x X k)

private theorem density_bound (q : XiZeroCopy) (branch normal : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k h : ℝ, 0 ≤ h →
      ‖weightedDensity q branch normal v x X k h‖ ≤
        (C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|))*
          Real.exp ((sourceGrowthExponent q-decayExponent q)*h) := by
  obtain ⟨B,hB,hb⟩ := weight_bound q branch normal
  obtain ⟨C,hC,hc⟩ := horizonMean_growth q
  refine ⟨B*C,mul_nonneg hB hC,fun v x X k h hh => ?_⟩
  rw [weightedDensity,norm_mul]
  calc
    _ ≤ (B*Real.exp (-decayExponent q*(v+h)))*
        (C*Real.exp (sourceGrowthExponent q*(h+|k|))) :=
      mul_le_mul (hb v h hh) (hc x h X k hh) (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (-decayExponent q*(v+h))*Real.exp (sourceGrowthExponent q*(h+|k|)) =
          Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|)*
            Real.exp ((sourceGrowthExponent q-decayExponent q)*h) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      calc
        _ = (B*C)*(Real.exp (-decayExponent q*(v+h))*Real.exp (sourceGrowthExponent q*(h+|k|))) := by ring
        _ = _ := by rw [he]; ring

private theorem majorant_integrable (q : XiZeroCopy) (C : ℝ) :
    IntegrableOn (fun h => C*Real.exp ((sourceGrowthExponent q-decayExponent q)*h)) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (sub_neg.mpr (decayExponent_bounds q).1) 0).const_mul C

private theorem density_integrable (q : XiZeroCopy) (branch normal : Bool) (v x X k : ℝ) :
    IntegrableOn (weightedDensity q branch normal v x X k) (Ioi 0) := by
  obtain ⟨C,hC,hb⟩ := density_bound q branch normal
  apply (majorant_integrable q (C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|))).mono'
    (density_continuous q branch normal v x X k).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact hb v x X k h hh.le

private def weightedArm (q : XiZeroCopy) (branch normal : Bool) (v x X k : ℝ) : ℂ :=
  ∫ h in Ioi (0:ℝ), weightedDensity q branch normal v x X k h

private theorem weightedArm_bound (q : XiZeroCopy) (branch normal : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k : ℝ,
      ‖weightedArm q branch normal v x X k‖ ≤
        C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|) := by
  obtain ⟨C,hC,hb⟩ := density_bound q branch normal
  have hp : 0 < decayExponent q-sourceGrowthExponent q := sub_pos.mpr (decayExponent_bounds q).1
  refine ⟨C/(decayExponent q-sourceGrowthExponent q),div_nonneg hC hp.le,fun v x X k => ?_⟩
  let D := C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|)
  have hi := density_integrable q branch normal v x X k
  calc
    _ ≤ ∫ h in Ioi (0:ℝ), ‖weightedDensity q branch normal v x X k h‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ h in Ioi (0:ℝ), D*Real.exp ((sourceGrowthExponent q-decayExponent q)*h) :=
      setIntegral_mono_on hi.norm (majorant_integrable q D) measurableSet_Ioi (fun h hh => hb v x X k h hh.le)
    _ = _ := by
      rw [integral_const_mul,integral_exp_mul_Ioi (by linarith : sourceGrowthExponent q-decayExponent q<0)]
      simp only [mul_zero,Real.exp_zero]
      dsimp only [D]
      rw [show sourceGrowthExponent q-decayExponent q=-(decayExponent q-sourceGrowthExponent q) by ring]
      simp only [neg_div_neg_eq]
      ring

private theorem weightedArm_limit (q : XiZeroCopy) (branch normal : Bool) (v X k : ℝ) :
    Tendsto (fun x => weightedArm q branch normal v x X k) atBot
      (𝓝 ((∫ h in Ioi (0:ℝ), sourceWeight q branch normal v h)*fullSquarePotential q ![X,Real.exp k])) := by
  obtain ⟨C,hC,hb⟩ := density_bound q branch normal
  let D := C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|)
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi (0:ℝ))) (fun h => D*Real.exp ((sourceGrowthExponent q-decayExponent q)*h))
    (Filter.Eventually.of_forall (fun x => (density_continuous q branch normal v x X k).aestronglyMeasurable))
    (Filter.Eventually.of_forall (fun x => (ae_restrict_mem measurableSet_Ioi).mono (fun h hh => hb v x X k h hh.le)))
    (majorant_integrable q D)
    (Filter.Eventually.of_forall (fun h => (horizonMean_ingoing q h X k).const_mul (sourceWeight q branch normal v h)))
  simpa only [weightedArm,weightedDensity,integral_mul_const] using ht

/-- Admitted integral of the original time-differentiated cap density. -/
def timeArm (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) : ℂ :=
  weightedArm q branch false v x X k

/-- Original cap time derivative; no differentiated-theta estimate is supplied. -/
theorem boundaryArm_time_hasDerivAt (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) :
    HasDerivAt (fun w => boundaryArm q branch w x X k) (timeArm q branch v x X k) v := by
  obtain ⟨C,hC,hb⟩ := density_bound q branch false
  let B := C*Real.exp (-decayExponent q*(v-1)+sourceGrowthExponent q*|k|)
  have hn : Ioo (v-1) (v+1) ∈ 𝓝 v := Ioo_mem_nhds (by linarith) (by linarith)
  have hm (w : ℝ) : Continuous (boundaryDensity q branch w x X k) :=
    ((first_continuous _).comp (continuous_const.add continuous_id)).mul (mean_continuous q x X k)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun w h => boundaryDensity q branch w x X k h)
    (F' := fun w h => weightedDensity q branch false w x X k h)
    (bound := fun h => B*Real.exp ((sourceGrowthExponent q-decayExponent q)*h)) hn
    (Filter.Eventually.of_forall (fun w => (hm w).aestronglyMeasurable))
    (boundaryDensity_integrable q branch v x X k)
    (density_continuous q branch false v x X k).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      intro w hw
      apply (hb w x X k h hh.le).trans
      dsimp only [B]
      have he : -decayExponent q*w+sourceGrowthExponent q*|k| ≤
          -decayExponent q*(v-1)+sourceGrowthExponent q*|k| := by
        have h := mul_le_mul_of_nonpos_left hw.1.le (neg_nonpos.mpr (decay_pos q).le)
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC) (Real.exp_pos _).le)
    (majorant_integrable q B)
    (by
      filter_upwards with h
      intro w hw
      simpa only [boundaryDensity,weightedDensity,sourceWeight,Bool.false_eq_true,↓reduceIte,add_comm] using
        (HasDerivAt.comp_const_add h w (timeOnsetFirst_hasDerivAt (2*physicalRate q branch) (h+w))).mul_const
          (horizonMean q x h X k))).2

private theorem sourceWeight_integrable (q : XiZeroCopy) (branch normal : Bool) (v : ℝ) :
    IntegrableOn (sourceWeight q branch normal v) (Ioi 0) := by
  obtain ⟨B,hB,hb⟩ := weight_bound q branch normal
  have hm := (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr (decay_pos q)) 0).const_mul
    (B*Real.exp (-decayExponent q*v))
  apply hm.mono' (weight_continuous q branch normal v).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have he : (B*Real.exp (-decayExponent q*v))*Real.exp (-decayExponent q*h) =
      B*Real.exp (-decayExponent q*(v+h)) := by
    rw [mul_assoc,← Real.exp_add]
    congr 2
    ring
  rw [he]
  exact hb v h hh.le

private theorem onsetFirst_shift_limit (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    Tendsto (fun h => timeOnsetFirst (2*physicalRate q branch) (v+h)) atTop (𝓝 0) := by
  obtain ⟨B,hB,hb⟩ := onset_derivative_bound q branch
  have he := Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (neg_lt_zero.mpr (decay_pos q))).mpr tendsto_id)
  have hbnd (h : ℝ) : ‖timeOnsetFirst (2*physicalRate q branch) (v+h)‖ ≤
      (B*Real.exp (-decayExponent q*v))*Real.exp (-decayExponent q*h) := by
    rw [mul_assoc,← Real.exp_add,show -decayExponent q*v+-decayExponent q*h=
        -decayExponent q*(v+h) by ring]
    linarith [hb (v+h),norm_nonneg (timeOnsetSecond (2*physicalRate q branch) (v+h))]
  apply squeeze_zero_norm hbnd
  simpa only [Function.comp_def,id_eq,mul_zero] using he.const_mul (B*Real.exp (-decayExponent q*v))

/-- Exact time contact, including the lower characteristic endpoint. -/
theorem onsetSecond_future_integral (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    (∫ h in Ioi (0:ℝ), timeOnsetSecond (2*physicalRate q branch) (v+h)) =
      -timeOnsetFirst (2*physicalRate q branch) v := by
  have hd (h : ℝ) (_ : h ∈ Ici (0:ℝ)) :
      HasDerivAt (fun t => timeOnsetFirst (2*physicalRate q branch) (v+t))
        (timeOnsetSecond (2*physicalRate q branch) (v+h)) h :=
    HasDerivAt.comp_const_add v h (timeOnsetFirst_hasDerivAt _ (v+h))
  simpa only [add_zero,zero_sub] using integral_Ioi_of_hasDerivAt_of_tendsto' hd
    (sourceWeight_integrable q branch false v) (onsetFirst_shift_limit q branch v)

private theorem normalPrimitive_hasDerivAt (q : XiZeroCopy) (branch : Bool) (v h : ℝ) :
    HasDerivAt (fun t => timeOnsetFirst (2*physicalRate q branch) (v+t)*(1-(Real.exp (-t):ℂ)))
      (normalWeight q branch v h) h := by
  have hg := HasDerivAt.comp_const_add v h
    (timeOnsetFirst_hasDerivAt (2*physicalRate q branch) (v+h))
  have he := (Real.hasDerivAt_exp (-h)).comp h (hasDerivAt_neg h)
  have hw := he.ofReal_comp.const_sub (1:ℂ)
  convert! hg.mul hw using 1
  dsimp only [normalWeight,Function.comp_def]
  push_cast
  ring

/-- The full transferred normal weight has zero total source contact. -/
theorem normalWeight_future_integral (q : XiZeroCopy) (branch : Bool) (v : ℝ) :
    (∫ h in Ioi (0:ℝ), normalWeight q branch v h) = 0 := by
  have he : Tendsto (fun h : ℝ => Real.exp (-h)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hw : Tendsto (fun h : ℝ => (1:ℂ)-(Real.exp (-h):ℂ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (Complex.continuous_ofReal.tendsto 0 |>.comp he)
  have ht := (onsetFirst_shift_limit q branch v).mul hw
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun h (_ : h ∈ Ici (0:ℝ)) => normalPrimitive_hasDerivAt q branch v h)
    (sourceWeight_integrable q branch true v) ht
  simpa only [zero_mul,neg_zero,Real.exp_zero,Complex.ofReal_one,sub_self,mul_zero] using hi

/-- Source-derived transferred normal arm, before identifying the cap derivative. -/
def normalArm (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) : ℂ :=
  weightedArm q branch true v x X k

/-- The actual time derivative has its original horizon contact. -/
theorem timeArm_ingoing (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    Tendsto (fun x => timeArm q branch v x X k) atBot
      (𝓝 (-timeOnsetFirst (2*physicalRate q branch) v*fullSquarePotential q ![X,Real.exp k])) := by
  simpa only [timeArm,sourceWeight,Bool.false_eq_true,↓reduceIte,onsetSecond_future_integral]
    using weightedArm_limit q branch false v X k

/-- The transferred normal arm has no ingoing horizon contact. -/
theorem normalArm_ingoing (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    Tendsto (fun x => normalArm q branch v x X k) atBot (𝓝 0) := by
  simpa only [normalArm,sourceWeight,↓reduceIte,normalWeight_future_integral,zero_mul]
    using weightedArm_limit q branch true v X k

private def delayFlow (b h : ℝ) : ℝ := Real.log ((b+Real.exp h-1)/b)
private def delayJac (b h : ℝ) : ℝ := Real.exp h/(b+Real.exp h-1)
private def delaySlope (b h : ℝ) : ℝ := (b+Real.exp h-1)⁻¹-b⁻¹
private def jacSlope (b h : ℝ) : ℝ := -Real.exp h/(b+Real.exp h-1)^2

private theorem delay_den_pos (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    0 < b+Real.exp h-1 := by
  have he := Real.one_le_exp_iff.mpr hh
  linarith

private theorem delay_exp (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    Real.exp (delayFlow b h) = (b+Real.exp h-1)/b :=
  Real.exp_log (div_pos (delay_den_pos b h hb hh) hb)

private theorem delay_pos (b h : ℝ) (hb : 0 < b) (hh : 0 < h) :
    0 < delayFlow b h := by
  apply Real.log_pos
  rw [lt_div_iff₀ hb]
  have he := Real.one_lt_exp_iff.mpr hh
  linarith

private theorem delay_h_derivative (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    HasDerivAt (delayFlow b) (delayJac b h) h := by
  have hd := (((Real.hasDerivAt_exp h).const_add b).sub_const 1).div_const b
  have hl := hd.log (div_ne_zero (delay_den_pos b h hb hh).ne' hb.ne')
  convert! hl using 1
  dsimp [delayJac]
  field_simp

private theorem delay_b_derivative (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    HasDerivAt (fun a => delayFlow a h) (delaySlope b h) b := by
  have hd := (((hasDerivAt_id b).add_const (Real.exp h)).sub_const 1).div (hasDerivAt_id b) hb.ne'
  have hl := hd.log (div_ne_zero (delay_den_pos b h hb hh).ne' hb.ne')
  convert! hl using 1
  dsimp [delaySlope]
  field_simp [hb.ne',(delay_den_pos b h hb hh).ne']

private theorem jac_b_derivative (b h : ℝ) (hb : 0 < b) (hh : 0 ≤ h) :
    HasDerivAt (fun a => delayJac a h) (jacSlope b h) b := by
  have hd := (hasDerivAt_const b (Real.exp h)).div
    (((hasDerivAt_id b).add_const (Real.exp h)).sub_const 1) (delay_den_pos b h hb hh).ne'
  convert! hd using 1
  simp only [jacSlope,zero_mul,mul_one,zero_sub,id_eq]

private theorem delay_image (b : ℝ) (hb : 0 < b) :
    delayFlow b '' Ioi 0 = Ioi 0 := by
  apply Set.Subset.antisymm
  · rintro y ⟨h,hh,rfl⟩
    exact delay_pos b h hb hh
  · intro y hy
    let t := Real.log (1+b*(Real.exp y-1))
    have hyE : 1 < Real.exp y := Real.one_lt_exp_iff.mpr hy
    have ha : 1 < 1+b*(Real.exp y-1) := by nlinarith
    have ht : 0 < t := Real.log_pos ha
    refine ⟨t,ht,?_⟩
    apply Real.exp_injective
    rw [delay_exp b t hb ht.le,show Real.exp t=1+b*(Real.exp y-1) from Real.exp_log (by linarith)]
    field_simp
    ring

private theorem delay_inj (b : ℝ) (hb : 0 < b) :
    Set.InjOn (delayFlow b) (Ioi 0) := by
  intro h hh t ht he
  have hf := congrArg Real.exp he
  rw [delay_exp b h hb hh.le,delay_exp b t hb ht.le] at hf
  have hd := (div_left_inj' hb.ne').mp hf
  exact Real.exp_injective (by linarith)

private theorem delay_local_bounds (b h : ℝ) (hb : b ∈ Ioo (1/2:ℝ) 2) (hh : 0 ≤ h) :
    0 < b ∧ 0 < delayJac b h ∧ delayJac b h ≤ 2 ∧
      |delaySlope b h| ≤ 4 ∧ |jacSlope b h| ≤ 4 ∧ h-Real.log 2 ≤ delayFlow b h := by
  have hb0 : 0 < b := by linarith [hb.1]
  have he : 1 ≤ Real.exp h := Real.one_le_exp_iff.mpr hh
  have hd := delay_den_pos b h hb0 hh
  have hdE : Real.exp h/2 ≤ b+Real.exp h-1 := by linarith [hb.1]
  have hdb : b ≤ b+Real.exp h-1 := by linarith
  have hdi : (b+Real.exp h-1)⁻¹ ≤ 2 := by
    rw [← one_div,div_le_iff₀ hd]
    linarith [hb.1]
  have hbi : b⁻¹ ≤ 2 := by rw [← one_div,div_le_iff₀ hb0]; linarith [hb.1]
  have hj0 : 0 < delayJac b h := div_pos (Real.exp_pos h) hd
  have hj2 : delayJac b h ≤ 2 := by
    dsimp [delayJac]
    rw [div_le_iff₀ hd]
    linarith
  have hs : |delaySlope b h| ≤ 4 := by
    apply (abs_sub _ _).trans
    rw [abs_of_pos (inv_pos.mpr hd),abs_of_pos (inv_pos.mpr hb0)]
    linarith
  have hjs : |jacSlope b h| ≤ 4 := by
    rw [jacSlope,abs_div,abs_neg,abs_of_pos (Real.exp_pos h),abs_of_nonneg (sq_nonneg _)]
    rw [div_le_iff₀ (sq_pos_of_pos hd)]
    have hhalf : (1/2:ℝ) ≤ b+Real.exp h-1 := by linarith [hb.1]
    nlinarith
  refine ⟨hb0,hj0,hj2,hs,hjs,?_⟩
  rw [← Real.exp_le_exp,delay_exp b h hb0 hh,Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<2)]
  rw [le_div_iff₀ hb0]
  have hp := mul_nonneg (sub_nonneg.mpr he) (sub_nonneg.mpr hb.2.le)
  nlinarith

private def movedDensity (q : XiZeroCopy) (branch : Bool) (v x X k b h : ℝ) : ℂ :=
  timeOnsetFirst (2*physicalRate q branch) (v+delayFlow b h)*(delayJac b h:ℂ)*
    horizonMean q x h X k

private def movedDerivative (q : XiZeroCopy) (branch : Bool) (v x X k b h : ℝ) : ℂ :=
  (timeOnsetSecond (2*physicalRate q branch) (v+delayFlow b h)*(delaySlope b h:ℂ)*(delayJac b h:ℂ)+
    timeOnsetFirst (2*physicalRate q branch) (v+delayFlow b h)*(jacSlope b h:ℂ))*
    horizonMean q x h X k

private theorem movedDensity_derivative (q : XiZeroCopy) (branch : Bool) (v x X k b h : ℝ)
    (hb : 0 < b) (hh : 0 ≤ h) :
    HasDerivAt (fun a => movedDensity q branch v x X k a h)
      (movedDerivative q branch v x X k b h) b := by
  have hg := (timeOnsetFirst_hasDerivAt (2*physicalRate q branch) (v+delayFlow b h)).scomp b
    ((delay_b_derivative b h hb hh).const_add v)
  have hj := (jac_b_derivative b h hb hh).ofReal_comp
  convert! (hg.mul hj).mul_const (horizonMean q x h X k) using 1
  simp only [movedDerivative,Complex.real_smul,Function.comp_apply]
  ring

private theorem movedDerivative_bound (q : XiZeroCopy) (branch : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v x X k b h : ℝ, b ∈ Ioo (1/2:ℝ) 2 → 0 ≤ h →
      ‖movedDerivative q branch v x X k b h‖ ≤
        C*Real.exp (-decayExponent q*(v-Real.log 2)+sourceGrowthExponent q*|k|)*
          Real.exp ((sourceGrowthExponent q-decayExponent q)*h) := by
  obtain ⟨B,hB,hb⟩ := onset_derivative_bound q branch
  obtain ⟨C,hC,hc⟩ := horizonMean_growth q
  refine ⟨8*B*C,by positivity,fun v x X k b h hbl hh => ?_⟩
  obtain ⟨hb0,hj0,hj2,hs,hjs,hflow⟩ := delay_local_bounds b h hbl hh
  have hg1 := norm_nonneg (timeOnsetFirst (2*physicalRate q branch) (v+delayFlow b h))
  have hg2 := norm_nonneg (timeOnsetSecond (2*physicalRate q branch) (v+delayFlow b h))
  have hm : ‖timeOnsetSecond (2*physicalRate q branch) (v+delayFlow b h)*(delaySlope b h:ℂ)*(delayJac b h:ℂ)+
      timeOnsetFirst (2*physicalRate q branch) (v+delayFlow b h)*(jacSlope b h:ℂ)‖ ≤
      8*B*Real.exp (-decayExponent q*(v+delayFlow b h)) := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hj0]
    have ha := mul_le_mul_of_nonneg_left hs hg2
    have hb' := mul_le_mul_of_nonneg_left hjs hg1
    have hj := mul_le_mul ha hj2 (le_of_lt hj0) (by positivity)
    nlinarith [hb (v+delayFlow b h)]
  have he : Real.exp (-decayExponent q*(v+delayFlow b h)) ≤
      Real.exp (-decayExponent q*(v-Real.log 2+h)) := by
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonpos_left hflow (neg_nonpos.mpr (decay_pos q).le)
    linarith
  rw [movedDerivative,norm_mul]
  calc
    _ ≤ (8*B*Real.exp (-decayExponent q*(v+delayFlow b h)))*
        (C*Real.exp (sourceGrowthExponent q*(h+|k|))) :=
      mul_le_mul hm (hc x h X k hh) (norm_nonneg _) (by positivity)
    _ ≤ (8*B*Real.exp (-decayExponent q*(v-Real.log 2+h)))*
        (C*Real.exp (sourceGrowthExponent q*(h+|k|))) := by gcongr
    _ = _ := by
      have hexp : Real.exp (-decayExponent q*(v-Real.log 2+h))*Real.exp (sourceGrowthExponent q*(h+|k|)) =
          Real.exp (-decayExponent q*(v-Real.log 2)+sourceGrowthExponent q*|k|)*
            Real.exp ((sourceGrowthExponent q-decayExponent q)*h) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      calc
        _ = (8*B*C)*(Real.exp (-decayExponent q*(v-Real.log 2+h))*Real.exp (sourceGrowthExponent q*(h+|k|))) := by ring
        _ = _ := by rw [hexp]; ring

private theorem delay_one (h : ℝ) : delayFlow 1 h=h ∧ delayJac 1 h=1 ∧
    delaySlope 1 h=Real.exp (-h)-1 ∧ jacSlope 1 h= -Real.exp (-h) := by
  have he := (Real.exp_pos h).ne'
  simp [delayFlow,delayJac,delaySlope,jacSlope,Real.exp_neg]
  field_simp

private theorem movedDensity_one (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) :
    movedDensity q branch v x X k 1=boundaryDensity q branch v x X k := by
  funext h
  rw [movedDensity,(delay_one h).1,(delay_one h).2.1]
  simp only [Complex.ofReal_one,mul_one,boundaryDensity]

private theorem movedDerivative_one (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) :
    movedDerivative q branch v x X k 1=fun h => -weightedDensity q branch true v x X k h := by
  funext h
  rw [movedDerivative,(delay_one h).1,(delay_one h).2.1,
    (delay_one h).2.2.1,(delay_one h).2.2.2]
  simp only [weightedDensity,sourceWeight,↓reduceIte,normalWeight,Complex.ofReal_one,
    Complex.ofReal_sub,Complex.ofReal_neg]
  ring

private theorem movedDensity_measurable (q : XiZeroCopy) (branch : Bool) (v x X k b : ℝ) (hb : 0 < b) :
    AEStronglyMeasurable (movedDensity q branch v x X k b) (volume.restrict (Ioi 0)) := by
  have hf : ContinuousOn (delayFlow b) (Ioi 0) := fun h hh =>
    (delay_h_derivative b h hb hh.le).continuousAt.continuousWithinAt
  have hj : ContinuousOn (delayJac b) (Ioi 0) :=
    Real.continuous_exp.continuousOn.div
      ((continuous_const.add Real.continuous_exp).sub continuous_const).continuousOn
      (fun h hh => (delay_den_pos b h hb hh.le).ne')
  have hg : ContinuousOn (fun h => timeOnsetFirst (2*physicalRate q branch) (v+delayFlow b h)) (Ioi 0) :=
    (first_continuous (2*physicalRate q branch)).comp_continuousOn (continuousOn_const.add hf)
  exact ((hg.mul (Complex.continuous_ofReal.comp_continuousOn hj)).mul
    (mean_continuous q x X k).continuousOn).aestronglyMeasurable measurableSet_Ioi

private theorem movedIntegral_derivative (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) :
    HasDerivAt (fun b => ∫ h in Ioi (0:ℝ), movedDensity q branch v x X k b h)
      (-normalArm q branch v x X k) 1 := by
  obtain ⟨C,hC,hb⟩ := movedDerivative_bound q branch
  let B := C*Real.exp (-decayExponent q*(v-Real.log 2)+sourceGrowthExponent q*|k|)
  have hn : Ioo (1/2:ℝ) 2 ∈ 𝓝 1 := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hm : ∀ᶠ b in 𝓝 (1:ℝ), AEStronglyMeasurable
      (movedDensity q branch v x X k b) (volume.restrict (Ioi 0)) := by
    filter_upwards [hn] with b hb
    exact movedDensity_measurable q branch v x X k b (by linarith [hb.1])
  have hi : IntegrableOn (movedDensity q branch v x X k 1) (Ioi 0) := by
    rw [movedDensity_one]
    exact boundaryDensity_integrable q branch v x X k
  have hm' : AEStronglyMeasurable (movedDerivative q branch v x X k 1) (volume.restrict (Ioi 0)) := by
    rw [movedDerivative_one]
    exact (density_continuous q branch true v x X k).neg.aestronglyMeasurable
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun b h => movedDensity q branch v x X k b h)
    (F' := fun b h => movedDerivative q branch v x X k b h)
    (bound := fun h => B*Real.exp ((sourceGrowthExponent q-decayExponent q)*h))
    hn hm hi hm'
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      intro b hbl
      exact hb v x X k b h hbl hh.le)
    (majorant_integrable q B)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      intro b hbl
      exact movedDensity_derivative q branch v x X k b h (by linarith [hbl.1]) hh.le)).2
  simpa only [movedDerivative_one,integral_neg,normalArm,weightedArm] using hd

/-- Original scale of the cap circle argument. -/
def capScale (x : ℝ) : ℝ := Real.exp x/Real.cosh x

private theorem capScale_pos (x : ℝ) : 0 < capScale x :=
  div_pos (Real.exp_pos x) (Real.cosh_pos x)

private theorem capScale_derivative (x : ℝ) :
    HasDerivAt capScale (capScale x*(2-capScale x)) x := by
  have hd := (Real.hasDerivAt_exp x).div (Real.hasDerivAt_cosh x) (Real.cosh_pos x).ne'
  convert! hd using 1
  dsimp [capScale]
  rw [← Real.cosh_add_sinh x]
  field_simp
  ring

private theorem capScale_ingoing : Tendsto capScale atBot (𝓝 (0:ℝ)) := by
  have ht : Tendsto (fun x : ℝ => 2*x) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (by norm_num : (0:ℝ)<2)).mpr tendsto_id
  have he := Real.tendsto_exp_atBot.comp ht
  have hc (x : ℝ) : capScale x=1-radialUnit x := by
    rw [capScale,radialUnit,← Real.cosh_add_sinh x]
    field_simp [(Real.cosh_pos x).ne']
    ring
  have hform : capScale=fun x => 2*Real.exp (2*x)/(1+Real.exp (2*x)) := by
    funext x
    rw [eq_div_iff (ne_of_gt (by positivity : 0 < 1+Real.exp (2*x))),hc]
    have hh := radialUnit_one_sub x
    nlinarith
  rw [hform]
  simpa only [Function.comp_def,Pi.div_apply,mul_zero,add_zero,zero_div]
    using! (he.const_mul 2).div (tendsto_const_nhds.add he) (by norm_num : (1:ℝ)+0 ≠ 0)

private theorem mean_moved (q : XiZeroCopy) (x y X k h : ℝ) (hh : 0 ≤ h) :
    horizonMean q x (delayFlow (capScale x/capScale y) h) X k=horizonMean q y h X k := by
  change mean q (Real.arcosh (max 1 (1+capScale x*(Real.exp (delayFlow (capScale x/capScale y) h)-1)))) X k=
    mean q (Real.arcosh (max 1 (1+capScale y*(Real.exp h-1)))) X k
  rw [delay_exp _ _ (div_pos (capScale_pos x) (capScale_pos y)) hh]
  congr 4
  field_simp [(capScale_pos x).ne',(capScale_pos y).ne']
  ring

/-- Exact change of delay in the original cap; both characteristic domains are unchanged. -/
private theorem boundaryArm_moved (q : XiZeroCopy) (branch : Bool) (v x y X k : ℝ) :
    boundaryArm q branch v x X k=
      ∫ h in Ioi (0:ℝ), movedDensity q branch v y X k (capScale x/capScale y) h := by
  let b := capScale x/capScale y
  have hb : 0 < b := div_pos (capScale_pos x) (capScale_pos y)
  have hi := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
    (fun h (hh : h ∈ Ioi (0:ℝ)) => (delay_h_derivative b h hb hh.le).hasDerivWithinAt)
    (delay_inj b hb) (boundaryDensity q branch v x X k)
  rw [delay_image b hb] at hi
  change (∫ h in Ioi (0:ℝ), boundaryDensity q branch v x X k h)=_
  rw [hi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro h hh
  change |delayJac b h| • boundaryDensity q branch v x X k (delayFlow b h)=_
  rw [abs_of_pos (show 0 < delayJac b h from div_pos (Real.exp_pos h) (delay_den_pos b h hb hh.le)),Complex.real_smul]
  rw [boundaryDensity,show b=capScale x/capScale y from rfl,mean_moved q x y X k h hh.le]
  dsimp [movedDensity]
  ring

/-- Actual normal derivative of the full theta cap arm at fixed original ingoing time. -/
theorem boundaryArm_normal_hasDerivAt (q : XiZeroCopy) (branch : Bool) (v x X k : ℝ) :
    HasDerivAt (fun y => boundaryArm q branch v y X k)
      (-((2-capScale x:ℝ):ℂ)*normalArm q branch v x X k) x := by
  have hk : HasDerivAt (fun y => capScale y/capScale x) (2-capScale x) x := by
    convert! (capScale_derivative x).div_const (capScale x) using 1
    field_simp [(capScale_pos x).ne']
  have ht := (movedIntegral_derivative q branch v x X k).scomp_of_eq x hk
    (by simp only [div_self (capScale_pos x).ne'] : (1:ℝ)=capScale x/capScale x)
  convert! ht using 1
  · funext y
    exact boundaryArm_moved q branch v y x X k
  · simp only [Complex.real_smul]
    ring

/-- The original arm's normal derivative has zero ingoing horizon trace. -/
theorem boundaryArm_normal_ingoing (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    Tendsto (fun x => deriv (fun y => boundaryArm q branch v y X k) x) atBot (𝓝 0) := by
  have hc : Tendsto (fun x => -((2-capScale x:ℝ):ℂ)) atBot (𝓝 (-2:ℂ)) := by
    have hr : Tendsto (fun x => 2-capScale x) atBot (𝓝 (2:ℝ)) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := (2:ℝ))).sub capScale_ingoing
    simpa only [Complex.ofReal_ofNat,Function.comp_def] using! ((Complex.continuous_ofReal.tendsto (2:ℝ)).comp hr).neg
  have ht := hc.mul (normalArm_ingoing q branch v X k)
  simp only [(boundaryArm_normal_hasDerivAt q branch v _ X k).deriv]
  simpa only [mul_zero] using ht

/-- The original arm's time derivative retains its exact source contact on the horizon. -/
theorem boundaryArm_time_ingoing (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    Tendsto (fun x => deriv (fun w => boundaryArm q branch w x X k) v) atBot
      (𝓝 (-timeOnsetFirst (2*physicalRate q branch) v*fullSquarePotential q ![X,Real.exp k])) := by
  simpa only [(boundaryArm_time_hasDerivAt q branch v _ X k).deriv] using timeArm_ingoing q branch v X k

private theorem weightedArm_image_ingoing (q : XiZeroCopy) (branch normal : Bool) (v X k : ℝ) :
    Tendsto (fun x => weightedArm q branch normal (v-2*x) (-x) X k) atBot (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := weightedArm_bound q branch normal
  have ht : Tendsto (fun x : ℝ => (2*decayExponent q)*x) atBot atBot :=
    (tendsto_const_mul_atBot_of_pos (mul_pos (by norm_num : (0:ℝ)<2) (decay_pos q))).mpr tendsto_id
  have he := Real.tendsto_exp_atBot.comp ht
  have hbnd (x : ℝ) : ‖weightedArm q branch normal (v-2*x) (-x) X k‖ ≤
      (C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|))*Real.exp ((2*decayExponent q)*x) := by
    have h := hb (v-2*x) (-x) X k
    rw [show -decayExponent q*(v-2*x)+sourceGrowthExponent q*|k|=
      (-decayExponent q*v+sourceGrowthExponent q*|k|)+(2*decayExponent q)*x by ring,Real.exp_add] at h
    simpa only [mul_assoc] using h
  apply squeeze_zero_norm hbnd
  simpa only [Function.comp_def,id_eq,mul_zero] using
    he.const_mul (C*Real.exp (-decayExponent q*v+sourceGrowthExponent q*|k|))

/-- The differentiated image arm vanishes on the original ingoing horizon. -/
theorem timeArm_image_ingoing (q : XiZeroCopy) (branch : Bool) (v X k : ℝ) :
    Tendsto (fun x => timeArm q branch (v-2*x) (-x) X k) atBot (𝓝 0) :=
  weightedArm_image_ingoing q branch false v X k

/-- Both original cap arms contribute to its actual time derivative. -/
theorem capBoundaryField_time_hasDerivAt (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (τ x X k : ℝ) :
    HasDerivAt (fun t => capBoundaryField q branch amplitude t x X k)
      (-liftTraceCoefficient q branch amplitude*
        (timeArm q branch (τ+x) x X k-timeArm q branch (τ-x) (-x) X k)) τ := by
  have h0 := HasDerivAt.comp_const_add x τ (boundaryArm_time_hasDerivAt q branch (x+τ) x X k)
  have h1 := HasDerivAt.comp_const_add (-x) τ (boundaryArm_time_hasDerivAt q branch (-x+τ) (-x) X k)
  simpa only [capBoundaryField,sub_eq_add_neg,add_comm] using!
    (h0.sub h1).const_mul (-liftTraceCoefficient q branch amplitude)

/-- The full cap's actual time derivative has exactly the original lift's time contact. -/
theorem capBoundaryField_time_ingoing (q : XiZeroCopy) (branch : Bool) (amplitude : ℂ)
    (v X k : ℝ) :
    Tendsto (fun x => deriv (fun t => capBoundaryField q branch amplitude t x X k) (v-x)) atBot
      (𝓝 (liftTraceCoefficient q branch amplitude*timeOnsetFirst (2*physicalRate q branch) v*
        fullSquarePotential q ![X,Real.exp k])) := by
  have ht := ((timeArm_ingoing q branch v X k).sub (timeArm_image_ingoing q branch v X k)).const_mul
    (-liftTraceCoefficient q branch amplitude)
  have he (x : ℝ) : deriv (fun t => capBoundaryField q branch amplitude t x X k) (v-x)=
      -liftTraceCoefficient q branch amplitude*(timeArm q branch v x X k-
        timeArm q branch (v-2*x) (-x) X k) := by
    rw [(capBoundaryField_time_hasDerivAt q branch amplitude (v-x) x X k).deriv]
    rw [sub_add_cancel,show v-x-x=v-2*x by ring]
  simpa only [he,sub_zero,neg_mul,mul_neg,neg_neg,mul_assoc] using ht

end
end RHTower.D4BMCapNormalTrace
