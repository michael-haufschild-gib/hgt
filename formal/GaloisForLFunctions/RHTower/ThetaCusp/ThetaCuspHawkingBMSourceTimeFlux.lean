import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCommonSourceGreen

/-! Source-time integration of the actual signed characteristic radial face.
The full theta angular coefficient and original smooth onset are retained. -/

open Set Filter Topology MeasureTheory
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
namespace RHTower.D4BMSourceTimeFlux
open D4BMCommonSourceGreen D4BMJointSource D4BMLaplaceRadial
open D4BMModularCore D4BMGlobalAngularResponse

private def profile (s : ℂ) (u : ℝ) : ℂ :=
  (u:ℂ)^4*(1+(u:ℂ))*power (2*s) (1+u)

private def profileFirst (s : ℂ) (u : ℝ) : ℂ :=
  (u:ℂ)^3*(4+(2*s+5)*(u:ℂ))*power (2*s) (1+u)

private theorem profile_derivative (s : ℂ) {u : ℝ} (hu : 0 < 1+u) :
    HasDerivAt (profile s) (profileFirst s u) u := by
  have hi := (hasDerivAt_id u).ofReal_comp
  have ha : HasDerivAt (fun z : ℝ => 1+z) 1 u := by
    simpa only [id_eq] using! (hasDerivAt_id u).const_add 1
  have hp := (power_derivatives (2*s) hu).1.scomp u ha
  have hz : (1+(u:ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hu
  convert! (((hi.pow 4).mul (hi.const_add 1)).mul hp) using 1
  dsimp [profileFirst,powerFirst,Function.comp_def,id_eq]
  push_cast
  field_simp
  ring

private theorem profile_derivative_bound (q : XiZeroCopy) (branch : Bool)
    {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    ‖profileFirst (physicalRate q branch) u‖ ≤ 4+‖2*physicalRate q branch+5‖ := by
  have hr := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hr
  have hp : ‖power (2*physicalRate q branch) (1+u)‖ ≤ 1 := by
    rw [power,Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hu.1])]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [hu.1]) (by linarith)
  have hu' : ‖(u:ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hu.1] using hu.2
  have hp3 : ‖(u:ℂ)^3‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) hu'
  have hb : ‖(4:ℂ)+(2*physicalRate q branch+5)*(u:ℂ)‖ ≤
      4+‖2*physicalRate q branch+5‖ := by
    calc
      _ ≤ ‖(4:ℂ)‖+‖(2*physicalRate q branch+5)*(u:ℂ)‖ := norm_add_le _ _
      _ ≤ 4+‖2*physicalRate q branch+5‖ := by
        rw [norm_mul]
        norm_num only [Complex.norm_ofNat]
        linarith [mul_le_of_le_one_right (norm_nonneg (2*physicalRate q branch+5)) hu']
  unfold profileFirst
  rw [norm_mul,norm_mul]
  calc
    _ ≤ (1*(4+‖2*physicalRate q branch+5‖))*1 :=
      mul_le_mul (mul_le_mul hp3 hb (norm_nonneg _) (by norm_num)) hp
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem profile_lipschitz (q : XiZeroCopy) (branch : Bool)
    {u v : ℝ} (hu : u ∈ Icc (0:ℝ) 1) (hv : v ∈ Icc (0:ℝ) 1) :
    ‖profile (physicalRate q branch) u-profile (physicalRate q branch) v‖ ≤
      (4+‖2*physicalRate q branch+5‖)*‖u-v‖ := by
  apply (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z hz => (profile_derivative (physicalRate q branch) (by linarith [hz.1])).hasDerivWithinAt)
    (fun z hz => profile_derivative_bound q branch hz) hv hu

private theorem radialUnit_mem {y : ℝ} (hy : y ≤ 0) : radialUnit y ∈ Icc (0:ℝ) 1 := by
  rcases lt_or_eq_of_le hy with h | rfl
  · exact ⟨(radialUnit_bounds y h).1.le,(radialUnit_bounds y h).2.le⟩
  · simp [radialUnit]

private theorem radialUnit_horizon_bound {y : ℝ} (hy : y ≤ 0) :
    ‖radialUnit y-1‖ ≤ 2*Real.exp (2*y) := by
  have hu := radialUnit_mem hy
  rw [Real.norm_eq_abs,abs_of_nonpos (by linarith [hu.2])]
  calc
    _ = Real.exp (2*y)*(1+radialUnit y) := by
      convert radialUnit_one_sub y using 1
      ring
    _ ≤ Real.exp (2*y)*2 := mul_le_mul_of_nonneg_left (by linarith [hu.2]) (Real.exp_pos _).le
    _ = _ := by ring

private theorem weight_eq_profile (s : ℂ) (y : ℝ) :
    sourceCharacteristicWeight s y = profile s (radialUnit y) := by
  change ((radialUnit y:ℂ)^4*(1+(radialUnit y:ℂ)))*sourceAmplitude s 0 1 1 y = _
  simp [sourceAmplitude,profile]

/-- The actual characteristic weight difference has exponential delay decay,
uniform over all exterior target radii, for either physical Xi branch. -/
theorem sourceCharacteristicWeight_exp_bound (q : XiZeroCopy) (branch : Bool)
    (target : Iic (0:ℝ)) (h : Ici (0:ℝ)) :
    ‖sourceCharacteristicWeight (physicalRate q branch) (-h.val/2)-
      sourceCharacteristicWeight (physicalRate q branch) (target.val-h.val/2)‖ ≤
      4*(4+‖2*physicalRate q branch+5‖)*Real.exp (-h.val) := by
  have hh : 0 ≤ h.val := h.property
  have hx : target.val ≤ 0 := target.property
  have hi : -h.val/2 ≤ 0 := by linarith
  have hd : target.val-h.val/2 ≤ 0 := by linarith
  have hi' := radialUnit_horizon_bound hi
  have hd' := radialUnit_horizon_bound hd
  have he : Real.exp (2*(target.val-h.val/2)) ≤ Real.exp (-h.val) :=
    Real.exp_le_exp.mpr (by linarith)
  have hi'' : ‖radialUnit (-h.val/2)-1‖ ≤ 2*Real.exp (-h.val) := by
    have heq : 2*(-h.val/2) = -h.val := by ring
    simpa only [heq] using hi'
  have hd'' : ‖radialUnit (target.val-h.val/2)-1‖ ≤ 2*Real.exp (-h.val) :=
    hd'.trans (mul_le_mul_of_nonneg_left he (by norm_num))
  have hu : ‖radialUnit (-h.val/2)-radialUnit (target.val-h.val/2)‖ ≤
      4*Real.exp (-h.val) := by
    calc
      _ ≤ ‖radialUnit (-h.val/2)-1‖+‖1-radialUnit (target.val-h.val/2)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ = ‖radialUnit (-h.val/2)-1‖+‖radialUnit (target.val-h.val/2)-1‖ := by rw [norm_sub_rev 1]
      _ ≤ _ := by linarith
  rw [weight_eq_profile,weight_eq_profile]
  calc
    _ ≤ (4+‖2*physicalRate q branch+5‖)*
        ‖radialUnit (-h.val/2)-radialUnit (target.val-h.val/2)‖ :=
      profile_lipschitz q branch (radialUnit_mem hi) (radialUnit_mem hd)
    _ ≤ (4+‖2*physicalRate q branch+5‖)*(4*Real.exp (-h.val)) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = _ := by ring

private theorem onset_bound (q : XiZeroCopy) (branch : Bool) {v : ℝ} (hv : 0 ≤ v) :
    ‖timeOnset (2*physicalRate q branch) v‖ ≤ Real.exp (-2*v) := by
  have hr := currentRate_re_lt q branch
  change (2*physicalRate q branch).re < -2 at hr
  have hc : ‖(Real.smoothTransition v:ℂ)‖ ≤ 1 := by
    simpa [Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.smoothTransition.nonneg v)] using Real.smoothTransition.le_one v
  have he : ‖Complex.exp ((2*physicalRate q branch)*(v:ℂ))‖ ≤ Real.exp (-2*v) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simpa using mul_le_mul_of_nonneg_right hr.le hv
  unfold timeOnset
  rw [norm_mul]
  exact (mul_le_mul hc he (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- The original four radial faces, with their direct-minus-image signs. -/
def signedRadialFace (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v h target X k : ℝ) : ℂ :=
  (sourceRadialTraceCurrent q branch a v false h target X k 0-
    sourceRadialTraceCurrent q branch a v false h target X k
      (sourceCharacteristic false h target))-
  (sourceRadialTraceCurrent q branch a v true h target X k 0-
    sourceRadialTraceCurrent q branch a v true h target X k
      (sourceCharacteristic true h target))

/-- Source-time integral over the actual causal interval at target ingoing time `T`. -/
def sourceTimeRadialFlux (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (target X k T : ℝ) : ℂ :=
  ∫ v in (0:ℝ)..T, signedRadialFace q branch a v (T-v) target X k

private theorem signedRadialFace_eq (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v h target X k : ℝ) :
    signedRadialFace q branch a v h target X k =
      (Complex.exp (-(k:ℂ))*a^2*thetaAngularCoupling q X k)*
        timeOnset (2*physicalRate q branch) v*
        (sourceCharacteristicWeight (physicalRate q branch) (-h/2)-
          sourceCharacteristicWeight (physicalRate q branch) (target-h/2)) := by
  rw [signedRadialFace,sourceRadialTraceCurrent_signed_faces]
  ring

private theorem weight_continuous (s : ℂ) : Continuous (sourceCharacteristicWeight s) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  have he : sourceCharacteristicWeight s = fun y => profile s (radialUnit y) :=
    funext (weight_eq_profile s)
  rw [he]
  exact ((profile_derivative s (radialUnit_add_one_pos y)).scomp y
    (radialUnit_hasDerivAt y)).continuousAt

private theorem signedRadialFace_continuous (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (target X k T : ℝ) :
    Continuous (fun v => signedRadialFace q branch a v (T-v) target X k) := by
  simp_rw [signedRadialFace_eq]
  have ho : Continuous (timeOnset (2*physicalRate q branch)) :=
    continuous_iff_continuousAt.mpr (fun v => (timeOnset_hasDerivAt _ v).continuousAt)
  exact (continuous_const.mul ho).mul
    (((weight_continuous _).comp ((continuous_const.sub continuous_id).neg.div_const 2)).sub
      ((weight_continuous _).comp
        (continuous_const.sub ((continuous_const.sub continuous_id).div_const 2))))

/-- The original source-time integrand is genuinely integrable at every finite time. -/
theorem sourceTimeRadialFlux_integrable (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (target X k T : ℝ) :
    IntervalIntegrable (fun v => signedRadialFace q branch a v (T-v) target X k)
      volume 0 T :=
  (signedRadialFace_continuous q branch a target X k T).intervalIntegrable _ _

/-- Exact source-time convolution, retaining the full angular coupling, branch,
amplitude and original smooth onset. -/
theorem sourceTimeRadialFlux_eq (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (target X k T : ℝ) :
    sourceTimeRadialFlux q branch a target X k T =
      ∫ v in (0:ℝ)..T,
        (Complex.exp (-(k:ℂ))*a^2*thetaAngularCoupling q X k)*
          timeOnset (2*physicalRate q branch) v*
          (sourceCharacteristicWeight (physicalRate q branch) (-(T-v)/2)-
            sourceCharacteristicWeight (physicalRate q branch) (target-(T-v)/2)) := by
  unfold sourceTimeRadialFlux
  simp_rw [signedRadialFace_eq]

/-- Explicit bound coefficient of the retained radial face. It is independent
of both target radius and target time. -/
def sourceTimeFluxBound (q : XiZeroCopy) (branch : Bool) (a : ℂ) (X k : ℝ) : ℝ :=
  ‖Complex.exp (-(k:ℂ))*a^2*thetaAngularCoupling q X k‖*
    (4*(4+‖2*physicalRate q branch+5‖))

private theorem fluxBound_nonneg (q : XiZeroCopy) (branch : Bool) (a : ℂ) (X k : ℝ) :
    0 ≤ sourceTimeFluxBound q branch a X k := by unfold sourceTimeFluxBound; positivity

private theorem face_bound (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (target : Iic (0:ℝ)) (X k T v : ℝ) (hv : v ∈ Icc 0 T) :
    ‖signedRadialFace q branch a v (T-v) target.val X k‖ ≤
      sourceTimeFluxBound q branch a X k*Real.exp (-T)*Real.exp (-v) := by
  have hw := sourceCharacteristicWeight_exp_bound q branch target ⟨T-v,show 0 ≤ T-v from sub_nonneg.mpr hv.2⟩
  have ho := onset_bound q branch hv.1
  rw [signedRadialFace_eq,norm_mul,norm_mul]
  calc
    _ ≤ (‖Complex.exp (-(k:ℂ))*a^2*thetaAngularCoupling q X k‖*Real.exp (-2*v))*
        (4*(4+‖2*physicalRate q branch+5‖)*Real.exp (-(T-v))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left ho (norm_nonneg _)) hw
        (norm_nonneg _) (by positivity)
    _ = _ := by
      have he : Real.exp (-2*v)*Real.exp (-(T-v)) = Real.exp (-T)*Real.exp (-v) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      dsimp [sourceTimeFluxBound]
      linear_combination ‖Complex.exp (-(k:ℂ))*a^2*thetaAngularCoupling q X k‖*
        (4*(4+‖2*physicalRate q branch+5‖))*he

private theorem integral_exp_neg (T : ℝ) :
    ∫ v in (0:ℝ)..T, Real.exp (-v) = 1-Real.exp (-T) := by
  have hi : IntervalIntegrable (fun v : ℝ => Real.exp (-v)) volume 0 T :=
    (Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _
  have hd : ∀ v ∈ uIcc (0:ℝ) T,
      HasDerivAt (fun v : ℝ => -Real.exp (-v)) (Real.exp (-v)) v := by
    intro v _
    simpa using! (((hasDerivAt_id v).neg.exp).neg)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  simp only [neg_zero,Real.exp_zero] at he
  linarith

/-- The actual radial characteristic face, integrated over all causal source
times, decays at least as `exp(-T)`, uniformly over exterior target radii. -/
theorem sourceTimeRadialFlux_exp_bound (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (target : Iic (0:ℝ)) (X k : ℝ) (T : Ici (0:ℝ)) :
    ‖sourceTimeRadialFlux q branch a target.val X k T.val‖ ≤
      sourceTimeFluxBound q branch a X k*Real.exp (-T.val) := by
  have hi : IntervalIntegrable (fun v : ℝ =>
      sourceTimeFluxBound q branch a X k*Real.exp (-T.val)*Real.exp (-v)) volume 0 T.val :=
    (continuous_const.mul (Real.continuous_exp.comp continuous_neg)).intervalIntegrable _ _
  have hb := intervalIntegral.norm_integral_le_of_norm_le T.property
    (Filter.Eventually.of_forall (fun v (hv : v ∈ Ioc (0:ℝ) T.val) =>
      face_bound q branch a target X k T.val v ⟨hv.1.le,hv.2⟩)) hi
  change ‖sourceTimeRadialFlux q branch a target.val X k T.val‖ ≤ _ at hb
  rw [intervalIntegral.integral_const_mul,integral_exp_neg] at hb
  exact hb.trans (mul_le_of_le_one_right
    (mul_nonneg (fluxBound_nonneg q branch a X k) (Real.exp_pos _).le)
    (by linarith [Real.exp_pos (-T.val)]))

/-- The time-integrated radial face vanishes along every exterior target-radius
path. No regularity or endpoint assumption on that path is needed, because the
exponential bound is uniform in radius. -/
theorem sourceTimeRadialFlux_tendsto_zero (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (target : ℝ → Iic (0:ℝ)) (X k : ℝ) :
    Tendsto (fun T => sourceTimeRadialFlux q branch a (target T).val X k T)
      atTop (𝓝 (0:ℂ)) := by
  have he := (Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul
    (sourceTimeFluxBound q branch a X k)
  apply squeeze_zero_norm' _ (by simpa using he)
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  exact sourceTimeRadialFlux_exp_bound q branch a (target T) X k ⟨T,hT⟩

end RHTower.D4BMSourceTimeFlux
