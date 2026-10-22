import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSpinTwoDelayCharacteristic
import GaloisForLFunctions.HTGeometry.ClockParametricDerivative

/-! Uniform geometry of the original full-source finite-delay transfer. -/
namespace RHTower.D4BMSpinTwoUniformDelay
open D4BMSpinTwoDelay D4BMNativeSpinTwoPrimitive D4BMCausalKernel D4BMModularCore
open D4BMHorizon D4BMJointSource Set Filter Topology MeasureTheory
open scoped ContDiff
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- The normalized primitive slope in the original causal kernel. -/
def primitiveRatio (p : CausalPoint) : ℝ :=
  (invariant p.time p.target p.source-1)/invariantTimeFirst p.time p.target p.source
/-- The normalized acceleration coefficient in the original causal kernel. -/
def accelerationRatio (p : CausalPoint) : ℝ :=
  invariantTimeSecond p.time p.target p.source*(invariant p.time p.target p.source-1)/
    (invariantTimeFirst p.time p.target p.source)^(2 : ℕ)

private theorem ratio_forms (p : CausalPoint) :
    primitiveRatio p=(Real.cosh p.time-Real.cosh (p.target-p.source))/Real.sinh p.time ∧
    accelerationRatio p=Real.cosh p.time*(Real.cosh p.time-Real.cosh (p.target-p.source))/
      (Real.sinh p.time)^(2 : ℕ) := by
  have hd := (mul_pos (Real.cosh_pos p.target) (Real.cosh_pos p.source)).ne'
  by_cases hs : Real.sinh p.time=0
  · simp [primitiveRatio,accelerationRatio,invariantTimeFirst,hs]
  · dsimp [primitiveRatio,accelerationRatio,invariant,invariantTimeFirst,invariantTimeSecond]
    rw [Real.cosh_sub]
    constructor <;> field_simp [hd,hs] <;> ring

private theorem scalar_bounds (c s e : ℝ) (hc : 1 ≤ c) (hs : 0 < s)
    (he : 1 ≤ e) (hec : e ≤ c) (hcs : c^(2 : ℕ)-s^(2 : ℕ)=1) :
    0 ≤ (c-e)/s ∧ (c-e)/s ≤ 1 ∧
    0 ≤ c*(c-e)/s^(2 : ℕ) ∧ c*(c-e)/s^(2 : ℕ) ≤ 1 ∧
    0 ≤ 3*(c*(c-e)/s^(2 : ℕ))^(2 : ℕ)-((c-e)/s)^(2 : ℕ) ∧
    3*(c*(c-e)/s^(2 : ℕ))^(2 : ℕ)-((c-e)/s)^(2 : ℕ) ≤ 2 := by
  have hc0 : 0 < c := by linarith
  have hs2 : 0 < s^(2 : ℕ) := sq_pos_of_pos hs
  have hs4 : 0 < s^(4 : ℕ) := pow_pos hs 4
  have hce : 0 ≤ c-e := sub_nonneg.mpr hec
  have hcle : c-e ≤ c-1 := by linarith
  have hcs2 : s^(2 : ℕ)=(c-1)*(c+1) := by nlinarith
  have hsmall : c-1 ≤ s := by nlinarith [sq_nonneg (c-1-s)]
  have hthird : 3*(c*(c-e)/s^(2 : ℕ))^(2 : ℕ)-((c-e)/s)^(2 : ℕ)=
      (2*c^(2 : ℕ)+1)*(c-e)^(2 : ℕ)/s^(4 : ℕ) := by
    field_simp [hs.ne']
    nlinarith [hcs]
  have hcSq : (c-e)^(2 : ℕ) ≤ (c-1)^(2 : ℕ) := by nlinarith
  have hfour : s^(4 : ℕ)=(c-1)^(2 : ℕ)*(c+1)^(2 : ℕ) := by nlinarith [sq_nonneg (s^(2 : ℕ)-(c-1)*(c+1))]
  refine ⟨div_nonneg hce hs.le, (div_le_one hs).mpr (hcle.trans hsmall),
    div_nonneg (mul_nonneg hc0.le hce) hs2.le, ?_, ?_, ?_⟩
  · apply (div_le_one hs2).mpr
    nlinarith
  · rw [hthird]
    positivity
  · rw [hthird]
    apply (div_le_iff₀ hs4).mpr
    have hfactor : 0 ≤ 2*c^(2 : ℕ)+1 := by positivity
    have hprod := mul_le_mul_of_nonneg_left hcSq hfactor
    have hlast : (2*c^(2 : ℕ)+1)*(c-1)^(2 : ℕ) ≤ 2*((c-1)^(2 : ℕ)*(c+1)^(2 : ℕ)) := by
      nlinarith [mul_nonneg (sq_nonneg (c-1)) (show 0 ≤ 4*c+1 by linarith)]
    rw [hfour]
    exact hprod.trans hlast

/-- Uniform bounds for all three original bulk coefficients on the entire closed causal cone. -/
theorem causal_coefficient_bounds (p : CausalPoint) :
    0 ≤ primitiveRatio p ∧ primitiveRatio p ≤ 1 ∧
    0 ≤ accelerationRatio p ∧ accelerationRatio p ≤ 1 ∧
    0 ≤ 3*(accelerationRatio p)^(2 : ℕ)-(primitiveRatio p)^(2 : ℕ) ∧
    3*(accelerationRatio p)^(2 : ℕ)-(primitiveRatio p)^(2 : ℕ) ≤ 2 := by
  have ht : 0 ≤ p.time := (abs_nonneg _).trans p.inside
  obtain ⟨hr,hb⟩ := ratio_forms p
  rw [hr,hb]
  rcases eq_or_lt_of_le ht with he | hp
  · rw [← he]
    simp
  · apply scalar_bounds _ _ _ (Real.one_le_cosh _) (Real.sinh_pos_iff.mpr hp)
      (Real.one_le_cosh _)
    · exact Real.cosh_le_cosh.mpr (by simpa only [abs_of_nonneg ht] using p.inside)
    · exact Real.cosh_sq_sub_sinh_sq p.time

private def reflected (image : Bool) (y : ℝ) := if image then -y else y

/-- The original radius-frozen delay point, with its actual direct/image causal domain. -/
def physicalPoint (image : Bool) (x y : Iic (0:ℝ))
    (h : Ici (causalDelayStart image x y)) : CausalPoint where
  time := h-x+y
  target := x
  source := reflected image y
  inside := by
    have hh : causalDelayStart image x y ≤ h.val := h.property
    have hx : x.val ≤ 0 := x.property
    have hy : y.val ≤ 0 := y.property
    cases image
    · change |x.val-y.val| ≤ h.val-x.val+y.val
      change 2*max (x.val-y.val) 0 ≤ h.val at hh
      have hm := le_max_left (x.val-y.val) 0
      have hm0 := le_max_right (x.val-y.val) 0
      exact abs_le.mpr ⟨by linarith,by linarith⟩
    · change |x.val-(-y.val)| ≤ h.val-x.val+y.val
      rw [sub_neg_eq_add]
      change -2*y.val ≤ h.val at hh
      rw [abs_of_nonpos (show x.val+y.val ≤ 0 by linarith)]
      linarith

private abbrev W (q : XiZeroCopy) (branch : Bool) (x y V : ℝ) :=
  clockDensity q branch (radialUnit x) (radialUnit y) V

private theorem normalized_algebra (j u a b w0 w1 w2 : ℂ) :
    j^(2 : ℕ)*u*(w2/a^(2 : ℕ)-3*b*w1/a^(3 : ℕ)+(3*b^(2 : ℕ)-a^(2 : ℕ))*w0/a^(4 : ℕ))=
    u*((j/a)^(2 : ℕ)*w2-3*(j/a)*(b*j/a^(2 : ℕ))*w1+(3*(b*j/a^(2 : ℕ))^(2 : ℕ)-(j/a)^(2 : ℕ))*w0) := by
  by_cases ha : a=0
  · simp [ha]
  · field_simp [ha]

/-- The literal full-source bulk factors through uniformly bounded geometric coefficients. -/
theorem delay_bulk_normalized (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (x y : Iic (0:ℝ)) (V X k : ℝ) (h : Ici (causalDelayStart image x y)) :
    delayBulk image q branch x y V X k h=
      secondMoment q X k (delayArgument image x y h)*
        ((primitiveRatio (physicalPoint image x y h):ℂ)^(2 : ℕ)*deriv (deriv (W q branch x y V)) h-
          3*(primitiveRatio (physicalPoint image x y h):ℂ)*
            (accelerationRatio (physicalPoint image x y h):ℂ)*deriv (W q branch x y V) h+
          (3*(accelerationRatio (physicalPoint image x y h):ℂ)^(2 : ℕ)-
            (primitiveRatio (physicalPoint image x y h):ℂ)^(2 : ℕ))*W q branch x y V h) := by
  let p := physicalPoint image x y h
  have hz : 1 ≤ delayArgument image x y h := invariant_causal p
  have hJ := (primitive_factor q X k ⟨delayArgument image x y h,hz⟩).1
  change primitive q X k (delayArgument image x y h)=(delayArgument image x y h-1:ℂ)^(2 : ℕ)*_
    at hJ
  change primitive q X k (delayArgument image x y h)*
    (deriv (deriv (W q branch x y V)) h/(delaySlope image x y h:ℂ)^(2 : ℕ)-
      3*(invariantTimeSecond (h-x+y) x (reflected image y):ℂ)*deriv (W q branch x y V) h/
        (delaySlope image x y h:ℂ)^(3 : ℕ)+
      (3*(invariantTimeSecond (h-x+y) x (reflected image y):ℂ)^(2 : ℕ)-(delaySlope image x y h:ℂ)^(2 : ℕ))*
        W q branch x y V h/(delaySlope image x y h:ℂ)^(4 : ℕ))=_
  rw [hJ]
  simp only [primitiveRatio,accelerationRatio,physicalPoint,Complex.ofReal_div,Complex.ofReal_sub,
    Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_one]
  exact normalized_algebra _ _ _ _ _ _ _

private theorem norm_normalized_le (r b : ℝ) (w0 w1 w2 : ℂ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ 3*b^(2 : ℕ)-r^(2 : ℕ)) (hc1 : 3*b^(2 : ℕ)-r^(2 : ℕ) ≤ 2) :
    ‖(r:ℂ)^(2 : ℕ)*w2-3*(r:ℂ)*(b:ℂ)*w1+(3*(b:ℂ)^(2 : ℕ)-(r:ℂ)^(2 : ℕ))*w0‖ ≤
      ‖w2‖+3*‖w1‖+2*‖w0‖ := by
  have h1 : ‖(r:ℂ)^(2 : ℕ)‖ ≤ 1 := by
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0]
    nlinarith
  have h2 : ‖(3:ℂ)*(r:ℂ)*(b:ℂ)‖ ≤ 3 := by
    rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,
      Real.norm_eq_abs,abs_of_nonneg hr0,abs_of_nonneg hb0]
    norm_num
    nlinarith [mul_le_mul hr1 hb1 hb0 (by norm_num : (0:ℝ) ≤ 1)]
  have h3 : ‖(3:ℂ)*(b:ℂ)^(2 : ℕ)-(r:ℂ)^(2 : ℕ)‖ ≤ 2 := by
    have he : (3:ℂ)*(b:ℂ)^(2 : ℕ)-(r:ℂ)^(2 : ℕ)=((3*b^(2 : ℕ)-r^(2 : ℕ):ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc0]
    exact hc1
  calc
    _ ≤ ‖(r:ℂ)^(2 : ℕ)*w2‖+‖3*(r:ℂ)*(b:ℂ)*w1‖+‖(3*(b:ℂ)^(2 : ℕ)-(r:ℂ)^(2 : ℕ))*w0‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ 1*‖w2‖+3*‖w1‖+2*‖w0‖ := by
      simp only [norm_mul] at h1 h2 h3 ⊢
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)))
        (mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
    _ = _ := by ring

/-- Radius-independent geometric domination of the ORIGINAL finite-clock source bulk,
including every closed characteristic and approach to the horizon. -/
theorem delay_bulk_bound (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (x y : Iic (0:ℝ)) (V X k : ℝ) (h : Ici (causalDelayStart image x y)) :
    ‖delayBulk image q branch x y V X k h‖ ≤
      ‖secondMoment q X k (delayArgument image x y h)‖*
        (‖deriv (deriv (W q branch x y V)) h‖+
          3*‖deriv (W q branch x y V) h‖+2*‖W q branch x y V h‖) := by
  rw [delay_bulk_normalized,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := causal_coefficient_bounds (physicalPoint image x y h)
  exact norm_normalized_le _ _ _ _ _ h0 h1 h2 h3 h4 h5

private theorem radial_mem (x : Iic (0:ℝ)) : radialUnit x ∈ Icc (0:ℝ) 1 := by
  rcases lt_or_eq_of_le (show x.val ≤ 0 from x.property) with h | h
  · exact ⟨(radialUnit_bounds x h).1.le,(radialUnit_bounds x h).2.le⟩
  · simp [h,radialUnit]

/-- Exact compact-radius expression for the original direct/image delay invariant. -/
theorem delay_invariant_formula (image : Bool) (x y h : ℝ) :
    delayArgument image x y h=
      Real.cosh h*(1-radialUnit x*radialUnit y)+
      Real.sinh h*(radialUnit x-radialUnit y)+
      (if image then -(radialUnit x*radialUnit y) else radialUnit x*radialUnit y) := by
  change (Real.cosh (h-x+y)+Real.sinh x*Real.sinh (if image then -y else y))/
    (Real.cosh x*Real.cosh (if image then -y else y))=_
  rw [show h-x+y=h-(x-y) by ring,Real.cosh_sub,Real.cosh_sub,Real.sinh_sub]
  have hx := (Real.cosh_pos x).ne'
  have hy := (Real.cosh_pos y).ne'
  cases image <;> simp only [Bool.false_eq_true,if_false,if_true,Real.cosh_neg,Real.sinh_neg,radialUnit]
  all_goals field_simp [hx,hy]; ring

/-- The original invariant stays in a delay-controlled compact interval uniformly in both radii. -/
theorem delay_invariant_bounds (image : Bool) (x y : Iic (0:ℝ))
    (h : Ici (causalDelayStart image x y)) :
    1 ≤ delayArgument image x y h ∧ delayArgument image x y h ≤ Real.exp h := by
  refine ⟨invariant_causal (physicalPoint image x y h),?_⟩
  have hx := radial_mem x
  have hy := radial_mem y
  have hh : 0 ≤ h.val := (causalDelayStart_nonneg image x y).trans h.property
  have hs : 0 ≤ Real.sinh h := Real.sinh_nonneg_iff.mpr hh
  have hc : 0 ≤ Real.cosh h-1 := sub_nonneg.mpr (Real.one_le_cosh h)
  have huw := mul_nonneg hx.1 hy.1
  have hdiff : radialUnit x-radialUnit y ≤ 1 := by linarith [hx.2,hy.1]
  have ht := mul_le_mul_of_nonneg_left hdiff hs
  have hp := mul_nonneg hc huw
  rw [delay_invariant_formula,← Real.cosh_add_sinh h]
  cases image <;> simp only [Bool.false_eq_true,if_false,if_true] <;> nlinarith

/-- One finite invariant interval contains every original causal point in a finite delay window. -/
theorem delay_invariant_finite_range (image : Bool) (x y : Iic (0:ℝ)) (V : ℝ)
    (h : Icc (causalDelayStart image x y) V) :
    delayArgument image x y h ∈ Icc (1:ℝ) (Real.exp V) := by
  obtain ⟨h0,h1⟩ := delay_invariant_bounds image x y ⟨h,h.property.1⟩
  exact ⟨h0,h1.trans (Real.exp_le_exp.mpr h.property.2)⟩

/-- Both exact original source moments have one bound on a finite invariant interval. -/
theorem source_moments_bounded (q : XiZeroCopy) (X k : ℝ) (R : Ici (1:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Icc (1:ℝ) R.val,
      ‖firstMoment q X k z‖ ≤ C ∧ ‖secondMoment q X k z‖ ≤ C := by
  obtain ⟨B,hB,hbound⟩ := primitive_characteristic_bounds q X k R
  let C := B+‖firstMoment q X k 1‖+‖secondMoment q X k 1‖
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro z
  rcases eq_or_lt_of_le z.property.1 with hz | hz
  · rw [← hz]
    constructor <;> dsimp [C] <;> nlinarith [norm_nonneg (firstMoment q X k 1),norm_nonneg (secondMoment q X k 1)]
  · obtain ⟨hb0,hb1⟩ := hbound z
    obtain ⟨hf0,hf1⟩ := primitive_factor q X k ⟨z,z.property.1⟩
    change primitive q X k z.val=(z.val-1:ℂ)^(2 : ℕ)*secondMoment q X k z.val at hf0
    change primitiveFirst q X k z.val=(z.val-1:ℂ)*firstMoment q X k z.val at hf1
    rw [hf0,norm_mul,norm_pow,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hz)] at hb0
    rw [hf1,norm_mul,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr hz)] at hb1
    have h0 : ‖secondMoment q X k z‖ ≤ B := by
      nlinarith [sq_pos_of_pos (sub_pos.mpr hz)]
    have h1 : ‖firstMoment q X k z‖ ≤ B := by nlinarith
    have hBC : B ≤ C := by
      dsimp [C]
      linarith [norm_nonneg (firstMoment q X k 1),norm_nonneg (secondMoment q X k 1)]
    exact ⟨h1.trans hBC,h0.trans hBC⟩

/-- Actual finite-delay source moments are uniformly bounded over both full physical radial domains. -/
theorem finite_delay_source_moments (q : XiZeroCopy) (X k : ℝ) (V : Ici (0:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (image : Bool) (x y : Iic (0:ℝ))
      (h : Icc (causalDelayStart image x y) V.val),
      ‖firstMoment q X k (delayArgument image x y h)‖ ≤ C ∧
      ‖secondMoment q X k (delayArgument image x y h)‖ ≤ C := by
  have hV : 1 ≤ Real.exp V := Real.one_le_exp_iff.mpr V.property
  obtain ⟨C,hC,hbound⟩ := source_moments_bounded q X k ⟨Real.exp V,hV⟩
  exact ⟨C,hC,fun image x y h => hbound ⟨_,delay_invariant_finite_range image x y V h⟩⟩

/-- The full finite-delay bulk has a uniform radial bound by the actual original clock jets. -/
theorem finite_delay_bulk_clock_bound (q : XiZeroCopy) (branch : Bool) (X k : ℝ)
    (V : Ici (0:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (image : Bool) (x y : Iic (0:ℝ))
      (h : Icc (causalDelayStart image x y) V.val),
      ‖delayBulk image q branch x y V X k h‖ ≤ C*
        (‖deriv (deriv (clockDensity q branch (radialUnit x) (radialUnit y) V)) h‖+
          3*‖deriv (clockDensity q branch (radialUnit x) (radialUnit y) V) h‖+
          2*‖clockDensity q branch (radialUnit x) (radialUnit y) V h‖) := by
  obtain ⟨C,hC,hbound⟩ := finite_delay_source_moments q X k V
  refine ⟨C,hC,?_⟩
  intro image x y h
  exact (delay_bulk_bound image q branch x y V X k ⟨h,h.property.1⟩).trans
    (mul_le_mul_of_nonneg_right (hbound image x y h).2 (by positivity))

private abbrev ClockPoint := (ℝ × ℝ) × ℝ
private abbrev KernelPoint := ClockPoint × ℝ
private def scaledProfile (s : ℂ) (u v : ℝ) : ℂ :=
  Complex.exp (2*s*(v:ℂ))*((2*s+1)*(2*s+2)*(1+(u:ℂ))*(Real.smoothTransition v:ℂ)-
    s*(s-1)/2*(u:ℂ)*(3+(2*s+3)*(u:ℂ))*((deriv Real.smoothTransition v:ℝ):ℂ))

private theorem scaledProfile_smooth (s : ℂ) :
    ContDiff ℝ ∞ (fun p : ℝ × ℝ => scaledProfile s p.1 p.2) := by
  have hc : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (Real.smoothTransition p.2:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp contDiff_snd)
  have hd : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ((deriv Real.smoothTransition p.2:ℝ):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (((contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2).comp contDiff_snd)
  have hu : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (p.1:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_fst
  have he : ContDiff ℝ ∞ (fun p : ℝ × ℝ => Complex.exp (2*s*(p.2:ℂ))) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd)).cexp
  have ha : ContDiff ℝ ∞ (fun p : ℝ × ℝ => (2*s+1)*(2*s+2)*(1+(p.1:ℂ))) :=
    contDiff_const.mul (contDiff_const.add hu)
  have hb : ContDiff ℝ ∞ (fun p : ℝ × ℝ => s*(s-1)/2*(p.1:ℂ)*(3+(2*s+3)*(p.1:ℂ))) :=
    (contDiff_const.mul hu).mul (contDiff_const.add (contDiff_const.mul hu))
  exact he.mul ((ha.mul hc).sub (hb.mul hd))

private def clockKernel (q : XiZeroCopy) (branch : Bool) (V : ℝ) (p : KernelPoint) : ℂ :=
  scaledProfile (physicalRate q branch) p.1.1.1 (p.1.2+(V-p.1.2)*p.2)*
    scaledProfile (-physicalRate q branch-3) p.1.1.2 ((V-p.1.2)*p.2)
private def partialClock (f : KernelPoint → ℂ) (p : KernelPoint) : ℂ :=
  fderiv ℝ f p (((0,0),1),0)
private def kernelJet (q : XiZeroCopy) (branch : Bool) (V : ℝ) : ℕ → KernelPoint → ℂ
  | 0 => clockKernel q branch V
  | n+1 => partialClock (kernelJet q branch V n)

private theorem kernel_smooth (q : XiZeroCopy) (branch : Bool) (V : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (kernelJet q branch V n) := by
  induction n with
  | zero =>
    exact ((scaledProfile_smooth (physicalRate q branch)).comp
      (show ContDiff ℝ ∞ (fun p : KernelPoint => (p.1.1.1,p.1.2+(V-p.1.2)*p.2)) by fun_prop)).mul
      ((scaledProfile_smooth (-physicalRate q branch-3)).comp
      (show ContDiff ℝ ∞ (fun p : KernelPoint => (p.1.1.2,(V-p.1.2)*p.2)) by fun_prop))
  | succ n ih =>
    exact (ih.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

private def clockIntegralJet (q : XiZeroCopy) (branch : Bool) (V : ℝ) (n : ℕ) (p : ClockPoint) : ℂ :=
  ∫ t in (0:ℝ)..1, kernelJet q branch V n (p,t)
private theorem integralJet_continuous (q : XiZeroCopy) (branch : Bool) (V : ℝ) (n : ℕ) :
    Continuous (clockIntegralJet q branch V n) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (f := fun p t => kernelJet q branch V n (p,t))
    (kernel_smooth q branch V n).continuous continuous_const

private theorem integralJet_derivative (q : XiZeroCopy) (branch : Bool) (V : ℝ) (n : ℕ)
    (u w h : ℝ) :
    HasDerivAt (fun r => clockIntegralJet q branch V n ((u,w),r))
      (clockIntegralJet q branch V (n+1) ((u,w),h)) h := by
  change HasDerivAt (fun r => ∫ t in (0:ℝ)..1, kernelJet q branch V n (((u,w),r),t))
    (∫ t in (0:ℝ)..1, kernelJet q branch V (n+1) (((u,w),h),t)) h
  refine GaloisForLFunctions.HTGeometry.hasDerivAt_parametric_intervalIntegral
    (f := fun r t => kernelJet q branch V n (((u,w),r),t))
    (f' := fun r t => kernelJet q branch V (n+1) (((u,w),r),t)) ?_ ?_ ?_ 0 1 h
  · exact (kernel_smooth q branch V n).continuous.comp
      (show Continuous (fun p : ℝ × ℝ => (((u,w),p.1),p.2)) by fun_prop)
  · exact (kernel_smooth q branch V (n+1)).continuous.comp
      (show Continuous (fun p : ℝ × ℝ => (((u,w),p.1),p.2)) by fun_prop)
  · intro r t
    have hm : HasDerivAt (fun h : ℝ => (((u,w),h),t)) (((0,0),1),0) r :=
      ((hasDerivAt_const r (u,w)).prodMk (hasDerivAt_id r)).prodMk (hasDerivAt_const r t)
    exact ((kernel_smooth q branch V n).differentiable (by simp) (((u,w),r),t)).hasFDerivAt.comp_hasDerivAt r hm

private def scaledClockZero (q : XiZeroCopy) (branch : Bool) (V : ℝ) (p : ClockPoint) : ℂ :=
  (V-p.2:ℂ)*clockIntegralJet q branch V 0 p
private def scaledClockFirst (q : XiZeroCopy) (branch : Bool) (V : ℝ) (p : ClockPoint) : ℂ :=
  -clockIntegralJet q branch V 0 p+(V-p.2:ℂ)*clockIntegralJet q branch V 1 p
private def scaledClockSecond (q : XiZeroCopy) (branch : Bool) (V : ℝ) (p : ClockPoint) : ℂ :=
  -2*clockIntegralJet q branch V 1 p+(V-p.2:ℂ)*clockIntegralJet q branch V 2 p

private theorem scaledClock_continuous (q : XiZeroCopy) (branch : Bool) (V : ℝ) :
    Continuous (scaledClockZero q branch V) ∧ Continuous (scaledClockFirst q branch V) ∧
      Continuous (scaledClockSecond q branch V) := by
  have h0 := integralJet_continuous q branch V 0
  have h1 := integralJet_continuous q branch V 1
  have h2 := integralJet_continuous q branch V 2
  have hv : Continuous (fun p : ClockPoint => (V-p.2:ℂ)) := by fun_prop
  exact ⟨hv.mul h0,h0.neg.add (hv.mul h1),(continuous_const.mul h1).add (hv.mul h2)⟩

private theorem scaledClock_derivatives (q : XiZeroCopy) (branch : Bool) (V u w h : ℝ) :
    HasDerivAt (fun r => scaledClockZero q branch V ((u,w),r))
      (scaledClockFirst q branch V ((u,w),h)) h ∧
    HasDerivAt (fun r => scaledClockFirst q branch V ((u,w),r))
      (scaledClockSecond q branch V ((u,w),h)) h := by
  have hv : HasDerivAt (fun r : ℝ => (V-r:ℂ)) (-1) h :=
    ((hasDerivAt_id h).ofReal_comp).const_sub (V:ℂ)
  have h0 := integralJet_derivative q branch V 0 u w h
  have h1 := integralJet_derivative q branch V 1 u w h
  constructor
  · apply (hv.mul h0).congr_deriv
    simp only [scaledClockFirst,neg_one_mul]
  · apply (h0.neg.add (hv.mul h1)).congr_deriv
    dsimp [scaledClockSecond]
    ring

private theorem scaledProfile_original (s : ℂ) (u : Icc (0:ℝ) 1) (v : ℝ) :
    scaledProfile s u v=(1+(u.val:ℂ))*clockProfile s u v := by
  have hu : 1+(u.val:ℂ) ≠ 0 := by
    exact_mod_cast (show (1:ℝ)+u.val ≠ 0 by linarith [u.property.1])
  dsimp [scaledProfile,clockProfile]
  field_simp [hu]

private def clockDenominator (p : ClockPoint) : ℂ := (1+(p.1.1:ℂ))*(1+(p.1.2:ℂ))
private theorem denominator_ne (u w : Icc (0:ℝ) 1) (h : ℝ) :
    clockDenominator ((u,w),h) ≠ 0 := by
  have hu : 1+(u.val:ℂ) ≠ 0 := by
    exact_mod_cast (show (1:ℝ)+u.val ≠ 0 by linarith [u.property.1])
  have hw : 1+(w.val:ℂ) ≠ 0 := by
    exact_mod_cast (show (1:ℝ)+w.val ≠ 0 by linarith [w.property.1])
  exact mul_ne_zero hu hw

private theorem scaledClock_original (q : XiZeroCopy) (branch : Bool) (V : ℝ)
    (u w : Icc (0:ℝ) 1) (h : ℝ) :
    scaledClockZero q branch V ((u,w),h)=
      clockDenominator ((u,w),h)*clockDensity q branch u w V h := by
  have he (t : ℝ) :
      scaledProfile (physicalRate q branch) u (h+(V-h)*t)*
        scaledProfile (-physicalRate q branch-3) w ((V-h)*t)=
      clockDenominator ((u,w),h)*(clockProfile (physicalRate q branch) u (h+(V-h)*t)*
        clockProfile (-physicalRate q branch-3) w ((V-h)*t)) := by
    rw [scaledProfile_original,scaledProfile_original]
    dsimp [clockDenominator]
    ring
  dsimp [scaledClockZero,clockIntegralJet,kernelJet,clockKernel]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  let I := ∫ t in (0:ℝ)..1, clockProfile (physicalRate q branch) u (h+(V-h)*t)*
    clockProfile (-physicalRate q branch-3) w ((V-h)*t)
  change (V-h:ℂ)*(clockDenominator ((u,w),h)*I)=clockDenominator ((u,w),h)*((V-h:ℂ)*I)
  ring

private theorem actual_clock_jets (q : XiZeroCopy) (branch : Bool) (V : ℝ)
    (u w : Icc (0:ℝ) 1) (h : ℝ) :
    clockDensity q branch u w V h=scaledClockZero q branch V ((u,w),h)/clockDenominator ((u,w),h) ∧
    deriv (clockDensity q branch u w V) h=scaledClockFirst q branch V ((u,w),h)/clockDenominator ((u,w),h) ∧
    deriv (deriv (clockDensity q branch u w V)) h=
      scaledClockSecond q branch V ((u,w),h)/clockDenominator ((u,w),h) := by
  have h0 (r : ℝ) : clockDensity q branch u w V r=
      scaledClockZero q branch V ((u,w),r)/clockDenominator ((u,w),r) := by
    apply (eq_div_iff (denominator_ne u w r)).mpr
    rw [scaledClock_original]
    ring
  have he0 := funext h0
  have h1 (r : ℝ) : deriv (clockDensity q branch u w V) r=
      scaledClockFirst q branch V ((u,w),r)/clockDenominator ((u,w),r) := by
    rw [he0]
    exact ((scaledClock_derivatives q branch V u w r).1.div_const (clockDenominator ((u,w),r))).deriv
  refine ⟨h0 h,h1 h,?_⟩
  rw [funext h1]
  exact ((scaledClock_derivatives q branch V u w h).2.div_const (clockDenominator ((u,w),h))).deriv

/-- The original moving-terminal clock and both delay derivatives have one uniform bound
for all compact physical radii and all delays in the fixed finite window. -/
theorem finite_clock_jet_bound (q : XiZeroCopy) (branch : Bool) (V : Ici (0:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u w : Icc (0:ℝ) 1) (h : Icc (0:ℝ) V.val),
      ‖deriv (deriv (clockDensity q branch u w V)) h‖+
        3*‖deriv (clockDensity q branch u w V) h‖+2*‖clockDensity q branch u w V h‖ ≤ C := by
  let K : Set ClockPoint := (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1) ×ˢ Icc (0:ℝ) V.val
  have hd : Continuous clockDenominator := by unfold clockDenominator; fun_prop
  have hn (p : ClockPoint) (hp : p ∈ K) : clockDenominator p ≠ 0 :=
    denominator_ne ⟨p.1.1,hp.1.1⟩ ⟨p.1.2,hp.1.2⟩ p.2
  obtain ⟨h0,h1,h2⟩ := scaledClock_continuous q branch V
  let g (p : ClockPoint) : ℝ :=
    ‖scaledClockSecond q branch V p/clockDenominator p‖+
      3*‖scaledClockFirst q branch V p/clockDenominator p‖+
      2*‖scaledClockZero q branch V p/clockDenominator p‖
  have hg : ContinuousOn g K :=
    (((h2.continuousOn.div hd.continuousOn hn).norm).add
      (continuousOn_const.mul (h1.continuousOn.div hd.continuousOn hn).norm)).add
      (continuousOn_const.mul (h0.continuousOn.div hd.continuousOn hn).norm)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  obtain ⟨B,hB⟩ := hK.exists_bound_of_continuousOn hg
  refine ⟨max B 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro u w h
  obtain ⟨he0,he1,he2⟩ := actual_clock_jets q branch V u w h
  rw [he0,he1,he2]
  change g ((u,w),h) ≤ max B 1
  have hb := hB ((u,w),h) ⟨⟨u.property,w.property⟩,h.property⟩
  exact (le_abs_self _).trans ((show |g ((u,w),h)| ≤ B by simpa [Real.norm_eq_abs] using hb).trans
    (le_max_left _ _))

/-- One derived constant bounds the literal full-source finite-delay bulk over BOTH complete
physical radial domains, including every characteristic corner and arbitrarily near the horizon. -/
theorem finite_delay_bulk_uniform (q : XiZeroCopy) (branch : Bool) (X k : ℝ)
    (V : Ici (0:ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (image : Bool) (x y : Iic (0:ℝ))
      (h : Icc (causalDelayStart image x y) V.val),
      ‖delayBulk image q branch x y V X k h‖ ≤ C := by
  obtain ⟨B,hB,hbulk⟩ := finite_delay_bulk_clock_bound q branch X k V
  obtain ⟨M,hM,hclock⟩ := finite_clock_jet_bound q branch V
  refine ⟨B*M,mul_pos hB hM,?_⟩
  intro image x y h
  have hh : 0 ≤ h.val := (causalDelayStart_nonneg image x y).trans h.property.1
  have hc := hclock ⟨radialUnit x,radial_mem x⟩ ⟨radialUnit y,radial_mem y⟩ ⟨h,hh,h.property.2⟩
  exact (hbulk image x y h).trans (mul_le_mul_of_nonneg_left hc hB.le)

/-- Original causal delay start on the target horizon. -/
def horizonStart (image : Bool) (y : ℝ) : ℝ := if image then -2*y else 0
/-- Original full-source invariant on the target horizon. -/
def horizonArgument (image : Bool) (y h : ℝ) : ℝ :=
  Real.exp h*(1-radialUnit y)+(if image then -radialUnit y else radialUnit y)
/-- Common limiting first and second time derivatives of the original invariant. -/
def horizonSlope (y h : ℝ) : ℝ := Real.exp h*(1-radialUnit y)
/-- The horizon coefficient retains the exact causal delay from its own branch. -/
def horizonRatio (image : Bool) (y h : ℝ) : ℝ := 1-Real.exp (horizonStart image y-h)

private theorem radial_limit : Tendsto radialUnit atBot (𝓝 (1:ℝ)) := by
  have heq : (fun x : ℝ => Real.exp (2*x))=fun x => (Real.exp x)^(2 : ℕ) := by
    funext x
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have he : Tendsto (fun x : ℝ => Real.exp (2*x)) atBot (𝓝 (0:ℝ)) := by
    rw [heq]
    simpa using Real.tendsto_exp_atBot.pow 2
  have hf (x : ℝ) : radialUnit x=(1-Real.exp (2*x))/(1+Real.exp (2*x)) := by
    have hid := radialUnit_one_sub x
    apply (eq_div_iff (show 1+Real.exp (2*x) ≠ 0 by positivity)).mpr
    nlinarith
  have h1 : Tendsto (fun _ : ℝ => (1:ℝ)) atBot (𝓝 1) := tendsto_const_nhds
  have ht := (h1.sub he).div (h1.add he)
    (show (1:ℝ)+0 ≠ 0 by norm_num)
  change Tendsto (fun x : ℝ => (1-Real.exp (2*x))/(1+Real.exp (2*x))) atBot
    (𝓝 ((1-0)/(1+0):ℝ)) at ht
  have hfFun : (fun x : ℝ => (1-Real.exp (2*x))/(1+Real.exp (2*x)))=radialUnit :=
    funext (fun x => (hf x).symm)
  simpa only [hfFun,sub_zero,add_zero,div_one] using ht

private theorem delay_time_formulas (image : Bool) (x y h : ℝ) :
    delaySlope image x y h=Real.sinh h*(1-radialUnit x*radialUnit y)+
      Real.cosh h*(radialUnit x-radialUnit y) ∧
    invariantTimeSecond (h-x+y) x (reflected image y)=
      Real.cosh h*(1-radialUnit x*radialUnit y)+Real.sinh h*(radialUnit x-radialUnit y) := by
  have hx := (Real.cosh_pos x).ne'
  have hy := (Real.cosh_pos y).ne'
  change Real.sinh (h-x+y)/(Real.cosh x*Real.cosh (if image then -y else y))=_ ∧
    Real.cosh (h-x+y)/(Real.cosh x*Real.cosh (if image then -y else y))=_
  rw [show h-x+y=h-(x-y) by ring]
  simp only [Real.sinh_sub,Real.cosh_sub]
  cases image <;> simp only [Bool.false_eq_true,if_false,if_true,Real.cosh_neg,radialUnit]
  all_goals constructor <;> field_simp [hx,hy] <;> ring

/-- The original compact invariant and both original time derivatives have their literal
horizon limits. No asymptotic kernel replaces the source. -/
theorem horizon_geometry_limits (image : Bool) (y h : ℝ) :
    Tendsto (fun x => delayArgument image x y h) atBot (𝓝 (horizonArgument image y h)) ∧
    Tendsto (fun x => delaySlope image x y h) atBot (𝓝 (horizonSlope y h)) ∧
    Tendsto (fun x => invariantTimeSecond (h-x+y) x (reflected image y)) atBot
      (𝓝 (horizonSlope y h)) := by
  have hc (c s : ℝ) : Tendsto (fun x => c*(1-radialUnit x*radialUnit y)+s*(radialUnit x-radialUnit y))
      atBot (𝓝 ((c+s)*(1-radialUnit y))) := by
    convert (tendsto_const_nhds.mul (tendsto_const_nhds.sub (radial_limit.mul_const (radialUnit y)))).add
      (tendsto_const_nhds.mul (radial_limit.sub_const (radialUnit y))) using 1
    ring
  have hB : Tendsto (fun x => Real.cosh h*(1-radialUnit x*radialUnit y)+
      Real.sinh h*(radialUnit x-radialUnit y)) atBot (𝓝 (horizonSlope y h)) := by
    simpa only [Real.cosh_add_sinh,horizonSlope] using hc (Real.cosh h) (Real.sinh h)
  have hA : Tendsto (fun x => Real.sinh h*(1-radialUnit x*radialUnit y)+
      Real.cosh h*(radialUnit x-radialUnit y)) atBot (𝓝 (horizonSlope y h)) := by
    simpa only [Real.sinh_add_cosh,horizonSlope] using hc (Real.sinh h) (Real.cosh h)
  refine ⟨?_,?_,?_⟩
  · have hi : Tendsto (fun x => if image then -(radialUnit x*radialUnit y) else radialUnit x*radialUnit y)
        atBot (𝓝 (if image then -radialUnit y else radialUnit y)) := by
      cases image
      · simpa only [Bool.false_eq_true,if_false,one_mul] using radial_limit.mul_const (radialUnit y)
      · simpa only [if_true,one_mul] using (radial_limit.mul_const (radialUnit y)).neg
    simpa only [← delay_invariant_formula,horizonArgument,horizonSlope] using hB.add hi
  · exact hA.congr' (Eventually.of_forall (fun x => (delay_time_formulas image x y h).1.symm))
  · exact hB.congr' (Eventually.of_forall (fun x => (delay_time_formulas image x y h).2.symm))

private theorem radial_lt_one (y : Iic (0:ℝ)) : radialUnit y < 1 := by
  rcases lt_or_eq_of_le (show y.val ≤ 0 from y.property) with hy | hy
  · exact (radialUnit_bounds y hy).2
  · simp [hy,radialUnit]
private theorem horizonSlope_pos (y : Iic (0:ℝ)) (h : ℝ) : 0 < horizonSlope y h :=
  mul_pos (Real.exp_pos _) (sub_pos.mpr (radial_lt_one y))
private theorem horizonStart_nonneg (image : Bool) (y : Iic (0:ℝ)) : 0 ≤ horizonStart image y := by
  cases image
  · simp [horizonStart]
  · change 0 ≤ -2*y.val
    have hy : y.val ≤ 0 := y.property
    linarith

private theorem horizon_gap (image : Bool) (y h : ℝ) :
    horizonArgument image y h-1=(1-radialUnit y)*(Real.exp h-Real.exp (horizonStart image y)) := by
  have he : Real.exp (-2*y)*(1-radialUnit y)=1+radialUnit y := by
    rw [radialUnit_one_sub,← mul_assoc,← Real.exp_add]
    rw [show -2*y+2*y=0 by ring,Real.exp_zero,one_mul]
  cases image
  · simp only [horizonArgument,horizonStart,Bool.false_eq_true,if_false,Real.exp_zero]
    ring
  · simp only [horizonArgument,horizonStart,if_true]
    nlinarith [he]

private theorem horizon_ratio_identity (image : Bool) (y : Iic (0:ℝ)) (h : ℝ) :
    (horizonArgument image y h-1)/horizonSlope y h=horizonRatio image y h ∧
    horizonSlope y h*(horizonArgument image y h-1)/(horizonSlope y h)^(2 : ℕ)=horizonRatio image y h := by
  have hw := (sub_pos.mpr (radial_lt_one y)).ne'
  have he := (Real.exp_pos h).ne'
  rw [horizon_gap]
  dsimp [horizonRatio,horizonSlope]
  rw [Real.exp_sub]
  constructor <;> field_simp [hw,he]

private theorem horizonArgument_interior (image : Bool) (y : Iic (0:ℝ))
    {h : ℝ} (hh : horizonStart image y < h) : 1 < horizonArgument image y h := by
  have hp := mul_pos (sub_pos.mpr (radial_lt_one y)) (sub_pos.mpr (Real.exp_lt_exp.mpr hh))
  rw [← horizon_gap] at hp
  linarith

/-- Both original normalized coefficients have the same branch-specific horizon delay factor. -/
theorem horizon_ratio_limits (image : Bool) (y : Iic (0:ℝ)) (h : ℝ) :
    Tendsto (fun x => (delayArgument image x y h-1)/delaySlope image x y h) atBot
      (𝓝 (horizonRatio image y h)) ∧
    Tendsto (fun x => invariantTimeSecond (h-x+y) x (reflected image y)*
      (delayArgument image x y h-1)/(delaySlope image x y h)^(2 : ℕ)) atBot (𝓝 (horizonRatio image y h)) := by
  obtain ⟨hZ,hA,hB⟩ := horizon_geometry_limits image y h
  have hn := (horizonSlope_pos y h).ne'
  obtain ⟨hr,hb⟩ := horizon_ratio_identity image y h
  constructor
  · have ht := (hZ.sub_const 1).div hA hn
    change Tendsto (fun x => (delayArgument image x y h-1)/delaySlope image x y h) atBot
      (𝓝 ((horizonArgument image y h-1)/horizonSlope y h)) at ht
    rwa [hr] at ht
  · have ht := (hB.mul (hZ.sub_const 1)).div (hA.pow 2) (pow_ne_zero _ hn)
    change Tendsto (fun x => invariantTimeSecond (h-x+y) x (reflected image y)*
      (delayArgument image x y h-1)/(delaySlope image x y h)^(2 : ℕ)) atBot
      (𝓝 (horizonSlope y h*(horizonArgument image y h-1)/(horizonSlope y h)^(2 : ℕ))) at ht
    rwa [hb] at ht

/-- The actual clock and both delay derivatives converge to their ORIGINAL compact target
radius-one values, retaining the moving terminal endpoint and both onset derivatives. -/
theorem clock_horizon_limits (q : XiZeroCopy) (branch : Bool) (y : Iic (0:ℝ)) (V h : ℝ) :
    Tendsto (fun x => clockDensity q branch (radialUnit x) (radialUnit y) V h) atBot
      (𝓝 (clockDensity q branch 1 (radialUnit y) V h)) ∧
    Tendsto (fun x => deriv (clockDensity q branch (radialUnit x) (radialUnit y) V) h) atBot
      (𝓝 (deriv (clockDensity q branch 1 (radialUnit y) V) h)) ∧
    Tendsto (fun x => deriv (deriv (clockDensity q branch (radialUnit x) (radialUnit y) V)) h) atBot
      (𝓝 (deriv (deriv (clockDensity q branch 1 (radialUnit y) V)) h)) := by
  let p : ClockPoint := ((1,radialUnit y),h)
  have hp : Tendsto (fun x => ((radialUnit x,radialUnit y),h)) atBot (𝓝 p) :=
    (radial_limit.prodMk_nhds tendsto_const_nhds).prodMk_nhds tendsto_const_nhds
  have hd : Continuous clockDenominator := by unfold clockDenominator; fun_prop
  have hD := hd.continuousAt.tendsto.comp hp
  have hn : clockDenominator p ≠ 0 := denominator_ne ⟨1,by simp⟩ ⟨radialUnit y,radial_mem y⟩ h
  obtain ⟨h0,h1,h2⟩ := scaledClock_continuous q branch V
  have ht0 := (h0.continuousAt.tendsto.comp hp).div hD hn
  have ht1 := (h1.continuousAt.tendsto.comp hp).div hD hn
  have ht2 := (h2.continuousAt.tendsto.comp hp).div hD hn
  obtain ⟨he0,he1,he2⟩ := actual_clock_jets q branch V ⟨1,by simp⟩ ⟨radialUnit y,radial_mem y⟩ h
  change _=scaledClockZero q branch V p/clockDenominator p at he0
  change _=scaledClockFirst q branch V p/clockDenominator p at he1
  change _=scaledClockSecond q branch V p/clockDenominator p at he2
  rw [← he0] at ht0
  rw [← he1] at ht1
  rw [← he2] at ht2
  refine ⟨ht0.congr' ?_,ht1.congr' ?_,ht2.congr' ?_⟩
  all_goals
    filter_upwards [eventually_le_atBot (0:ℝ)] with x hx
    obtain ⟨hx0,hx1,hx2⟩ := actual_clock_jets q branch V
      ⟨radialUnit x,radial_mem ⟨x,hx⟩⟩ ⟨radialUnit y,radial_mem y⟩ h
  · exact hx0.symm
  · exact hx1.symm
  · exact hx2.symm

private theorem moment_quotient (q : XiZeroCopy) (X k : ℝ) (z : Ioi (1:ℝ)) :
    secondMoment q X k z=primitive q X k z/(z.val-1:ℂ)^(2 : ℕ) := by
  have hz : (z.val-1:ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr z.property).ne'
  have he := (primitive_factor q X k ⟨z,(show (1:ℝ) < z.val from z.property).le⟩).1
  apply (eq_div_iff (pow_ne_zero _ hz)).mpr
  change primitive q X k z.val=(z.val-1:ℂ)^(2 : ℕ)*secondMoment q X k z.val at he
  rw [he]
  ring

private theorem moment_continuousAt (q : XiZeroCopy) (X k : ℝ) {z : ℝ} (hz : 1 < z) :
    ContinuousAt (secondMoment q X k) z := by
  have hn : (z-1:ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hz).ne'
  have hden : Continuous (fun r : ℝ => (r-1:ℂ)^(2 : ℕ)) := by fun_prop
  have ht := ((primitive_derivatives q X k hz).1.continuousAt.div hden.continuousAt
    (pow_ne_zero _ hn)).tendsto
  change Tendsto (fun r : ℝ => primitive q X k r/(r-1:ℂ)^(2 : ℕ)) (𝓝 z)
    (𝓝 (primitive q X k z/(z-1:ℂ)^(2 : ℕ))) at ht
  rw [← moment_quotient q X k ⟨z,hz⟩] at ht
  exact ht.congr' (by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with r hr
    exact (moment_quotient q X k ⟨r,hr⟩).symm)

/-- The literal horizon bulk retains the original source moment and factors the physical
clock operator as (partial_h-1)(partial_h-2). -/
def horizonBulk (image : Bool) (q : XiZeroCopy) (branch : Bool) (y V X k h : ℝ) : ℂ :=
  secondMoment q X k (horizonArgument image y h)*(horizonRatio image y h:ℂ)^(2 : ℕ)*
    (deriv (deriv (clockDensity q branch 1 (radialUnit y) V)) h-
      3*deriv (clockDensity q branch 1 (radialUnit y) V) h+
      2*clockDensity q branch 1 (radialUnit y) V h)

private theorem start_at_source (image : Bool) (y x : ℝ) (hx : x ≤ y) :
    causalDelayStart image x y=horizonStart image y := by
  cases image
  · simp [causalDelayStart,horizonStart,max_eq_right (sub_nonpos.mpr hx)]
  · rfl

/-- Exact pointwise target-horizon limit of the original complete source-delay bulk,
with its true branch-dependent causal delay. -/
theorem original_bulk_horizon_limit (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (y : Iic (0:ℝ)) (V X k : ℝ) (h : Ioi (horizonStart image y)) :
    Tendsto (fun x => delayBulk image q branch x y V X k h) atBot
      (𝓝 (horizonBulk image q branch y V X k h)) := by
  obtain ⟨hZ,_,_⟩ := horizon_geometry_limits image y h
  obtain ⟨hr,hb⟩ := horizon_ratio_limits image y h
  obtain ⟨hW,hW1,hW2⟩ := clock_horizon_limits q branch y V h
  have hU := (moment_continuousAt q X k (horizonArgument_interior image y h.property)).tendsto.comp hZ
  have hrc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have hbc := Complex.continuous_ofReal.continuousAt.tendsto.comp hb
  have h3 : Tendsto (fun _ : ℝ => (3:ℂ)) atBot (𝓝 3) := tendsto_const_nhds
  have ht := hU.mul ((((hrc.pow 2).mul hW2).sub
    (((h3.mul hrc).mul hbc).mul hW1)).add
      (((h3.mul (hbc.pow 2)).sub (hrc.pow 2)).mul hW))
  have he : secondMoment q X k (horizonArgument image y h)*
      ((horizonRatio image y h:ℂ)^(2 : ℕ)*deriv (deriv (clockDensity q branch 1 (radialUnit y) V)) h-
        3*(horizonRatio image y h:ℂ)*(horizonRatio image y h:ℂ)*deriv (clockDensity q branch 1 (radialUnit y) V) h+
        (3*(horizonRatio image y h:ℂ)^(2 : ℕ)-(horizonRatio image y h:ℂ)^(2 : ℕ))*clockDensity q branch 1 (radialUnit y) V h)=
      horizonBulk image q branch y V X k h := by unfold horizonBulk; ring
  change Tendsto _ atBot (𝓝 (_)) at ht
  rw [he] at ht
  apply ht.congr'
  filter_upwards [eventually_le_atBot (min (0:ℝ) y.val)] with x hx
  have hx0 : x ≤ 0 := hx.trans (min_le_left _ _)
  have hxy : x ≤ y.val := hx.trans (min_le_right _ _)
  have hh : causalDelayStart image x y ≤ h.val := by rw [start_at_source image y x hxy]; exact h.property.le
  exact (delay_bulk_normalized image q branch ⟨x,hx0⟩ y V X k ⟨h,hh⟩).symm

private theorem actual_clock_continuous (q : XiZeroCopy) (branch : Bool) (V : ℝ)
    (u w : Icc (0:ℝ) 1) :
    Continuous (clockDensity q branch u w V) ∧
    Continuous (deriv (clockDensity q branch u w V)) ∧
    Continuous (deriv (deriv (clockDensity q branch u w V))) := by
  have hp : Continuous (fun h : ℝ => ((u.val,w.val),h)) := by fun_prop
  obtain ⟨h0,h1,h2⟩ := scaledClock_continuous q branch V
  refine ⟨?_,?_,?_⟩
  · convert (h0.comp hp).div_const ((1+(u.val:ℂ))*(1+(w.val:ℂ))) using 1
    funext h
    exact (actual_clock_jets q branch V u w h).1
  · convert (h1.comp hp).div_const ((1+(u.val:ℂ))*(1+(w.val:ℂ))) using 1
    funext h
    exact (actual_clock_jets q branch V u w h).2.1
  · convert (h2.comp hp).div_const ((1+(u.val:ℂ))*(1+(w.val:ℂ))) using 1
    funext h
    exact (actual_clock_jets q branch V u w h).2.2

private theorem horizon_delay_interior (image : Bool) (x y : Iic (0:ℝ))
    (hxy : x.val ≤ y.val) {h : ℝ} (hh : horizonStart image y < h) :
    1 < delayArgument image x y h ∧ 0 < delaySlope image x y h := by
  have hs : horizonStart image y-x+y=|x.val-reflected image y| := by
    have hx0 : x.val ≤ 0 := x.property
    have hy0 : y.val ≤ 0 := y.property
    cases image
    · simp only [horizonStart,reflected,Bool.false_eq_true,if_false]
      rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring
    · simp only [horizonStart,reflected,if_true,sub_neg_eq_add]
      rw [abs_of_nonpos (show x.val+y.val ≤ 0 by linarith)]
      ring
  have ht : |x.val-reflected image y| < h-x+y := by linarith
  have ht0 : 0 < h-x+y := lt_of_le_of_lt (abs_nonneg _) ht
  have hc : Real.cosh (x.val-reflected image y)<Real.cosh (h-x+y) :=
    Real.cosh_lt_cosh.mpr (by simpa only [abs_of_pos ht0] using ht)
  refine ⟨?_,div_pos (Real.sinh_pos_iff.mpr ht0)
    (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))⟩
  unfold delayArgument invariant
  apply (lt_div_iff₀ (mul_pos (Real.cosh_pos _) (Real.cosh_pos _))).mpr
  change 1*(Real.cosh x*Real.cosh (reflected image y)) <
    Real.cosh (h-x+y)+Real.sinh x*Real.sinh (reflected image y)
  rw [Real.cosh_sub] at hc
  linarith

private theorem original_bulk_continuousOn (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (x y : Iic (0:ℝ)) (V X k : ℝ) (hxy : x.val ≤ y.val) :
    ContinuousOn (delayBulk image q branch x y V X k) (Ioo (horizonStart image y) V) := by
  have hZ : Continuous (delayArgument image x y) := by
    unfold delayArgument invariant
    fun_prop
  have hA : Continuous (delaySlope image x y) := by
    unfold delaySlope invariantTimeFirst
    fun_prop
  have hB : Continuous (fun h => invariantTimeSecond (h-x+y) x (reflected image y)) := by
    unfold invariantTimeSecond
    fun_prop
  obtain ⟨hW,hW1,hW2⟩ := actual_clock_continuous q branch V
    ⟨radialUnit x,radial_mem x⟩ ⟨radialUnit y,radial_mem y⟩
  intro h hh
  obtain ⟨hz,ha⟩ := horizon_delay_interior image x y hxy hh.1
  have hJ := (primitive_derivatives q X k hz).1.continuousAt.comp hZ.continuousAt
  have h0 := hW.continuousAt (x := h)
  have h1 := hW1.continuousAt (x := h)
  have h2 := hW2.continuousAt (x := h)
  have hac := (Complex.continuous_ofReal.comp hA).continuousAt (x := h)
  have hbc := (Complex.continuous_ofReal.comp hB).continuousAt (x := h)
  have hn : (delaySlope image x y h:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  exact (hJ.mul (((h2.div (hac.pow 2) (pow_ne_zero _ hn)).sub
    (((continuousAt_const.mul hbc).mul h1).div (hac.pow 3) (pow_ne_zero _ hn))).add
      ((((continuousAt_const.mul (hbc.pow 2)).sub (hac.pow 2)).mul h0).div
        (hac.pow 4) (pow_ne_zero _ hn)))).continuousWithinAt

/-- The actual source-delay bulk converges under its full finite causal integral as the target
approaches the horizon. The limit is derived from the original kernel and actual clock jets. -/
theorem original_bulk_horizon_integral (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (y : Iic (0:ℝ)) (X k : ℝ) (V : Ici (horizonStart image y)) :
    Tendsto (fun x => ∫ h in causalDelayStart image x y..V.val,
      delayBulk image q branch x y V X k h) atBot
      (𝓝 (∫ h in horizonStart image y..V.val, horizonBulk image q branch y V X k h)) := by
  have hV0 : 0 ≤ V.val := (horizonStart_nonneg image y).trans V.property
  obtain ⟨C,hC,hbound⟩ := finite_delay_bulk_uniform q branch X k ⟨V,hV0⟩
  have hmeas : ∀ᶠ x : ℝ in atBot, AEStronglyMeasurable (delayBulk image q branch x y V X k)
      (volume.restrict (Ioo (horizonStart image y) V.val)) := by
    filter_upwards [eventually_le_atBot (min (0:ℝ) y.val)] with x hx
    exact (original_bulk_continuousOn image q branch ⟨x,hx.trans (min_le_left _ _)⟩ y V X k
      (hx.trans (min_le_right _ _))).aestronglyMeasurable measurableSet_Ioo
  have hdom : ∀ᶠ x : ℝ in atBot, ∀ᵐ h ∂volume.restrict (Ioo (horizonStart image y) V.val),
      ‖delayBulk image q branch x y V X k h‖ ≤ C := by
    filter_upwards [eventually_le_atBot (min (0:ℝ) y.val)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    have hstart := start_at_source image y x (hx.trans (min_le_right _ _))
    exact hbound image ⟨x,hx.trans (min_le_left _ _)⟩ y
      ⟨h,by rw [hstart]; exact hh.1.le,hh.2.le⟩
  have hfinite : volume (Ioo (horizonStart image y) V.val) ≠ ⊤ :=
    ne_top_of_le_ne_top (isCompact_Icc.measure_ne_top (μ := volume)) (measure_mono Ioo_subset_Icc_self)
  have hlim : ∀ᵐ h ∂volume.restrict (Ioo (horizonStart image y) V.val),
      Tendsto (fun x => delayBulk image q branch x y V X k h) atBot
        (𝓝 (horizonBulk image q branch y V X k h)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with h hh
    exact original_bulk_horizon_limit image q branch y V X k ⟨h,hh.1⟩
  have ht := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => C)
    hmeas hdom (integrableOn_const hfinite) hlim
  rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le V.property] at ht
  apply ht.congr'
  filter_upwards [eventually_le_atBot y.val] with x hx
  rw [start_at_source image y x hx,intervalIntegral.integral_of_le V.property,
    integral_Ioc_eq_integral_Ioo]

/-- Signed direct-minus-image finite source transfer retains both original causal starts while
passing to the target horizon; neither branch is discarded or assigned a common onset. -/
theorem signed_bulk_horizon_integral (q : XiZeroCopy) (branch : Bool)
    (y : Iic (0:ℝ)) (X k : ℝ) (V : Ici (horizonStart true y)) :
    Tendsto (fun x =>
      (∫ h in causalDelayStart false x y..V.val, delayBulk false q branch x y V X k h)-
      (∫ h in causalDelayStart true x y..V.val, delayBulk true q branch x y V X k h)) atBot
      (𝓝 ((∫ h in horizonStart false y..V.val, horizonBulk false q branch y V X k h)-
        (∫ h in horizonStart true y..V.val, horizonBulk true q branch y V X k h))) := by
  have hV0 : horizonStart false y ≤ V.val := (horizonStart_nonneg true y).trans V.property
  exact (original_bulk_horizon_integral false q branch y X k ⟨V,hV0⟩).sub
    (original_bulk_horizon_integral true q branch y X k V)

/-- The original signed native spin-two source action has this derived target-horizon limit.
The already proved finite causal transpose identifies it with the negative horizon bulk. -/
theorem signed_native_horizon_integral (q : XiZeroCopy) (branch : Bool)
    (y : Iic (0:ℝ)) (X k : ℝ) (V : Ici (horizonStart true y)) :
    Tendsto (fun x =>
      (∫ h in causalDelayStart false x y..V.val,
        clockDensity q branch (radialUnit x) (radialUnit y) V h*D4BMCommonSourceGreen.nativeSpinTwoTrace false q h x ![y,X,k])-
      (∫ h in causalDelayStart true x y..V.val,
        clockDensity q branch (radialUnit x) (radialUnit y) V h*D4BMCommonSourceGreen.nativeSpinTwoTrace true q h x ![y,X,k])) atBot
      (𝓝 (-(∫ h in horizonStart false y..V.val, horizonBulk false q branch y V X k h)+
        (∫ h in horizonStart true y..V.val, horizonBulk true q branch y V X k h))) := by
  have ht := (signed_bulk_horizon_integral q branch y X k V).neg
  rw [neg_sub] at ht
  rw [show (∫ h in horizonStart true y..V.val, horizonBulk true q branch y V X k h)-
      (∫ h in horizonStart false y..V.val, horizonBulk false q branch y V X k h)=
      -(∫ h in horizonStart false y..V.val, horizonBulk false q branch y V X k h)+
        (∫ h in horizonStart true y..V.val, horizonBulk true q branch y V X k h) by ring] at ht
  apply ht.congr'
  filter_upwards [eventually_le_atBot (0:ℝ)] with x hx
  have hV : causalDelayStart true x y ≤ V.val := V.property
  have he := signed_delay_finite_transfer q branch ⟨x,hx⟩ y X k ⟨V,hV⟩
  change _=-(∫ h in causalDelayStart false x y..V.val, delayBulk false q branch x y V X k h)+
    (∫ h in causalDelayStart true x y..V.val, delayBulk true q branch x y V X k h) at he
  rw [he]
  ring

end
end RHTower.D4BMSpinTwoUniformDelay
