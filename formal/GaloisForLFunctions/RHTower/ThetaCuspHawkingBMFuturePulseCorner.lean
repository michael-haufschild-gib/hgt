import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMRetardedHorizonGeometry
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFuturePulseAdmission
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeAngularGreen

/-! Smooth two-triangle charts for the characteristic corner of the future pulse. -/
namespace RHTower.D4BMFuturePulseCorner
open Set MeasureTheory
open D4BMRetardedHorizonGeometry D4BMRetardedTriangleGeometry
open D4BMHorizon D4BMModularCore D4BMJointSource D4BMLaplaceRadial
open D4BMGlobalAngularResponse D4BMFuturePulseAdmission D4BMNativeCircle
open scoped ContDiff
noncomputable section
set_option autoImplicit false

def timeScale (first : Bool) (u : ℝ) : ℝ := if first then 1 else u
def radialScale (first : Bool) (u : ℝ) : ℝ := if first then u else 1
def timeOffset (first : Bool) (T t u : ℝ) : ℝ := T*t*timeScale first u
def radialLoss (first : Bool) (t u : ℝ) : ℝ := t*radialScale first u

/-- Strictly positive factor left after resolving the two characteristic faces. -/
def cornerFactor (first : Bool) (w T t u : ℝ) : ℝ :=
  (1-Real.exp (-w-timeOffset first T t u))*
    (T*timeScale first u*expc (timeOffset first T t u)+radialScale first u)/
    ((1+Real.exp (-w))*(2-radialLoss first t u))

private theorem radialLoss_bounds (first : Bool) {t u : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1) :
    radialLoss first t u ∈ Icc (0:ℝ) 1 := by
  cases first
  · simpa [radialLoss,radialScale] using ht
  · exact ⟨mul_nonneg ht.1 hu.1, mul_le_one₀ ht.2 hu.1 hu.2⟩

theorem cornerFactor_pos (first : Bool) {w T t u : ℝ}
    (hw : 0<w) (hT : 0<T) (ht : t ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1) :
    0 < cornerFactor first w T t u := by
  have hts : 0 ≤ timeScale first u := by cases first <;> simp [timeScale,hu.1]
  have ha : 0 ≤ timeOffset first T t u := mul_nonneg (mul_nonneg hT.le ht.1) hts
  have he : 0 < 1-Real.exp (-w-timeOffset first T t u) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hg : 0 < T*timeScale first u*expc (timeOffset first T t u)+radialScale first u := by
    cases first
    · simp only [timeScale,radialScale,Bool.false_eq_true,↓reduceIte]
      exact add_pos_of_nonneg_of_pos (mul_nonneg (mul_nonneg hT.le hu.1) (expc_pos _).le)
        (by norm_num)
    · simp only [timeScale,radialScale,↓reduceIte,mul_one]
      exact add_pos_of_pos_of_nonneg (mul_pos hT (expc_pos _)) hu.1
  exact div_pos (mul_pos he hg) (mul_pos (by positivity)
    (by linarith [(radialLoss_bounds first ht hu).2]))

/-- Exact invariant factorisation on both triangles of the original future source rectangle. -/
theorem compactInvariant_corner (first : Bool) (w T t u : ℝ) :
    compactInvariant false (Real.exp (-w-timeOffset first T t u)) (Real.exp (-w))
      (1-radialLoss first t u)-1 = 2*t*cornerFactor first w T t u := by
  have he : Real.exp (-w)/Real.exp (-w-timeOffset first T t u)=
      Real.exp (timeOffset first T t u) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hq : Real.exp (timeOffset first T t u)-1=
      t*(T*timeScale first u*expc (timeOffset first T t u)) := by
    rw [← expc_mul]
    unfold timeOffset
    ring
  simp only [compactInvariant,Bool.false_eq_true,↓reduceIte,add_sub_cancel_left,he,
    cornerFactor]
  rw [show 1-radialLoss first t u-Real.exp (timeOffset first T t u)=
    -(Real.exp (timeOffset first T t u)-1)-radialLoss first t u by ring,hq]
  unfold radialLoss
  ring

def cornerRadius (first : Bool) (z : Fin 4 → ℝ) : ℝ :=
  2*Real.arsinh (Real.sin (z 2)*Real.sqrt (cornerFactor first (Real.exp (z 0))
    (Real.exp (z 1)) (Real.sin (z 2)^(2 : ℕ)) (Real.sin (z 3)^(2 : ℕ))))

@[fun_prop] theorem cornerFactor_chart_smooth (first : Bool) :
    ContDiff ℝ ∞ (fun z : Fin 4 → ℝ => cornerFactor first (Real.exp (z 0))
      (Real.exp (z 1)) (Real.sin (z 2)^(2 : ℕ)) (Real.sin (z 3)^(2 : ℕ))) := by
  have hd (z : Fin 4 → ℝ) :
      (1+Real.exp (-Real.exp (z 0)))*
        (2-radialLoss first (Real.sin (z 2)^(2 : ℕ)) (Real.sin (z 3)^(2 : ℕ))) ≠ 0 := by
    apply mul_ne_zero (ne_of_gt (by positivity))
    have h := (radialLoss_bounds first
      ⟨sq_nonneg (Real.sin (z 2)),Real.sin_sq_le_one (z 2)⟩
      ⟨sq_nonneg (Real.sin (z 3)),Real.sin_sq_le_one (z 3)⟩).2
    exact ne_of_gt (by linarith)
  unfold cornerFactor
  apply ContDiff.div
  · cases first <;> dsimp [timeScale,radialScale,timeOffset] <;> fun_prop
  · cases first <;> dsimp [radialLoss,radialScale] <;> fun_prop
  · exact hd

@[fun_prop] theorem cornerRadius_smooth (first : Bool) : ContDiff ℝ ∞ (cornerRadius first) := by
  have hp (z : Fin 4 → ℝ) : 0 < cornerFactor first (Real.exp (z 0)) (Real.exp (z 1))
      (Real.sin (z 2)^(2 : ℕ)) (Real.sin (z 3)^(2 : ℕ)) :=
    cornerFactor_pos first (Real.exp_pos _) (Real.exp_pos _)
      ⟨sq_nonneg _,Real.sin_sq_le_one _⟩ ⟨sq_nonneg _,Real.sin_sq_le_one _⟩
  unfold cornerRadius
  exact contDiff_const.mul (Real.contDiff_arsinh.comp
    ((show ContDiff ℝ ∞ (fun z : Fin 4 → ℝ => Real.sin (z 2)) by fun_prop).mul
      ((cornerFactor_chart_smooth first).sqrt (fun z => (hp z).ne'))))

theorem compact_corner_radius (first : Bool) {w T t u : ℝ}
    (hw : 0<w) (hT : 0<T) (ht : t ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1) :
    Real.arcosh (max 1 (compactInvariant false (Real.exp (-w-timeOffset first T t u))
      (Real.exp (-w)) (1-radialLoss first t u))) =
      2*Real.arsinh (Real.sqrt t*Real.sqrt (cornerFactor first w T t u)) := by
  have hp := cornerFactor_pos first hw hT ht hu
  have hc : Real.cosh (2*Real.arsinh (Real.sqrt t*Real.sqrt (cornerFactor first w T t u)))=
      compactInvariant false (Real.exp (-w-timeOffset first T t u)) (Real.exp (-w))
        (1-radialLoss first t u) := by
    rw [Real.cosh_two_mul,Real.cosh_arsinh,Real.sinh_arsinh,
      Real.sq_sqrt (by positivity : 0 ≤ 1+(Real.sqrt t*Real.sqrt (cornerFactor first w T t u))^(2 : ℕ)),
      mul_pow,Real.sq_sqrt ht.1,Real.sq_sqrt hp.le]
    linear_combination -(compactInvariant_corner first w T t u)
  rw [← hc,max_eq_right (Real.one_le_cosh _),Real.arcosh_cosh]
  exact mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.mpr (by positivity))

/-- The smooth signed radius agrees with the actual future radius on both closed triangles. -/
theorem cornerRadius_eq (first : Bool) (W L : ℝ) {t u : ℝ}
    (ht : t ∈ Icc (0:ℝ) 1) (hu : u ∈ Icc (0:ℝ) 1) :
    cornerRadius first ![W,L,angleMap t,angleMap u]=
      Real.arcosh (max 1 (compactInvariant false
        (Real.exp (-Real.exp W-timeOffset first (Real.exp L) t u)) (Real.exp (-Real.exp W))
        (1-radialLoss first t u))) := by
  rw [compact_corner_radius first (Real.exp_pos _) (Real.exp_pos _) ht hu]
  change 2*Real.arsinh (Real.sin (angleMap t)*Real.sqrt (cornerFactor first (Real.exp W)
    (Real.exp L) (Real.sin (angleMap t)^(2 : ℕ)) (Real.sin (angleMap u)^(2 : ℕ)))) = _
  rw [angleMap_sine_square ht,angleMap_sine_square hu]
  have hs : Real.sin (angleMap t)=Real.sqrt t := by
    unfold angleMap
    exact Real.sin_arcsin (le_trans (by norm_num : (-1:ℝ)≤0) (Real.sqrt_nonneg t))
      (Real.sqrt_le_one.mpr ht.2)
  rw [hs]

/-- The complete pulse density after cancelling its radial horizon exponential. -/
def compactPulse (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (v z : ℝ) (B Q : ℂ) : ℂ :=
  (-2*seedHorizonProfile q branch amp (compactUnit z)*B+
    parameter q branch*sourceHorizonProfile (physicalRate q branch) amp 1 (compactUnit z)*Q)*
    ((deriv Real.smoothTransition v:ℝ):ℂ)*Complex.exp (2*physicalRate q branch*(v:ℂ))

/-- This compact density is exactly the original source, including both angular channels. -/
theorem fullSourceOnsetPulse_compact (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (tau y : ℝ) (point : Point) :
    fullSourceOnsetPulse q branch amp tau y point=(Real.exp (2*y):ℂ)*
      compactPulse q branch amp (tau+y) (Real.exp (2*y))
        (fullAngularField q branch point) (fullSquarePotential q point) := by
  rw [fullSourceOnsetPulse_transition,seedFirst_horizon]
  rw [show 2*parameter q branch*radialLiftFirst (physicalRate q branch) 0 amp 1 y=
      parameter q branch*(2*radialLiftFirst (physicalRate q branch) 0 amp 1 y) by ring,
    radialLiftFirst_horizon,radialUnit_compact]
  unfold compactPulse
  ring

private theorem power_comp_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : ℂ) {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (hp : ∀ x, 0 < f x) :
    ContDiff ℝ ∞ (fun x => power s (f x)) := by
  have he (x : E) : power s (f x)=Complex.exp (s*(Real.log (f x):ℂ)) := by
    rw [power,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hp x).ne'),
      ← Complex.ofReal_log (hp x).le]
    congr 1
    ring
  simp_rw [he]
  exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hf.log (fun x => (hp x).ne')))).cexp

theorem compactPulse_comp_smooth {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) {v z : E → ℝ} {B Q : E → ℂ}
    (hv : ContDiff ℝ ∞ v) (hz : ContDiff ℝ ∞ z)
    (hB : ContDiff ℝ ∞ B) (hQ : ContDiff ℝ ∞ Q) (hp : ∀ x, 0<1+z x) :
    ContDiff ℝ ∞ (fun x => compactPulse q branch amp (v x) (z x) (B x) (Q x)) := by
  have hU : ContDiff ℝ ∞ (fun x => compactUnit (z x)) :=
    (contDiff_const.sub hz).div (contDiff_const.add hz) (fun x => (hp x).ne')
  have hUc : ContDiff ℝ ∞ (fun x => (compactUnit (z x):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hU
  have hu (x : E) : 1+compactUnit (z x)=2/(1+z x) := by
    unfold compactUnit
    field_simp [(hp x).ne']
    ring
  have hP : ContDiff ℝ ∞ (fun x => power (2*physicalRate q branch) (1+compactUnit (z x))) :=
    power_comp_smooth _ (contDiff_const.add hU)
      (fun x => by rw [hu]; exact div_pos (by norm_num) (hp x))
  have hD : ContDiff ℝ ∞ (fun x => ((deriv Real.smoothTransition (v x):ℝ):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (((contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2).comp hv)
  have hV : ContDiff ℝ ∞ (fun x => (v x:ℂ)) := Complex.ofRealCLM.contDiff.comp hv
  have hE : ContDiff ℝ ∞ (fun x => Complex.exp (2*physicalRate q branch*(v x:ℂ))) :=
    (contDiff_const.mul hV).cexp
  have hS : ContDiff ℝ ∞ (fun x => seedHorizonProfile q branch amp (compactUnit (z x))) := by
    unfold seedHorizonProfile
    exact ((((contDiff_const.mul hP).mul contDiff_const).mul (contDiff_const.add hUc)).mul
      ((contDiff_const.mul hUc).add contDiff_const))
  have hL : ContDiff ℝ ∞ (fun x => sourceHorizonProfile (physicalRate q branch) amp 1
      (compactUnit (z x))) := by
    simp only [sourceHorizonProfile,show (1:Fin 2) ≠ 0 by norm_num,↓reduceIte]
    exact (((hP.mul contDiff_const).mul (contDiff_const.add hUc)).mul
      ((contDiff_const.mul (hUc.pow 2)).mul ((contDiff_const.mul hUc).add contDiff_const)))
  exact (((((contDiff_const.mul hS).mul hB).add ((contDiff_const.mul hL).mul hQ)).mul hD).mul hE)

private def chartParameters (z : (Fin 5 → ℝ) × (Fin 3 → ℝ)) : Fin 4 → ℝ :=
  ![z.1 1,z.1 2,z.2 0,z.2 1]

private theorem chartParameters_smooth : ContDiff ℝ ∞ chartParameters := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [chartParameters] <;> fun_prop

private def chartCircle (first : Bool) (z : (Fin 5 → ℝ) × (Fin 3 → ℝ)) : Point :=
  logCircle (cornerRadius first (chartParameters z)) (2*Real.pi*z.2 2) (z.1 3) (z.1 4)

private theorem chartCircle_smooth (first : Bool) : ContDiff ℝ ∞ (chartCircle first) := by
  have hR := (cornerRadius_smooth first).comp chartParameters_smooth
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [chartCircle,logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := intro z; exact (denominator_pos _ _).ne')

private theorem chartCircle_height_pos (first : Bool) (z : (Fin 5 → ℝ) × (Fin 3 → ℝ)) :
    0 < chartCircle first z 1 :=
  mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))

/-- Full pulse with the two-triangle Jacobian, on globally smooth target/source charts. -/
def cornerIntegrand (first : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : (Fin 5 → ℝ) × (Fin 3 → ℝ)) : ℂ :=
  (Real.exp (z.1 2)*Real.sin (z.2 0)^(2 : ℕ):ℝ)*
    compactPulse q branch amp
      (z.1 0+timeOffset first (Real.exp (z.1 2)) (Real.sin (z.2 0)^(2 : ℕ)) (Real.sin (z.2 1)^(2 : ℕ)))
      (1-radialLoss first (Real.sin (z.2 0)^(2 : ℕ)) (Real.sin (z.2 1)^(2 : ℕ)))
      (fullAngularField q branch (chartCircle first z)) (fullSquarePotential q (chartCircle first z))/4

/-- Every target derivative exists across the resolved characteristic corner. -/
theorem cornerIntegrand_smooth (first : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContDiff ℝ ∞ (cornerIntegrand first q branch amp) := by
  have hC := chartCircle_smooth first
  have hB : ContDiff ℝ ∞ (fun z => fullAngularField q branch (chartCircle first z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact (fullAngularField_smooth q branch _ (chartCircle_height_pos first z)).comp z hC.contDiffAt
  have hQ : ContDiff ℝ ∞ (fun z => fullSquarePotential q (chartCircle first z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact (contDiffAt_infty.mpr (fun n =>
      fullSquarePotential_smooth q _ (chartCircle_height_pos first z) n)).comp z hC.contDiffAt
  have hv : ContDiff ℝ ∞ (fun z : (Fin 5 → ℝ) × (Fin 3 → ℝ) =>
      z.1 0+timeOffset first (Real.exp (z.1 2)) (Real.sin (z.2 0)^(2 : ℕ)) (Real.sin (z.2 1)^(2 : ℕ))) := by
    cases first <;> dsimp [timeOffset,timeScale] <;> fun_prop
  have hz : ContDiff ℝ ∞ (fun z : (Fin 5 → ℝ) × (Fin 3 → ℝ) =>
      1-radialLoss first (Real.sin (z.2 0)^(2 : ℕ)) (Real.sin (z.2 1)^(2 : ℕ))) := by
    cases first <;> dsimp [radialLoss,radialScale] <;> fun_prop
  have hp (z : (Fin 5 → ℝ) × (Fin 3 → ℝ)) :
      0<1+(1-radialLoss first (Real.sin (z.2 0)^(2 : ℕ)) (Real.sin (z.2 1)^(2 : ℕ))) := by
    have h := (radialLoss_bounds first
      ⟨sq_nonneg (Real.sin (z.2 0)),Real.sin_sq_le_one (z.2 0)⟩
      ⟨sq_nonneg (Real.sin (z.2 1)),Real.sin_sq_le_one (z.2 1)⟩).2
    linarith
  have hF := compactPulse_comp_smooth q branch amp hv hz hB hQ hp
  have hJ : ContDiff ℝ ∞ (fun z : (Fin 5 → ℝ) × (Fin 3 → ℝ) =>
      ((Real.exp (z.1 2)*Real.sin (z.2 0)^(2 : ℕ):ℝ):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (by fun_prop : ContDiff ℝ ∞ (fun z : (Fin 5 → ℝ) × (Fin 3 → ℝ) =>
        Real.exp (z.1 2)*Real.sin (z.2 0)^(2 : ℕ)))
  unfold cornerIntegrand
  simpa only [div_eq_mul_inv] using (hJ.mul hF).mul (contDiff_const (c := (4:ℂ)⁻¹))

private def gamma (t : ℝ × ℝ × ℝ) : Fin 3 → ℝ :=
  ![angleMap t.1,angleMap t.2.1,t.2.2]

private theorem gamma_continuous : Continuous gamma := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact angleMap_continuous.comp continuous_fst
  · exact angleMap_continuous.comp continuous_snd.fst
  · exact continuous_snd.snd

/-- The two compact triangle integrals retaining the original source and Jacobian. -/
def cornerAction (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (z : Fin 5 → ℝ) : ℂ :=
  (∫ t in (0:ℝ)..1, ∫ u in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
    cornerIntegrand true q branch amp (z,gamma (t,u,c)))+
  (∫ t in (0:ℝ)..1, ∫ u in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
    cornerIntegrand false q branch amp (z,gamma (t,u,c)))

theorem cornerAction_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContDiff ℝ ∞ (cornerAction q branch amp) :=
  (D4BMNativeResponse.unitCube_integral_smooth
    (cornerIntegrand_smooth true q branch amp) gamma gamma_continuous).add
  (D4BMNativeResponse.unitCube_integral_smooth
    (cornerIntegrand_smooth false q branch amp) gamma gamma_continuous)

private theorem triangle_swap (f : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) {l r : ℝ} (hlr : l ≤ r) :
    (∫ x in l..r, ∫ y in x..r, f x y) = ∫ y in l..r, ∫ x in l..y, f x y := by
  let μ : Measure ℝ := volume.restrict (Ioc l r)
  let g (x y : ℝ) := if x ≤ y then f x y else 0
  have hi : Integrable (Function.uncurry f) (μ.prod μ) := by
    rw [Measure.prod_restrict,← Measure.volume_eq_prod]
    exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hg : Integrable (Function.uncurry g) (μ.prod μ) := by
    convert! hi.indicator (measurableSet_le measurable_fst measurable_snd) using 1
  have hswap := integral_integral_swap hg
  have hleft : (∫ x in l..r, ∫ y in x..r, f x y) = ∫ x, ∫ y, g x y ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hlr]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    have hset : Ioc l r ∩ Ici x = Icc x r := by
      ext y
      simp only [mem_inter_iff,mem_Ioc,mem_Ici,mem_Icc]
      constructor
      · rintro ⟨hxy,hy⟩; exact ⟨hy,hxy.2⟩
      · rintro ⟨hxy,hy⟩; exact ⟨⟨hx.1.trans_le hxy,hy⟩,hxy⟩
    have he : g x = (Ici x).indicator (f x) := by
      ext y; simp only [g,Set.indicator_apply,mem_Ici]
    change _ = ∫ y in Ioc l r, g x y
    rw [he,setIntegral_indicator measurableSet_Ici,hset,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hx.2]
  have hright : (∫ y in l..r, ∫ x in l..y, f x y) = ∫ y, ∫ x, g x y ∂μ ∂μ := by
    rw [intervalIntegral.integral_of_le hlr]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro y hy
    dsimp only
    have hset : Ioc l r ∩ Iic y = Ioc l y := by
      ext x
      simp only [mem_inter_iff,mem_Ioc,mem_Iic]
      constructor
      · rintro ⟨hxy,hx⟩; exact ⟨hxy.1,hx⟩
      · rintro ⟨hx,hxy⟩; exact ⟨⟨hx,hxy.trans hy.2⟩,hxy⟩
    have he : (fun x => g x y) = (Iic y).indicator (fun x => f x y) := by
      ext x; simp only [g,Set.indicator_apply,mem_Iic]
    change _ = ∫ x in Ioc l r, g x y
    rw [he,setIntegral_indicator measurableSet_Iic,hset,intervalIntegral.integral_of_le hy.1.le]
  rw [hleft,hright]
  exact hswap


private theorem rectangle_triangles (f : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) {p : ℝ} (hp : 0 ≤ p) (r : ℝ) :
    (∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r, f a b)=
      (∫ a in (0:ℝ)..p, ∫ b in a..r, f a b)+
      (∫ a in (0:ℝ)..p, ∫ b in a..p, f b a) := by
  have hslice (a : ℝ) : Continuous (f a) := hf.comp (continuous_const.prodMk continuous_id)
  have hz : Continuous (fun a => ∫ b in (0:ℝ)..a, f a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf continuous_id
  have hr : Continuous (fun a => ∫ b in (0:ℝ)..r, f a b) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hf 0 r
  have htail : Continuous (fun a => ∫ b in a..r, f a b) := by
    convert! hr.sub hz using 1
    funext a
    exact (intervalIntegral.integral_interval_sub_left
      ((hslice a).intervalIntegrable 0 r) ((hslice a).intervalIntegrable 0 a)).symm
  have he (a : ℝ) : (∫ b in (0:ℝ)..r, f a b)=
      (∫ b in a..r, f a b)+(∫ b in (0:ℝ)..a, f a b) := by
    rw [add_comm]
    exact (intervalIntegral.integral_add_adjacent_intervals
      ((hslice a).intervalIntegrable 0 a) ((hslice a).intervalIntegrable a r)).symm
  simp_rw [he]
  rw [intervalIntegral.integral_add (htail.intervalIntegrable 0 p) (hz.intervalIntegrable 0 p)]
  congr 1
  exact (triangle_swap (fun a b => f b a) (hf.comp continuous_swap) hp).symm


private theorem square_triangles (f : ℝ → ℝ → ℂ)
    (hf : Continuous (Function.uncurry f)) :
    (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, f a b)=
      (∫ t in (0:ℝ)..1, ∫ u in (0:ℝ)..1, (t:ℂ)*f t (t*u))+
      (∫ t in (0:ℝ)..1, ∫ u in (0:ℝ)..1, (t:ℂ)*f (t*u) t) := by
  have h := rectangle_triangles f hf (by norm_num : (0:ℝ) ≤ 1) 1
  rw [triangle_swap f hf (by norm_num),
    triangle_swap (fun a b => f b a) (hf.comp continuous_swap) (by norm_num)] at h
  rw [h,add_comm]
  congr 1 <;> apply intervalIntegral.integral_congr <;> intro t ht
  · simpa only [mul_zero,mul_one,Complex.real_smul,intervalIntegral.integral_const_mul] using
      (intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := 1) (f t) t).symm
  · simpa only [mul_zero,mul_one,Complex.real_smul,intervalIntegral.integral_const_mul] using
      (intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := 1) (fun u => f u t) t).symm

theorem compactPulse_comp_continuous {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) {v z : E → ℝ} {B Q : E → ℂ}
    (hv : Continuous v) (hz : Continuous z) (hB : Continuous B) (hQ : Continuous Q)
    (hp : ∀ x, 0<1+z x) :
    Continuous (fun x => compactPulse q branch amp (v x) (z x) (B x) (Q x)) := by
  let F : (ℝ × ℝ) × (ℂ × ℂ) → ℂ := fun y =>
    compactPulse q branch amp y.1.1 (Real.exp y.1.2-1) y.2.1 y.2.2
  have hf : ContDiff ℝ ∞ F := compactPulse_comp_smooth q branch amp
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (fun y => by linarith [Real.exp_pos y.1.2])
  have hc : Continuous (fun x => ((v x,Real.log (1+z x)),(B x,Q x))) :=
    (hv.prodMk ((continuous_const.add hz).log (fun x => (hp x).ne'))).prodMk (hB.prodMk hQ)
  convert hf.continuous.comp hc using 1
  funext x
  dsimp only [Function.comp_def,F]
  rw [Real.exp_log (hp x),add_sub_cancel_left]

private def upperRadius (z : Fin 5 → ℝ) (ab : ℝ × ℝ) : ℝ :=
  Real.arcosh (max 1 (compactInvariant false (Real.exp (-Real.exp (z 1)-Real.exp (z 2)*ab.1))
    (Real.exp (-Real.exp (z 1))) (max 0 (1-ab.2))))

private theorem upperRadius_continuous (z : Fin 5 → ℝ) : Continuous (upperRadius z) := by
  have hz : Continuous (fun ab : ℝ × ℝ => max 0 (1-ab.2)) := by fun_prop
  have hI : Continuous (fun ab : ℝ × ℝ => compactInvariant false
      (Real.exp (-Real.exp (z 1)-Real.exp (z 2)*ab.1)) (Real.exp (-Real.exp (z 1)))
      (max 0 (1-ab.2))) := by
    simp only [compactInvariant,Bool.false_eq_true,↓reduceIte]
    fun_prop (disch := intro ab; positivity)
  exact Real.continuousOn_arcosh.comp_continuous (continuous_const.max hI)
    (fun ab => (show (1:ℝ) ≤ max 1 _ from le_max_left _ _))

private def upperCircle (z : Fin 5 → ℝ) (y : (ℝ × ℝ) × ℝ) : Point :=
  logCircle (upperRadius z y.1) (2*Real.pi*y.2) (z 3) (z 4)

private theorem upperCircle_continuous (z : Fin 5 → ℝ) : Continuous (upperCircle z) := by
  have hR : Continuous (fun y : (ℝ × ℝ) × ℝ => upperRadius z y.1) :=
    (upperRadius_continuous z).comp continuous_fst
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [upperCircle,logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := intro y; exact (denominator_pos _ _).ne')

private theorem upperCircle_height_pos (z : Fin 5 → ℝ) (y : (ℝ × ℝ) × ℝ) :
    0 < upperCircle z y 1 :=
  mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))

/-- The unchanged compact upper direct density; the clamp is inactive on the source square. -/
def upperSample (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : Fin 5 → ℝ) (ab : ℝ × ℝ) (c : ℝ) : ℂ :=
  compactPulse q branch amp (z 0+Real.exp (z 2)*ab.1) (max 0 (1-ab.2))
    (fullAngularField q branch (upperCircle z (ab,c)))
    (fullSquarePotential q (upperCircle z (ab,c)))/4

private theorem upperSample_continuous (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : Fin 5 → ℝ) : Continuous (Function.uncurry (upperSample q branch amp z)) := by
  have hc := upperCircle_continuous z
  have hB : Continuous (fun y => fullAngularField q branch (upperCircle z y)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (fullAngularField_smooth q branch _ (upperCircle_height_pos z y)).continuousAt.comp
      hc.continuousAt
  have hQ : Continuous (fun y => fullSquarePotential q (upperCircle z y)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (fullSquarePotential_smooth q _ (upperCircle_height_pos z y) 0).continuousAt.comp
      hc.continuousAt
  have hF := compactPulse_comp_continuous q branch amp
    (by fun_prop : Continuous (fun y : (ℝ × ℝ) × ℝ => z 0+Real.exp (z 2)*y.1.1))
    (by fun_prop : Continuous (fun y : (ℝ × ℝ) × ℝ => max 0 (1-y.1.2))) hB hQ
    (fun y => by linarith [le_max_left (0:ℝ) (1-y.1.2)])
  exact hF.div_const 4

/-- The complete finite upper direct rectangle, before resolving its corner. -/
def upperDirectAction (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (z : Fin 5 → ℝ) : ℂ :=
  (Real.exp (z 2):ℂ)*(∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
    upperSample q branch amp z (a,b) c)

private theorem cornerIntegrand_eq_sample (first : Bool) (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (z : Fin 5 → ℝ) {t u : ℝ} (ht : t ∈ Icc (0:ℝ) 1)
    (hu : u ∈ Icc (0:ℝ) 1) (c : ℝ) :
    cornerIntegrand first q branch amp (z,gamma (t,u,c))=
      (Real.exp (z 2):ℂ)*(t:ℂ)*upperSample q branch amp z
        (t*timeScale first u,radialLoss first t u) c := by
  have hr : cornerRadius first (chartParameters (z,gamma (t,u,c)))=
      upperRadius z (t*timeScale first u,radialLoss first t u) := by
    change cornerRadius first ![z 1,z 2,angleMap t,angleMap u]=_
    rw [cornerRadius_eq first (z 1) (z 2) ht hu]
    unfold upperRadius
    rw [max_eq_right (sub_nonneg.mpr (radialLoss_bounds first ht hu).2)]
    congr 5
    unfold timeOffset
    ring
  have hc : chartCircle first (z,gamma (t,u,c))=
      upperCircle z ((t*timeScale first u,radialLoss first t u),c) := by
    change logCircle (cornerRadius first (chartParameters (z,gamma (t,u,c))))
      (2*Real.pi*c) (z 3) (z 4)=_
    rw [hr]
    rfl
  unfold cornerIntegrand
  rw [hc]
  change ((Real.exp (z 2)*Real.sin (angleMap t)^(2 : ℕ):ℝ):ℂ)*
    compactPulse q branch amp
      (z 0+timeOffset first (Real.exp (z 2)) (Real.sin (angleMap t)^(2 : ℕ)) (Real.sin (angleMap u)^(2 : ℕ)))
      (1-radialLoss first (Real.sin (angleMap t)^(2 : ℕ)) (Real.sin (angleMap u)^(2 : ℕ))) _ _/4=_
  rw [angleMap_sine_square ht,angleMap_sine_square hu]
  unfold upperSample
  rw [max_eq_right (sub_nonneg.mpr (radialLoss_bounds first ht hu).2)]
  rw [show timeOffset first (Real.exp (z 2)) t u=Real.exp (z 2)*(t*timeScale first u) by
    unfold timeOffset; ring]
  push_cast
  ring

/-- Resolving the characteristic corner preserves the exact full-source integral. -/
theorem cornerAction_eq_upperDirectAction (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : Fin 5 → ℝ) : cornerAction q branch amp z=upperDirectAction q branch amp z := by
  let f : ℝ → ℝ → ℂ := fun a b => ∫ c in (0:ℝ)..1, upperSample q branch amp z (a,b) c
  have hf : Continuous (Function.uncurry f) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (upperSample_continuous q branch amp z) 0 1
  have he (first : Bool) :
      (∫ t in (0:ℝ)..1, ∫ u in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
        cornerIntegrand first q branch amp (z,gamma (t,u,c)))=
      (Real.exp (z 2):ℂ)*(∫ t in (0:ℝ)..1, ∫ u in (0:ℝ)..1,
        (t:ℂ)*f (t*timeScale first u) (radialLoss first t u)) := by
    simp_rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    apply intervalIntegral.integral_congr
    intro u hu
    change (∫ c in (0:ℝ)..1, _) =
      (Real.exp (z 2):ℂ)*((t:ℂ)*(∫ c in (0:ℝ)..1,
        upperSample q branch amp z (t*timeScale first u,radialLoss first t u) c))
    simp_rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro c hc
    dsimp only
    rw [cornerIntegrand_eq_sample first q branch amp z
      (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ht)
      (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hu) c]
    ring
  unfold cornerAction upperDirectAction
  rw [he true,he false]
  simp only [timeScale,radialLoss,radialScale,↓reduceIte,Bool.false_eq_true,mul_one]
  rw [← mul_add,← square_triangles f hf]

/-- All target derivatives of the actual finite upper direct pulse exist, including its corner. -/
theorem upperDirectAction_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContDiff ℝ ∞ (upperDirectAction q branch amp) := by
  have he : upperDirectAction q branch amp=cornerAction q branch amp :=
    funext (fun z => (cornerAction_eq_upperDirectAction q branch amp z).symm)
  rw [he]
  exact cornerAction_smooth q branch amp

/-- Time reversal expresses the original future kernel in the same compact source coordinate. -/
theorem future_invariant_compact (image : Bool) (tau x v y : ℝ) :
    D4BMCausalKernel.invariant (v-y-tau) x (if image then -y else y)=
      compactInvariant image (Real.exp (tau+x-v)) (Real.exp (2*x)) (Real.exp (2*y)) := by
  have h := invariant_compact image (tau+x-v) x y
  rw [show tau+x-v-x+y=-(v-y-tau) by ring] at h
  simpa only [D4BMCausalKernel.invariant,Real.cosh_neg] using h

/-- Each compact sample is the original future pulse divided by its exact Jacobian factor. -/
theorem upperSample_original (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (r W L X k v y c : ℝ) :
    upperSample q branch amp ![r,W,L,X,k] ((v-r)/Real.exp L,1-Real.exp (2*y)) c =
      fullSourceOnsetPulse q branch amp (v-y) y
        (logCircle (Real.arcosh (max 1 (D4BMCausalKernel.invariant
          (v-y-(r-Real.exp W/2)) (-Real.exp W/2) y))) (2*Real.pi*c) X k)/
        (4*(Real.exp (2*y):ℂ)) := by
  have hv : r+Real.exp L*((v-r)/Real.exp L)=v := by
    field_simp
    ring
  have hz : max 0 (1-(1-Real.exp (2*y)))=Real.exp (2*y) := by
    rw [sub_sub_cancel,max_eq_right (Real.exp_pos _).le]
  have hi := future_invariant_compact false (r-Real.exp W/2) (-Real.exp W/2) v y
  simp only [Bool.false_eq_true,↓reduceIte] at hi
  rw [show r-Real.exp W/2+-Real.exp W/2-v = -Real.exp W-(v-r) by ring,
    show 2*(-Real.exp W/2) = -Real.exp W by ring] at hi
  have ha : Real.exp L*((v-r)/Real.exp L)=v-r := by field_simp
  have hd : upperRadius ![r,W,L,X,k] ((v-r)/Real.exp L,1-Real.exp (2*y))=
      Real.arcosh (max 1 (D4BMCausalKernel.invariant
        (v-y-(r-Real.exp W/2)) (-Real.exp W/2) y)) := by
    change Real.arcosh (max 1 (compactInvariant false
      (Real.exp (-Real.exp W-Real.exp L*((v-r)/Real.exp L))) (Real.exp (-Real.exp W))
      (max 0 (1-(1-Real.exp (2*y))))))=_
    rw [hz,ha,hi]
  unfold upperSample upperCircle
  change compactPulse q branch amp (r+Real.exp L*((v-r)/Real.exp L))
    (max 0 (1-(1-Real.exp (2*y))))
    (fullAngularField q branch (logCircle
      (upperRadius ![r,W,L,X,k] ((v-r)/Real.exp L,1-Real.exp (2*y))) (2*Real.pi*c) X k))
    (fullSquarePotential q (logCircle
      (upperRadius ![r,W,L,X,k] ((v-r)/Real.exp L,1-Real.exp (2*y))) (2*Real.pi*c) X k))/4=_
  rw [hv,hz,hd,fullSourceOnsetPulse_compact,sub_add_cancel]
  have he : (Real.exp (2*y):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  field_simp [he]

end
end RHTower.D4BMFuturePulseCorner
