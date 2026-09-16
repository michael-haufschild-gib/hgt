import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFuturePulseCorner

/-! The lower direct and upper image pulse regions, with a single smooth global cutoff. -/
namespace RHTower.D4BMFuturePulseAssembly
open Set MeasureTheory
open D4BMRetardedHorizonGeometry D4BMRetardedTriangleGeometry D4BMFuturePulseCorner
open D4BMHorizon D4BMModularCore D4BMJointSource D4BMNativeCircle
open scoped ContDiff
noncomputable section
set_option autoImplicit false

def sourceZ (image : Bool) (w a b : ℝ) : ℝ :=
  if image then b else Real.exp (-w*(1-a))*b

def sourceE (image : Bool) (w T a : ℝ) : ℝ :=
  if image then Real.exp (-w-T*a) else Real.exp (-w*a)

def sourceClock (image : Bool) (r w T a : ℝ) : ℝ :=
  if image then r+T*a else r-w+w*a

def sourceJacobian (image : Bool) (w T a : ℝ) : ℝ :=
  if image then T else w*Real.exp (-w*(1-a))

/-- The positive characteristic factor for the two remaining future regions. -/
def edgeFactor (image : Bool) (w T a b : ℝ) : ℝ :=
  (if image then T*expc (T*a)*(1-Real.exp (-w-T*a)*b)
    else Real.exp (-w)*w*expc (w*a))/((1+Real.exp (-w))*(1+sourceZ image w a b))

private theorem sourceZ_nonneg (image : Bool) (w a : ℝ) {b : ℝ} (hb : 0 ≤ b) :
    0 ≤ sourceZ image w a b := by
  cases image <;> simp only [sourceZ,Bool.false_eq_true,↓reduceIte]
  · exact mul_nonneg (Real.exp_pos _).le hb
  · exact hb

theorem edgeFactor_pos (image : Bool) {w T a b : ℝ} (hw : 0<w) (hT : 0<T)
    (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) : 0 < edgeFactor image w T a b := by
  have hd : 0 < (1+Real.exp (-w))*(1+sourceZ image w a b) :=
    mul_pos (by positivity) (by linarith [sourceZ_nonneg image w a hb.1])
  apply div_pos _ hd
  cases image <;> simp only [Bool.false_eq_true,↓reduceIte]
  · exact mul_pos (mul_pos (Real.exp_pos _) hw) (expc_pos _)
  · have he : Real.exp (-w-T*a)<1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [mul_nonneg hT.le ha.1])
    have hprod := mul_le_mul_of_nonneg_left hb.2 (Real.exp_pos (-w-T*a)).le
    exact mul_pos (mul_pos hT (expc_pos _)) (by nlinarith)

/-- The exact causal invariant, including its characteristic boundary. -/
theorem compactInvariant_edge (image : Bool) (w T a b : ℝ) :
    compactInvariant image (sourceE image w T a) (Real.exp (-w)) (sourceZ image w a b)-1=
      2*a*(if image then 1 else 1-b)*edgeFactor image w T a b := by
  cases image
  · simp only [compactInvariant,sourceE,edgeFactor,sourceZ,Bool.false_eq_true,↓reduceIte,
      add_sub_cancel_left]
    rw [show 2*a*(1-b)*(Real.exp (-w)*w*expc (w*a)/
      ((1+Real.exp (-w))*(1+Real.exp (-w*(1-a))*b)))=
      2*Real.exp (-w)*((w*a)*expc (w*a))*(1-b)/
      ((1+Real.exp (-w))*(1+Real.exp (-w*(1-a))*b)) by ring,expc_mul]
    apply congrArg (fun n : ℝ => n/((1+Real.exp (-w))*(1+Real.exp (-w*(1-a))*b)))
    have he : Real.exp (-w*(1-a))=Real.exp (-w)*Real.exp (w*a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he,show -w*a=-(w*a) by ring,Real.exp_neg]
    field_simp
    ring
  · simp only [compactInvariant,sourceE,edgeFactor,sourceZ,↓reduceIte,add_sub_cancel_left,mul_one]
    rw [show 2*a*(T*expc (T*a)*(1-Real.exp (-w-T*a)*b)/
      ((1+Real.exp (-w))*(1+b)))=
      2*((T*a)*expc (T*a))*(1-Real.exp (-w-T*a)*b)/
      ((1+Real.exp (-w))*(1+b)) by ring,expc_mul]
    apply congrArg (fun n : ℝ => n/((1+Real.exp (-w))*(1+b)))
    rw [Real.exp_sub]
    field_simp
    ring

def edgeRadius (image : Bool) (z : Fin 4 → ℝ) : ℝ :=
  2*Real.arsinh (Real.sin (z 2)*(if image then 1 else Real.cos (z 3))*
    Real.sqrt (edgeFactor image (Real.exp (z 0)) (Real.exp (z 1))
      (Real.sin (z 2)^2) (Real.sin (z 3)^2)))

@[fun_prop] theorem edgeFactor_chart_smooth (image : Bool) :
    ContDiff ℝ ∞ (fun z : Fin 4 → ℝ => edgeFactor image (Real.exp (z 0)) (Real.exp (z 1))
      (Real.sin (z 2)^2) (Real.sin (z 3)^2)) := by
  have hd (z : Fin 4 → ℝ) : (1+Real.exp (-Real.exp (z 0)))*
      (1+sourceZ image (Real.exp (z 0)) (Real.sin (z 2)^2) (Real.sin (z 3)^2)) ≠ 0 := by
    apply mul_ne_zero (ne_of_gt (by positivity))
    have hz := sourceZ_nonneg image (Real.exp (z 0)) (Real.sin (z 2)^2)
      (sq_nonneg (Real.sin (z 3)))
    exact ne_of_gt (by linarith)
  unfold edgeFactor
  apply ContDiff.div
  · cases image <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
  · cases image <;> dsimp [sourceZ] <;> fun_prop
  · exact hd

@[fun_prop] theorem edgeRadius_smooth (image : Bool) : ContDiff ℝ ∞ (edgeRadius image) := by
  have hp (z : Fin 4 → ℝ) : 0 < edgeFactor image (Real.exp (z 0)) (Real.exp (z 1))
      (Real.sin (z 2)^2) (Real.sin (z 3)^2) :=
    edgeFactor_pos image (Real.exp_pos _) (Real.exp_pos _)
      ⟨sq_nonneg _,Real.sin_sq_le_one _⟩ ⟨sq_nonneg _,Real.sin_sq_le_one _⟩
  have hs : ContDiff ℝ ∞ (fun z : Fin 4 → ℝ =>
      Real.sin (z 2)*(if image then 1 else Real.cos (z 3))) := by
    cases image <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop
  unfold edgeRadius
  exact contDiff_const.mul (Real.contDiff_arsinh.comp
    (hs.mul ((edgeFactor_chart_smooth image).sqrt (fun z => (hp z).ne'))))

private theorem compact_edge_radius (image : Bool) {w T a b : ℝ} (hw : 0<w) (hT : 0<T)
    (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    Real.arcosh (max 1 (compactInvariant image (sourceE image w T a) (Real.exp (-w))
      (sourceZ image w a b)))=
      2*Real.arsinh (Real.sqrt a*(if image then 1 else Real.sqrt (1-b))*
        Real.sqrt (edgeFactor image w T a b)) := by
  have hp := edgeFactor_pos image hw hT ha hb
  have hsq : (Real.sqrt a*(if image then 1 else Real.sqrt (1-b)))^2=
      a*(if image then 1 else 1-b) := by
    cases image <;> simp only [Bool.false_eq_true,↓reduceIte,mul_one]
    · rw [mul_pow,Real.sq_sqrt ha.1,Real.sq_sqrt (sub_nonneg.mpr hb.2)]
    · exact Real.sq_sqrt ha.1
  have hc : Real.cosh (2*Real.arsinh (Real.sqrt a*(if image then 1 else Real.sqrt (1-b))*
      Real.sqrt (edgeFactor image w T a b)))=
      compactInvariant image (sourceE image w T a) (Real.exp (-w)) (sourceZ image w a b) := by
    rw [Real.cosh_two_mul,Real.cosh_arsinh,Real.sinh_arsinh,
      Real.sq_sqrt (by positivity : 0 ≤ 1+(Real.sqrt a*(if image then 1 else Real.sqrt (1-b))*
        Real.sqrt (edgeFactor image w T a b))^2),mul_pow,hsq,Real.sq_sqrt hp.le]
    linear_combination -(compactInvariant_edge image w T a b)
  rw [← hc,max_eq_right (Real.one_le_cosh _),Real.arcosh_cosh]
  apply mul_nonneg (by norm_num)
  apply Real.arsinh_nonneg_iff.mpr
  cases image <;> simp only [Bool.false_eq_true,↓reduceIte] <;> positivity

theorem edgeRadius_eq (image : Bool) (W L : ℝ) {a b : ℝ}
    (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    edgeRadius image ![W,L,angleMap a,angleMap b]=
      Real.arcosh (max 1 (compactInvariant image (sourceE image (Real.exp W) (Real.exp L) a)
        (Real.exp (-Real.exp W)) (sourceZ image (Real.exp W) a b))) := by
  rw [compact_edge_radius image (Real.exp_pos _) (Real.exp_pos _) ha hb]
  change 2*Real.arsinh (Real.sin (angleMap a)*(if image then 1 else Real.cos (angleMap b))*
    Real.sqrt (edgeFactor image (Real.exp W) (Real.exp L)
      (Real.sin (angleMap a)^2) (Real.sin (angleMap b)^2)))=_
  rw [angleMap_sine_square ha,angleMap_sine_square hb,angleMap_cosine hb]
  have hs : Real.sin (angleMap a)=Real.sqrt a := by
    unfold angleMap
    exact Real.sin_arcsin (le_trans (by norm_num : (-1:ℝ)≤0) (Real.sqrt_nonneg a))
      (Real.sqrt_le_one.mpr ha.2)
  rw [hs]

private def chartParameters (z : (Fin 5 → ℝ) × (Fin 3 → ℝ)) : Fin 4 → ℝ :=
  ![z.1 1,z.1 2,z.2 0,z.2 1]

private theorem chartParameters_smooth : ContDiff ℝ ∞ chartParameters := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [chartParameters] <;> fun_prop

private def chartCircle (image : Bool) (z : (Fin 5 → ℝ) × (Fin 3 → ℝ)) : Point :=
  logCircle (edgeRadius image (chartParameters z)) (2*Real.pi*z.2 2) (z.1 3) (z.1 4)

private theorem chartCircle_smooth (image : Bool) : ContDiff ℝ ∞ (chartCircle image) := by
  have hR := (edgeRadius_smooth image).comp chartParameters_smooth
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [chartCircle,logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := intro z; exact (denominator_pos _ _).ne')

private theorem chartCircle_height_pos (image : Bool) (z : (Fin 5 → ℝ) × (Fin 3 → ℝ)) :
    0 < chartCircle image z 1 :=
  mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))

/-- Full original pulse on the two remaining compact source regions. -/
def edgeIntegrand (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : (Fin 5 → ℝ) × (Fin 3 → ℝ)) : ℂ :=
  (sourceJacobian image (Real.exp (z.1 1)) (Real.exp (z.1 2)) (Real.sin (z.2 0)^2):ℂ)*
    compactPulse q branch amp
      (sourceClock image (z.1 0) (Real.exp (z.1 1)) (Real.exp (z.1 2)) (Real.sin (z.2 0)^2))
      (sourceZ image (Real.exp (z.1 1)) (Real.sin (z.2 0)^2) (Real.sin (z.2 1)^2))
      (fullAngularField q branch (chartCircle image z)) (fullSquarePotential q (chartCircle image z))/4

theorem edgeIntegrand_smooth (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContDiff ℝ ∞ (edgeIntegrand image q branch amp) := by
  have hC := chartCircle_smooth image
  have hB : ContDiff ℝ ∞ (fun z => fullAngularField q branch (chartCircle image z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact (fullAngularField_smooth q branch _ (chartCircle_height_pos image z)).comp z hC.contDiffAt
  have hQ : ContDiff ℝ ∞ (fun z => fullSquarePotential q (chartCircle image z)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact (contDiffAt_infty.mpr (fun n =>
      fullSquarePotential_smooth q _ (chartCircle_height_pos image z) n)).comp z hC.contDiffAt
  have hv : ContDiff ℝ ∞ (fun z : (Fin 5 → ℝ) × (Fin 3 → ℝ) =>
      sourceClock image (z.1 0) (Real.exp (z.1 1)) (Real.exp (z.1 2)) (Real.sin (z.2 0)^2)) := by
    cases image <;> dsimp [sourceClock] <;> fun_prop
  have hz : ContDiff ℝ ∞ (fun z : (Fin 5 → ℝ) × (Fin 3 → ℝ) =>
      sourceZ image (Real.exp (z.1 1)) (Real.sin (z.2 0)^2) (Real.sin (z.2 1)^2)) := by
    cases image <;> dsimp [sourceZ] <;> fun_prop
  have hp (z : (Fin 5 → ℝ) × (Fin 3 → ℝ)) :
      0<1+sourceZ image (Real.exp (z.1 1)) (Real.sin (z.2 0)^2) (Real.sin (z.2 1)^2) := by
    linarith [sourceZ_nonneg image (Real.exp (z.1 1)) (Real.sin (z.2 0)^2)
      (sq_nonneg (Real.sin (z.2 1)))]
  have hF := compactPulse_comp_smooth q branch amp hv hz hB hQ hp
  have hJ : ContDiff ℝ ∞ (fun z : (Fin 5 → ℝ) × (Fin 3 → ℝ) =>
      sourceJacobian image (Real.exp (z.1 1)) (Real.exp (z.1 2)) (Real.sin (z.2 0)^2)) := by
    cases image <;> dsimp [sourceJacobian] <;> fun_prop
  have hJc : ContDiff ℝ ∞ (fun z : (Fin 5 → ℝ) × (Fin 3 → ℝ) =>
      (sourceJacobian image (Real.exp (z.1 1)) (Real.exp (z.1 2)) (Real.sin (z.2 0)^2):ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hJ
  unfold edgeIntegrand
  simpa only [div_eq_mul_inv] using
    ((hJc.mul hF).mul (contDiff_const (c := (4:ℂ)⁻¹)))

private def gamma (t : ℝ × ℝ × ℝ) : Fin 3 → ℝ :=
  ![angleMap t.1,angleMap t.2.1,t.2.2]

private theorem gamma_continuous : Continuous gamma := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact angleMap_continuous.comp continuous_fst
  · exact angleMap_continuous.comp continuous_snd.fst
  · exact continuous_snd.snd

def edgeAction (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (z : Fin 5 → ℝ) : ℂ :=
  ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
    edgeIntegrand image q branch amp (z,gamma (a,b,c))

theorem edgeAction_smooth (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContDiff ℝ ∞ (edgeAction image q branch amp) :=
  D4BMNativeResponse.unitCube_integral_smooth (edgeIntegrand_smooth image q branch amp)
    gamma gamma_continuous

/-- Original circle density in compact source radius, including the factor one quarter. -/
def compactSample (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (r w X k v z c : ℝ) : ℂ :=
  let point := logCircle (Real.arcosh (max 1 (compactInvariant image
    (Real.exp (r-w-v)) (Real.exp (-w)) z))) (2*Real.pi*c) X k
  compactPulse q branch amp v z (fullAngularField q branch point) (fullSquarePotential q point)/4

def lowerDirectIntegral (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (r w X k : ℝ) : ℂ :=
  ∫ v in (r-w)..r, ∫ z in (0:ℝ)..(Real.exp (v-r)), ∫ c in (0:ℝ)..1,
    compactSample false q branch amp r w X k v z c

def upperIntegral (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (r w T X k : ℝ) : ℂ :=
  ∫ v in r..(r+T), ∫ z in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
    compactSample image q branch amp r w X k v z c

private theorem affine_integral (f : ℝ → ℂ) (a b : ℝ) :
    (∫ x in a..b,f x)=∫ t in (0:ℝ)..1,((b-a:ℝ):ℂ)*f (a+(b-a)*t) := by
  rw [intervalIntegral.integral_const_mul]
  simpa only [mul_zero,mul_one,add_zero,show a+(b-a)=b by ring,Complex.real_smul]
    using (intervalIntegral.smul_integral_comp_add_mul (a := (0:ℝ)) (b := 1) f (b-a) a).symm

private theorem lower_change (F : ℝ → ℝ → ℝ → ℂ) (r w : ℝ) :
    (∫ v in (r-w)..r, ∫ z in (0:ℝ)..(Real.exp (v-r)), ∫ c in (0:ℝ)..1,F v z c)=
    ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
      (w*Real.exp (-w*(1-a)):ℝ)*F (r-w+w*a) (Real.exp (-w*(1-a))*b) c := by
  rw [affine_integral]
  rw [show r-(r-w)=w by ring]
  apply intervalIntegral.integral_congr
  intro a ha
  dsimp only
  rw [show r-w+w*a-r = -w*(1-a) by ring,affine_integral]
  simp only [sub_zero,zero_add]
  simp_rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro b hb
  apply intervalIntegral.integral_congr
  intro c hc
  dsimp only
  push_cast
  ring

private theorem upper_change (F : ℝ → ℝ → ℝ → ℂ) (r T : ℝ) :
    (∫ v in r..(r+T), ∫ z in (0:ℝ)..1, ∫ c in (0:ℝ)..1,F v z c)=
    ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
      (T:ℂ)*F (r+T*a) b c := by
  rw [affine_integral,show r+T-r=T by ring]
  simp_rw [intervalIntegral.integral_const_mul]

private theorem edgeIntegrand_eq_sample (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (z : Fin 5 → ℝ) {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1)
    (hb : b ∈ Icc (0:ℝ) 1) (c : ℝ) :
    edgeIntegrand image q branch amp (z,gamma (a,b,c))=
      (sourceJacobian image (Real.exp (z 1)) (Real.exp (z 2)) a:ℂ)*
        compactSample image q branch amp (z 0) (Real.exp (z 1)) (z 3) (z 4)
          (sourceClock image (z 0) (Real.exp (z 1)) (Real.exp (z 2)) a)
          (sourceZ image (Real.exp (z 1)) a b) c := by
  have he : Real.exp (z 0-Real.exp (z 1)-
      sourceClock image (z 0) (Real.exp (z 1)) (Real.exp (z 2)) a)=
      sourceE image (Real.exp (z 1)) (Real.exp (z 2)) a := by
    cases image <;> simp only [sourceClock,sourceE,Bool.false_eq_true,↓reduceIte]
    all_goals congr 1; ring
  unfold edgeIntegrand
  change (sourceJacobian image (Real.exp (z 1)) (Real.exp (z 2)) (Real.sin (angleMap a)^2):ℂ)*
    compactPulse q branch amp
      (sourceClock image (z 0) (Real.exp (z 1)) (Real.exp (z 2)) (Real.sin (angleMap a)^2))
      (sourceZ image (Real.exp (z 1)) (Real.sin (angleMap a)^2) (Real.sin (angleMap b)^2))
      (fullAngularField q branch (logCircle (edgeRadius image ![z 1,z 2,angleMap a,angleMap b])
        (2*Real.pi*c) (z 3) (z 4)))
      (fullSquarePotential q (logCircle (edgeRadius image ![z 1,z 2,angleMap a,angleMap b])
        (2*Real.pi*c) (z 3) (z 4)))/4=_
  rw [angleMap_sine_square ha,angleMap_sine_square hb,edgeRadius_eq image (z 1) (z 2) ha hb]
  unfold compactSample
  rw [he]
  ring

theorem edgeAction_eq_integral (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : Fin 5 → ℝ) : edgeAction image q branch amp z=
      if image then upperIntegral true q branch amp (z 0) (Real.exp (z 1)) (Real.exp (z 2)) (z 3) (z 4)
      else lowerDirectIntegral q branch amp (z 0) (Real.exp (z 1)) (z 3) (z 4) := by
  have he : edgeAction image q branch amp z=
      ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
      (sourceJacobian image (Real.exp (z 1)) (Real.exp (z 2)) a:ℂ)*
        compactSample image q branch amp (z 0) (Real.exp (z 1)) (z 3) (z 4)
          (sourceClock image (z 0) (Real.exp (z 1)) (Real.exp (z 2)) a)
          (sourceZ image (Real.exp (z 1)) a b) c := by
    apply intervalIntegral.integral_congr
    intro a ha
    apply intervalIntegral.integral_congr
    intro b hb
    apply intervalIntegral.integral_congr
    intro c hc
    exact edgeIntegrand_eq_sample image q branch amp z
      (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using ha)
      (by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hb) c
  rw [he]
  cases image
  · simp only [Bool.false_eq_true,↓reduceIte,sourceJacobian,sourceClock,sourceZ]
    exact (lower_change (compactSample false q branch amp (z 0) (Real.exp (z 1)) (z 3) (z 4))
      (z 0) (Real.exp (z 1))).symm
  · simp only [↓reduceIte,sourceJacobian,sourceClock,sourceZ]
    exact (upper_change (compactSample true q branch amp (z 0) (Real.exp (z 1)) (z 3) (z 4))
      (z 0) (Real.exp (z 2))).symm

private theorem upperSample_eq_compactSample (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : Fin 5 → ℝ) (a b c : ℝ) (hb : b ≤ 1) :
    upperSample q branch amp z (a,b) c=
      compactSample false q branch amp (z 0) (Real.exp (z 1)) (z 3) (z 4)
        (z 0+Real.exp (z 2)*a) (1-b) c := by
  change compactPulse q branch amp (z 0+Real.exp (z 2)*a) (max 0 (1-b))
    (fullAngularField q branch (logCircle (Real.arcosh (max 1 (compactInvariant false
      (Real.exp (-Real.exp (z 1)-Real.exp (z 2)*a)) (Real.exp (-Real.exp (z 1))) (max 0 (1-b)))))
      (2*Real.pi*c) (z 3) (z 4)))
    (fullSquarePotential q (logCircle (Real.arcosh (max 1 (compactInvariant false
      (Real.exp (-Real.exp (z 1)-Real.exp (z 2)*a)) (Real.exp (-Real.exp (z 1))) (max 0 (1-b)))))
      (2*Real.pi*c) (z 3) (z 4)))/4=_
  unfold compactSample
  rw [max_eq_right (sub_nonneg.mpr hb),show z 0-Real.exp (z 1)-(z 0+Real.exp (z 2)*a)=
    -Real.exp (z 1)-Real.exp (z 2)*a by ring]

theorem upperDirectAction_eq_integral (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : Fin 5 → ℝ) : upperDirectAction q branch amp z=
      upperIntegral false q branch amp (z 0) (Real.exp (z 1)) (Real.exp (z 2)) (z 3) (z 4) := by
  let F := compactSample false q branch amp (z 0) (Real.exp (z 1)) (z 3) (z 4)
  calc
    _ = (Real.exp (z 2):ℂ)*(∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
        F (z 0+Real.exp (z 2)*a) (1-b) c) := by
      unfold upperDirectAction
      congr 1
      apply intervalIntegral.integral_congr
      intro a ha
      apply intervalIntegral.integral_congr
      intro b hb
      apply intervalIntegral.integral_congr
      intro c hc
      exact upperSample_eq_compactSample q branch amp z a b c
        (show b ∈ Icc (0:ℝ) 1 by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hb).2
    _ = (Real.exp (z 2):ℂ)*(∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ c in (0:ℝ)..1,
        F (z 0+Real.exp (z 2)*a) b c) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro a ha
      simpa only [sub_self,sub_zero] using
        (intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := 1)
          (fun b => ∫ c in (0:ℝ)..1,F (z 0+Real.exp (z 2)*a) b c) 1)
    _ = _ := by
      unfold upperIntegral
      rw [upper_change]
      simp_rw [intervalIntegral.integral_const_mul]
      rfl

/-- A single smooth span reaches strictly beyond the original pulse for every target time. -/
def pulseSpan (r : ℝ) : ℝ := 1+Real.exp (-r)

theorem pulseSpan_pos (r : ℝ) : 0 < pulseSpan r := by unfold pulseSpan; positivity
theorem pulseSpan_covers (r : ℝ) : 2 ≤ r+pulseSpan r := by
  have h := Real.add_one_le_exp (-r)
  unfold pulseSpan
  linarith

def assemblyParameters (z : Fin 4 → ℝ) : Fin 5 → ℝ :=
  ![z 0,z 1,Real.log (pulseSpan (z 0)),z 2,z 3]

@[fun_prop] theorem assemblyParameters_smooth : ContDiff ℝ ∞ assemblyParameters := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> dsimp [assemblyParameters]
  · fun_prop
  · fun_prop
  · exact (by fun_prop : ContDiff ℝ ∞ (fun z : Fin 4 → ℝ => 1+Real.exp (-z 0))).log
      (fun z => (pulseSpan_pos (z 0)).ne')
  · fun_prop
  · fun_prop

/-- The three original compact source regions, with the retained reflected-image sign. -/
def compactFutureAction (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (z : Fin 4 → ℝ) : ℂ :=
  lowerDirectIntegral q branch amp (z 0) (Real.exp (z 1)) (z 2) (z 3)+
    upperIntegral false q branch amp (z 0) (Real.exp (z 1)) (pulseSpan (z 0)) (z 2) (z 3)-
    upperIntegral true q branch amp (z 0) (Real.exp (z 1)) (pulseSpan (z 0)) (z 2) (z 3)

theorem compactFutureAction_eq_charts (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (z : Fin 4 → ℝ) : compactFutureAction q branch amp z=
      edgeAction false q branch amp (assemblyParameters z)+
      upperDirectAction q branch amp (assemblyParameters z)-
      edgeAction true q branch amp (assemblyParameters z) := by
  rw [edgeAction_eq_integral,upperDirectAction_eq_integral,edgeAction_eq_integral]
  simp only [Bool.false_eq_true,↓reduceIte]
  change compactFutureAction q branch amp z=
    lowerDirectIntegral q branch amp (z 0) (Real.exp (z 1)) (z 2) (z 3)+
    upperIntegral false q branch amp (z 0) (Real.exp (z 1))
      (Real.exp (Real.log (pulseSpan (z 0)))) (z 2) (z 3)-
    upperIntegral true q branch amp (z 0) (Real.exp (z 1))
      (Real.exp (Real.log (pulseSpan (z 0)))) (z 2) (z 3)
  rw [Real.exp_log (pulseSpan_pos (z 0))]
  rfl

/-- The entire compact future pulse formula is smooth in every physical interior target coordinate. -/
theorem compactFutureAction_smooth (q : XiZeroCopy) (branch : Bool) (amp : ℂ) :
    ContDiff ℝ ∞ (compactFutureAction q branch amp) := by
  have he : compactFutureAction q branch amp=fun z =>
      edgeAction false q branch amp (assemblyParameters z)+
      upperDirectAction q branch amp (assemblyParameters z)-
      edgeAction true q branch amp (assemblyParameters z) := funext
    (compactFutureAction_eq_charts q branch amp)
  rw [he]
  exact (((edgeAction_smooth false q branch amp).comp assemblyParameters_smooth).add
    ((upperDirectAction_smooth q branch amp).comp assemblyParameters_smooth)).sub
      ((edgeAction_smooth true q branch amp).comp assemblyParameters_smooth)

/-- The compact sample is the original pulse at its actual future source circle. -/
theorem compactSample_original (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (r w X k v y c : ℝ) :
    compactSample image q branch amp r w X k v (Real.exp (2*y)) c=
      fullSourceOnsetPulse q branch amp (v-y) y
        (logCircle (Real.arcosh (max 1 (D4BMCausalKernel.invariant
          (v-y-(r-w/2)) (-w/2) (if image then -y else y)))) (2*Real.pi*c) X k)/
        (4*(Real.exp (2*y):ℂ)) := by
  have hi := future_invariant_compact image (r-w/2) (-w/2) v y
  rw [show r-w/2+-w/2-v=r-w-v by ring,show 2*(-w/2)=-w by ring] at hi
  unfold compactSample
  rw [hi,fullSourceOnsetPulse_compact,sub_add_cancel]
  have he : (Real.exp (2*y):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  field_simp [he]

theorem compactSample_zero_outside (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (r w X k v z c : ℝ) (hv : v ∉ Icc (0:ℝ) 1) :
    compactSample image q branch amp r w X k v z c=0 := by
  unfold compactSample compactPulse
  rw [GaloisForLFunctions.HTGeometry.deriv_smoothTransition_eq_zero_of_notMem hv]
  simp

private def sampleCircle (image : Bool) (r w X k : ℝ) (y : (ℝ × ℝ) × ℝ) : Point :=
  logCircle (Real.arcosh (max 1 (compactInvariant image (Real.exp (r-w-y.1.1))
    (Real.exp (-w)) (max 0 y.1.2)))) (2*Real.pi*y.2) X k

private theorem sampleCircle_continuous (image : Bool) (r w X k : ℝ) :
    Continuous (sampleCircle image r w X k) := by
  have hI : Continuous (fun y : (ℝ × ℝ) × ℝ =>
      compactInvariant image (Real.exp (r-w-y.1.1)) (Real.exp (-w)) (max 0 y.1.2)) := by
    cases image <;> simp only [compactInvariant,Bool.false_eq_true,↓reduceIte]
    all_goals fun_prop (disch := intro y; positivity)
  have hd : Continuous (fun y : (ℝ × ℝ) × ℝ => Real.arcosh (max 1
      (compactInvariant image (Real.exp (r-w-y.1.1)) (Real.exp (-w)) (max 0 y.1.2)))) :=
    Real.continuousOn_arcosh.comp_continuous (continuous_const.max hI)
      (fun y => (show (1:ℝ) ≤ max 1 _ from le_max_left _ _))
  apply continuous_pi
  intro i
  fin_cases i <;> dsimp [sampleCircle,logCircle,circle,offset,height,denominator]
  all_goals fun_prop (disch := intro y; exact (denominator_pos _ _).ne')

private theorem sampleCircle_height_pos (image : Bool) (r w X k : ℝ) (y : (ℝ × ℝ) × ℝ) :
    0 < sampleCircle image r w X k y 1 :=
  mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))

theorem compactSample_clamped_continuous (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (r w X k : ℝ) : Continuous (fun y : (ℝ × ℝ) × ℝ =>
      compactSample image q branch amp r w X k y.1.1 (max 0 y.1.2) y.2) := by
  have hc := sampleCircle_continuous image r w X k
  have hB : Continuous (fun y => fullAngularField q branch (sampleCircle image r w X k y)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (fullAngularField_smooth q branch _ (sampleCircle_height_pos image r w X k y)).continuousAt.comp
      hc.continuousAt
  have hQ : Continuous (fun y => fullSquarePotential q (sampleCircle image r w X k y)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (fullSquarePotential_smooth q _ (sampleCircle_height_pos image r w X k y) 0).continuousAt.comp
      hc.continuousAt
  have hF := compactPulse_comp_continuous q branch amp
    (by fun_prop : Continuous (fun y : (ℝ × ℝ) × ℝ => y.1.1))
    (by fun_prop : Continuous (fun y : (ℝ × ℝ) × ℝ => max 0 y.1.2)) hB hQ
    (fun y => by linarith [le_max_left (0:ℝ) y.1.2])
  exact hF.div_const 4

def compactMean (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (r w X k v z : ℝ) : ℂ := ∫ c in (0:ℝ)..1, compactSample image q branch amp r w X k v z c

theorem compactMean_clamped_continuous (image : Bool) (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (r w X k : ℝ) : Continuous (fun vz : ℝ × ℝ =>
      compactMean image q branch amp r w X k vz.1 (max 0 vz.2)) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (compactSample_clamped_continuous image q branch amp r w X k) 0 1

theorem compactMean_zero_outside (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (r w X k v z : ℝ) (hv : v ∉ Icc (0:ℝ) 1) :
    compactMean image q branch amp r w X k v z=0 := by
  unfold compactMean
  simp_rw [compactSample_zero_outside image q branch amp r w X k v z _ hv]
  simp

private theorem exponential_strip_limit (F : ℝ → ℝ → ℂ)
    (hF : Continuous (Function.uncurry F)) (a b : ℝ) : Filter.Tendsto
    (fun L : ℝ => ∫ v in a..b, ∫ z in (0:ℝ)..(Real.exp (v-L)), F v z)
    Filter.atTop (nhds 0) := by
  have hF' : Continuous (fun y : (ℝ × ℝ) × ℝ => F y.1.2 y.2) :=
    hF.comp (show Continuous (fun y : (ℝ × ℝ) × ℝ => (y.1.2,y.2)) by fun_prop)
  have hP : Continuous (fun ev : ℝ × ℝ => ∫ z in (0:ℝ)..(Real.exp ev.2*ev.1), F ev.2 z) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun ev : ℝ × ℝ => F ev.2) hF'
      (by fun_prop : Continuous (fun ev : ℝ × ℝ => Real.exp ev.2*ev.1))
  have hA : Continuous (fun e : ℝ => ∫ v in a..b, ∫ z in (0:ℝ)..(Real.exp v*e), F v z) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hP a b
  have hL := hA.continuousAt.tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero
  have hzero : (∫ v in a..b, ∫ z in (0:ℝ)..(Real.exp v*0),F v z)=0 := by simp
  rw [hzero] at hL
  apply hL.congr'
  exact Filter.Eventually.of_forall (fun L => by
    simp only [Function.comp_def,Real.exp_sub,Real.exp_neg,div_eq_mul_inv])

/-- The omitted compact-radius strip vanishes as the original outgoing cutoff recedes. -/
theorem compactMean_cut_tail (image : Bool) (q : XiZeroCopy) (branch : Bool) (amp : ℂ)
    (r w X k a b : ℝ) : Filter.Tendsto
      (fun L : ℝ => ∫ v in a..b, ∫ z in (0:ℝ)..(Real.exp (v-L)),
        compactMean image q branch amp r w X k v z) Filter.atTop (nhds 0) := by
  have h := exponential_strip_limit
    (fun v z => compactMean image q branch amp r w X k v (max 0 z))
    (compactMean_clamped_continuous image q branch amp r w X k) a b
  apply h.congr'
  exact Filter.Eventually.of_forall (fun L => by
    apply intervalIntegral.integral_congr
    intro v hv
    apply intervalIntegral.integral_congr
    intro z hz
    have hz0 : 0 ≤ z := (show z ∈ Icc (0:ℝ) (Real.exp (v-L)) by
      simpa only [uIcc_of_le (Real.exp_pos (v-L)).le] using hz).1
    exact congrArg (compactMean image q branch amp r w X k v) (max_eq_right hz0))

end
end RHTower.D4BMFuturePulseAssembly
