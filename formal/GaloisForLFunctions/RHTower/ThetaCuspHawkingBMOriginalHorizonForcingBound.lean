import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalHorizonSourceJets
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalHorizonRegularity
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalBaseCircleJets

/-! Uniform horizon bounds for the original principal-subtracted retarded forcing
and actual integrated base derivatives, retaining the source Jacobian, onset,
image subtraction, and hyperbolic gradient weight. -/
open Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMOriginalHorizonForcingBound
open D4BMNativeCircle D4BMSquareCuspJets D4BMGlobalAngularResponse
open D4BMOriginalHorizonRadiusDerivative D4BMOriginalHorizonSourceJets
open D4BMRetardedHorizonGeometry D4BMNativeSourceJetGrowth D4BMLaplaceRadial D4BMJointSource
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
noncomputable section
set_option autoImplicit false

private structure Site where
  image : Bool
  p : ℝ
  alpha : ℝ
  beta : ℝ
  theta : ℝ
  x : ℝ
  k : ℝ
  hp : 0 ≤ p
  ha : alpha ∈ Icc (0:ℝ) 1
  hb : beta ∈ Icc (0:ℝ) 1
  hk : 0 ≤ k

private abbrev window := Icc (-(1/4:ℝ)) (1/4)
private theorem zero_window : (0:ℝ) ∈ window := by constructor <;> norm_num
private def E (f : Site → ℝ → ℂ) (C B K : ℝ) : Prop :=
  ∀ z r, r ∈ window →
    ‖f z r‖ ≤ C*Real.exp (B*z.p+K*z.k) ∧
    ‖f z r-f z 0‖ ≤ C*Real.exp (B*z.p+K*z.k)*|r|

private theorem E_add {f g : Site → ℝ → ℂ} {C D B A K : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hB : 0 ≤ B) (hA : 0 ≤ A)
    (hf : E f C B K) (hg : E g D A K) : E (fun z r => f z r+g z r) (C+D) (B+A) K := by
  intro z r hr
  have hu : C*Real.exp (B*z.p+K*z.k)+D*Real.exp (A*z.p+K*z.k) ≤
      (C+D)*Real.exp ((B+A)*z.p+K*z.k) := by
    rw [add_mul]
    gcongr <;> nlinarith [z.hp]
  constructor
  · exact (norm_add_le _ _).trans ((add_le_add (hf z r hr).1 (hg z r hr).1).trans hu)
  · rw [show f z r+g z r-(f z 0+g z 0)=(f z r-f z 0)+(g z r-g z 0) by ring]
    apply (norm_add_le _ _).trans
    calc
      _ ≤ C*Real.exp (B*z.p+K*z.k)*|r|+D*Real.exp (A*z.p+K*z.k)*|r| :=
        add_le_add (hf z r hr).2 (hg z r hr).2
      _ = (C*Real.exp (B*z.p+K*z.k)+D*Real.exp (A*z.p+K*z.k))*|r| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hu (abs_nonneg _)

private theorem E_mul {f g : Site → ℝ → ℂ} {C D B A K L : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hf : E f C B K) (hg : E g D A L) :
    E (fun z r => f z r*g z r) (2*C*D) (B+A) (K+L) := by
  intro z r hr
  have he : C*Real.exp (B*z.p+K*z.k)*(D*Real.exp (A*z.p+L*z.k))=
      C*D*Real.exp ((B+A)*z.p+(K+L)*z.k) := by
    rw [mul_mul_mul_comm,← Real.exp_add]
    congr 2
    ring
  constructor
  · rw [norm_mul]
    apply (mul_le_mul (hf z r hr).1 (hg z r hr).1 (norm_nonneg _) (by positivity)).trans
    rw [he]
    nlinarith [Real.exp_pos ((B+A)*z.p+(K+L)*z.k),mul_nonneg hC hD]
  · rw [show f z r*g z r-f z 0*g z 0=(f z r-f z 0)*g z r+f z 0*(g z r-g z 0) by ring]
    apply (norm_add_le _ _).trans
    simp only [norm_mul]
    calc
      _ ≤ (C*Real.exp (B*z.p+K*z.k)*|r|)*(D*Real.exp (A*z.p+L*z.k))+
          (C*Real.exp (B*z.p+K*z.k))*(D*Real.exp (A*z.p+L*z.k)*|r|) := by
        gcongr
        · exact (hf z r hr).2
        · exact (hg z r hr).1
        · exact (hf z 0 zero_window).1
        · exact (hg z r hr).2
      _ = 2*(C*Real.exp (B*z.p+K*z.k)*(D*Real.exp (A*z.p+L*z.k)))*|r| := by ring
      _ = _ := by rw [he]; ring

private def Rapid (f : Site → ℝ → ℂ) : Prop :=
  ∀ N : ℕ, ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ E f C B (-(N:ℝ))

private theorem Rapid.add {f g : Site → ℝ → ℂ} (hf : Rapid f) (hg : Rapid g) :
    Rapid (fun z r => f z r+g z r) := by
  intro N
  obtain ⟨C,B,hC,hB,hf⟩ := hf N
  obtain ⟨D,A,hD,hA,hg⟩ := hg N
  exact ⟨C+D,B+A,add_nonneg hC hD,add_nonneg hB hA,E_add hC hD hB hA hf hg⟩

private theorem Rapid.mul {f g : Site → ℝ → ℂ} {D A : ℝ} (m : ℕ)
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hg : E g D A m) (hf : Rapid f) :
    Rapid (fun z r => g z r*f z r) := by
  intro N
  obtain ⟨C,B,hC,hB,hf⟩ := hf (N+m)
  refine ⟨2*D*C,A+B,by positivity,by positivity,?_⟩
  have h := E_mul hD hC hg hf
  convert h using 1
  push_cast
  ring

private theorem constant_E (c : ℂ) : E (fun _ _ => c) ‖c‖ 0 0 := by
  intro z r hr
  simp only [zero_mul,zero_add,Real.exp_zero,mul_one,sub_self,norm_zero,le_refl,true_and]
  positivity

private theorem Rapid.scale {f : Site → ℝ → ℂ} (hf : Rapid f) (c : ℂ) :
    Rapid (fun z r => c*f z r) := hf.mul 0 (norm_nonneg c) le_rfl (by simpa only [Nat.cast_zero] using constant_E c)

private def sourceSample (f : (Fin 2 → ℝ) → ℂ) (z : Site) (r : ℝ) : ℂ :=
  sample f z.image z.p r z.alpha z.beta z.theta z.x z.k

private theorem sample_rapid (f : (Fin 2 → ℝ) → ℂ)
    (hv : ∀ N : ℕ, ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ d theta x k : ℝ, 0 ≤ d → 0 ≤ k →
      ‖f (logCircle d theta x k)‖ ≤ C*Real.exp (B*d-(N:ℝ)*k))
    (hh : ∀ N : ℕ, ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ z : Site, ∀ r ∈ window,
      ‖sourceSample f z r-sourceSample f z 0‖ ≤ C*Real.exp (B*z.p-(N:ℝ)*z.k)*|r|) :
    Rapid (sourceSample f) := by
  intro N
  obtain ⟨C,B,hC,hB,hv⟩ := hv N
  obtain ⟨D,A,hD,hA,hh⟩ := hh N
  refine ⟨C*Real.exp (6*B)+D,2*B+A,by positivity,by positivity,?_⟩
  intro z r hr
  have hd := unitRadius_growth z.image z.p r z.alpha z.beta z.hp hr.1 hr.2 z.ha.1 z.ha.2 z.hb.1 z.hb.2
  constructor
  · calc
      _ ≤ C*Real.exp (B*unitRadius z.image z.p r z.alpha z.beta-(N:ℝ)*z.k) :=
        hv _ _ _ _ hd.1 z.hk
      _ ≤ C*Real.exp (B*(2*z.p+6)-(N:ℝ)*z.k) := by gcongr; exact hd.2
      _ = (C*Real.exp (6*B))*Real.exp ((2*B)*z.p+(-(N:ℝ))*z.k) := by
        rw [mul_assoc,← Real.exp_add]; congr 2; ring
      _ ≤ _ := by gcongr <;> nlinarith [z.hp]
  · have h := hh z r hr
    calc
      _ ≤ D*Real.exp (A*z.p-(N:ℝ)*z.k)*|r| := h
      _ ≤ _ := by gcongr <;> nlinarith [z.hp,Real.exp_pos (6*B)]

private theorem square_rapid (u : ℂ) (word : List (Fin 2)) :
    Rapid (sourceSample (coordinateJet word (squareRemainder u))) := by
  apply sample_rapid
  · intro N
    simpa only [Nat.cast_zero,zero_mul,Real.exp_zero,one_mul] using squareRemainder_circle_jet_bound u word N 0
  · intro N
    obtain ⟨C,B,hC,hB,hh⟩ := square_jet_horizon_estimate u word N
    exact ⟨C,B,hC,hB,fun z r hr =>
      (hh z.image z.p r z.alpha z.beta z.theta z.x z.k z.hp hr.1 hr.2 z.ha.1 z.ha.2 z.hb.1 z.hb.2 z.hk).2⟩

private theorem gradient_rapid (u : ℂ) (i j : Fin 2) (word : List (Fin 2)) :
    Rapid (sourceSample (coordinateJet word (gradientProductRemainder u i j))) := by
  apply sample_rapid
  · intro N
    simpa only [Nat.cast_zero,zero_mul,Real.exp_zero,one_mul] using gradientProductRemainder_circle_jet_bound u i j word N 0
  · intro N
    obtain ⟨C,B,hC,hB,hh⟩ := gradient_jet_horizon_estimate u i j word N
    exact ⟨C,B,hC,hB,fun z r hr =>
      (hh z.image z.p r z.alpha z.beta z.theta z.x z.k z.hp hr.1 hr.2 z.ha.1 z.ha.2 z.hb.1 z.hb.2 z.hk).2⟩

private def Y (z : Site) (r : ℝ) : ℝ :=
  Real.exp z.k*height (unitRadius z.image z.p r z.alpha z.beta) z.theta

private theorem height_bounds (d theta : ℝ) (hd : 0 ≤ d) :
    0 < height d theta ∧ height d theta ≤ Real.exp d ∧
      |heightRadial d theta| ≤ height d theta := by
  have hD := denominator_pos d theta
  have hN : |radialNumerator d theta| ≤ denominator d theta := by
    have hid : (denominator d theta)^(2 : ℕ)-(radialNumerator d theta)^(2 : ℕ)=(Real.sin theta)^(2 : ℕ) := by
      calc
        _ = (Real.cosh d^(2 : ℕ)-Real.sinh d^(2 : ℕ))*(1-Real.cos theta^(2 : ℕ)) := by unfold denominator radialNumerator; ring
        _ = _ := by rw [Real.cosh_sq_sub_sinh_sq]; nlinarith [Real.sin_sq_add_cos_sq theta]
    nlinarith [sq_nonneg (Real.sin theta),sq_abs (radialNumerator d theta)]
  have hlo : Real.exp (-d) ≤ denominator d theta := by
    rw [← Real.cosh_sub_sinh]
    unfold denominator
    nlinarith [Real.sinh_nonneg_iff.mpr hd,Real.cos_le_one theta]
  refine ⟨one_div_pos.mpr hD,?_,?_⟩
  · calc
      _ ≤ 1/Real.exp (-d) := one_div_le_one_div_of_le (Real.exp_pos _) hlo
      _ = _ := by rw [Real.exp_neg]; field_simp
  · rw [heightRadial,abs_div,abs_neg,abs_of_pos (sq_pos_of_pos hD)]
    calc
      _ ≤ denominator d theta/(denominator d theta)^(2 : ℕ) := div_le_div_of_nonneg_right hN (sq_nonneg _)
      _ = _ := by unfold height; field_simp

private theorem Y_bounds (z : Site) (r : ℝ) (hr : r ∈ window) :
    0 < Y z r ∧ Y z r ≤ Real.exp (z.k+2*z.p+6) ∧
    DifferentiableAt ℝ (Y z) r ∧ |deriv (Y z) r| ≤ 4*Real.exp (z.k+2*z.p+6) := by
  have hd := unitRadius_growth z.image z.p r z.alpha z.beta z.hp hr.1 hr.2 z.ha.1 z.ha.2 z.hb.1 z.hb.2
  have hb := height_bounds _ z.theta hd.1
  have hR := (unitRadius_hasDerivAt z.image z.p r z.alpha z.beta z.hp hr.1 hr.2 z.ha.2 z.hb.1 z.hb.2).differentiableAt.hasDerivAt
  have hY := (((height_radial_derivatives _ z.theta).1.comp r hR).const_mul (Real.exp z.k))
  simp only [Function.comp_def] at hY
  have hv : Y z r ≤ Real.exp (z.k+2*z.p+6) := by
    calc
      _ ≤ Real.exp z.k*Real.exp (unitRadius z.image z.p r z.alpha z.beta) :=
        mul_le_mul_of_nonneg_left hb.2.1 (Real.exp_nonneg _)
      _ = Real.exp (z.k+unitRadius z.image z.p r z.alpha z.beta) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [hd.2])
  refine ⟨mul_pos (Real.exp_pos _) hb.1,hv,hY.differentiableAt,?_⟩
  change |deriv (fun r => Real.exp z.k*height (unitRadius z.image z.p r z.alpha z.beta) z.theta) r| ≤ _
  rw [hY.deriv,abs_mul,abs_of_pos (Real.exp_pos _),abs_mul]
  have hV := (unitRadius_horizon_derivative_bound z.image z.p r z.alpha z.beta z.hp hr.1 hr.2 z.ha.2 z.hb.1 z.hb.2).2
  calc
    _ ≤ Real.exp z.k*(height (unitRadius z.image z.p r z.alpha z.beta) z.theta*4) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul hb.2.2 hV (abs_nonneg _) hb.1.le) (Real.exp_nonneg _)
    _ = 4*Y z r := by unfold Y; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hv (by norm_num)

private theorem height_E : E (fun z r => (Y z r:ℂ)) (4*Real.exp 6) 2 1 := by
  intro z r hr
  have he : 4*Real.exp (z.k+2*z.p+6)=4*Real.exp 6*Real.exp (2*z.p+1*z.k) := by
    rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have hv := Y_bounds z r hr
  constructor
  · rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv.1]
    have h := Real.exp_pos (z.k+2*z.p+6)
    calc
      _ ≤ Real.exp (z.k+2*z.p+6) := hv.2.1
      _ ≤ 4*Real.exp (z.k+2*z.p+6) := by linarith
      _ = _ := he
  · have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (Y_bounds z s hs).2.2.1)
      (fun s hs => (show ‖deriv (Y z) s‖ ≤ 4*Real.exp (z.k+2*z.p+6) by
        simpa only [Real.norm_eq_abs] using (Y_bounds z s hs).2.2.2))
      (convex_Icc (-(1/4:ℝ)) (1/4)) zero_window hr
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    simpa only [Real.norm_eq_abs,sub_zero,he] using h

private theorem source_bounds (z : Site) (r : ℝ) (hr : r ∈ window) :
    sourceZ z.image z.p r z.alpha z.beta ∈ Icc (-(1/4:ℝ)) 1 ∧
    |sourceZ z.image z.p r z.alpha z.beta-sourceZ z.image z.p 0 z.alpha z.beta| ≤ |r| ∧
    |z.p*(1-sourceLower z.image z.p r z.alpha)| ≤ 2*Real.exp z.p ∧
    |z.p*(1-sourceLower z.image z.p r z.alpha)-z.p*(1-sourceLower z.image z.p 0 z.alpha)| ≤
      2*Real.exp z.p*|r| := by
  let e := Real.exp (-(z.p*(1-z.alpha)))
  have he0 : 0 ≤ e := Real.exp_nonneg _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [z.hp,z.ha.2])
  have hre : -(1/4:ℝ) ≤ r*e ∧ r*e ≤ 1/4 := by
    constructor <;> nlinarith [hr.1,hr.2,mul_nonneg (by linarith [hr.1] : 0 ≤ r+1/4) he0,
      mul_nonneg (by linarith [hr.2] : 0 ≤ 1/4-r) he0]
  have hb0 := z.hb.1
  have hb1 := z.hb.2
  have hp : z.p ≤ Real.exp z.p := by linarith [Real.add_one_le_exp z.p]
  cases hi : z.image
  · simp only [sourceZ,sourceLower,Bool.false_eq_true,↓reduceIte,zero_mul]
    change _ ∈ Icc (-(1/4:ℝ)) 1 ∧ |r*e+(1-r*e)*z.beta-(0+(1-0)*z.beta)| ≤ |r| ∧ _
    refine ⟨⟨?_,?_⟩,?_,?_,?_⟩
    · nlinarith [hre.1,mul_nonneg (by linarith [hre.1] : 0 ≤ r*e+1/4) (sub_nonneg.mpr hb1)]
    · nlinarith [hre.2,mul_nonneg (by linarith [hre.2] : 0 ≤ 1-r*e) (sub_nonneg.mpr hb1)]
    · rw [show r*e+(1-r*e)*z.beta-(0+(1-0)*z.beta)=r*(e*(1-z.beta)) by ring,abs_mul,
        abs_of_nonneg (mul_nonneg he0 (sub_nonneg.mpr hb1))]
      nlinarith [abs_nonneg r,mul_le_mul_of_nonneg_left (show e*(1-z.beta) ≤ 1 by nlinarith) (abs_nonneg r)]
    · change |z.p*(1-r*e)| ≤ _
      rw [abs_of_nonneg (mul_nonneg z.hp (by linarith [hre.2]))]
      nlinarith [mul_le_mul_of_nonneg_left (show 1-r*e ≤ 2 by linarith [hre.1]) z.hp]
    · change |z.p*(1-r*e)-z.p*(1-0)| ≤ _
      rw [show z.p*(1-r*e)-z.p*(1-0)=-(z.p*e)*r by ring,abs_mul,abs_neg,
        abs_of_nonneg (mul_nonneg z.hp he0)]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg r)
      have hpe : z.p*e ≤ z.p := by nlinarith [z.hp]
      linarith [Real.exp_pos z.p]
  · simp only [sourceZ,sourceLower,↓reduceIte,one_mul,sub_self,abs_zero]
    change e+(1-e)*z.beta ∈ Icc (-(1/4:ℝ)) 1 ∧ _
    refine ⟨⟨by nlinarith [mul_nonneg (sub_nonneg.mpr he1) hb0],by nlinarith [mul_nonneg (sub_nonneg.mpr he1) (sub_nonneg.mpr hb1)]⟩,
      abs_nonneg _,?_,by positivity⟩
    change |z.p*(1-e)| ≤ _
    rw [abs_of_nonneg (mul_nonneg z.hp (sub_nonneg.mpr he1))]
    nlinarith [mul_nonneg z.hp he0,Real.exp_pos z.p]

private theorem jacobian_E : E (fun z r => (z.p*(1-sourceLower z.image z.p r z.alpha):ℝ)) 2 1 0 := by
  intro z r hr
  have h := source_bounds z r hr
  simpa only [one_mul,zero_mul,add_zero,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using h.2.2

private def coefficient (s amp : ℂ) (gradient : Bool) (z : ℝ) : ℂ :=
  (-8*(compactUnit z:ℂ)/(1+(z:ℂ))^(2 : ℕ)*power (2*s) (2/(1+z))*amp^(2 : ℕ))*
    (if gradient then -(s*(s-1)*(compactUnit z:ℂ)^(2 : ℕ)/4)
      else (5*s^(2 : ℕ)+15*s+4)/4+s*(s-1)*(compactUnit z:ℂ)^(2 : ℕ)/4*(s+2)^(2 : ℕ))

private theorem coefficient_smooth (s amp : ℂ) (gradient : Bool) :
    ContDiffOn ℝ ∞ (coefficient s amp gradient) (Ioi (-1:ℝ)) := by
  have hn (z : ℝ) (hz : z ∈ Ioi (-1:ℝ)) : 1+z ≠ 0 := by simp only [mem_Ioi] at hz; linarith
  have hUR : ContDiffOn ℝ ∞ compactUnit (Ioi (-1:ℝ)) :=
    (contDiffOn_const.sub contDiffOn_id).div (contDiffOn_const.add contDiffOn_id) hn
  have hU : ContDiffOn ℝ ∞ (fun z : ℝ => (compactUnit z:ℂ)) (Ioi (-1:ℝ)) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hUR
  have hP : ContDiffOn ℝ ∞ (fun z : ℝ => power (2*s) (2/(1+z))) (Ioi (-1:ℝ)) := by
    have hbase : ContDiffOn ℝ ∞ (fun z : ℝ => 2/(1+z)) (Ioi (-1:ℝ)) :=
      contDiffOn_const.div (contDiffOn_const.add contDiffOn_id) hn
    have hpos (z : ℝ) (hz : z ∈ Ioi (-1:ℝ)) : 0 < 2/(1+z) := by
      change -1 < z at hz
      exact div_pos (by norm_num) (by linarith)
    have hlog := hbase.log (fun z hz => (hpos z hz).ne')
    have he := ((contDiffOn_const (c := 2*s)).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hlog)).cexp
    simp only [Function.comp_def,Complex.ofRealCLM_apply] at he
    apply he.congr
    intro z hz
    rw [power,Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hpos z hz).ne'),← Complex.ofReal_log (hpos z hz).le]
    congr 1
    ring
  have hQ : ContDiffOn ℝ ∞ (fun z : ℝ => -8*(compactUnit z:ℂ)/(1+(z:ℂ))^(2 : ℕ)) (Ioi (-1:ℝ)) := by
    have hR : ContDiffOn ℝ ∞ (fun z : ℝ => -8*compactUnit z/(1+z)^(2 : ℕ)) (Ioi (-1:ℝ)) :=
      (contDiffOn_const.mul hUR).div ((contDiffOn_const.add contDiffOn_id).pow 2)
        (fun z hz => pow_ne_zero 2 (hn z hz))
    have h := Complex.ofRealCLM.contDiff.comp_contDiffOn hR
    simpa only [Function.comp_def,Complex.ofRealCLM_apply,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_neg,
      Complex.ofReal_ofNat,Complex.ofReal_pow,Complex.ofReal_add,Complex.ofReal_one] using h
  have hpre : ContDiffOn ℝ ∞ (fun z : ℝ => -8*(compactUnit z:ℂ)/(1+(z:ℂ))^(2 : ℕ)*power (2*s) (2/(1+z))*amp^(2 : ℕ)) (Ioi (-1:ℝ)) :=
    (hQ.mul hP).mul contDiffOn_const
  cases gradient
  · exact hpre.mul (contDiffOn_const.add (((contDiffOn_const.mul (hU.pow 2)).div_const 4).mul contDiffOn_const))
  · exact hpre.mul (((contDiffOn_const.mul (hU.pow 2)).div_const 4).neg)

private theorem compact_coefficient_E (f : ℝ → ℂ) (hf : ContDiffOn ℝ ∞ f (Ioi (-1:ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ E (fun z r => f (sourceZ z.image z.p r z.alpha z.beta)) C 0 0 := by
  have hi : Icc (-(1/4:ℝ)) 1 ⊆ Ioi (-1:ℝ) := by intro x hx; simp only [mem_Ioi]; linarith [hx.1]
  obtain ⟨A,hA⟩ := (isCompact_Icc : IsCompact (Icc (-(1/4:ℝ)) 1)).exists_bound_of_continuousOn (hf.continuousOn.mono hi)
  obtain ⟨B,hB⟩ := (isCompact_Icc : IsCompact (Icc (-(1/4:ℝ)) 1)).exists_bound_of_continuousOn
    ((hf.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)).mono hi)
  let C := max A 0+max B 0
  have hC : 0 ≤ C := add_nonneg (le_max_right _ _) (le_max_right _ _)
  have hAC : A ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_right (le_max_right _ _))
  have hBC : B ≤ C := (le_max_left _ _).trans (le_add_of_nonneg_left (le_max_right _ _))
  refine ⟨C,hC,?_⟩
  intro z r hr
  have hrange := (source_bounds z r hr).1
  have hzero := (source_bounds z 0 zero_window).1
  simp only [zero_mul,zero_add,Real.exp_zero,mul_one]
  refine ⟨(hA _ hrange).trans hAC,?_⟩
  have hd (x : ℝ) (hx : x ∈ Icc (-(1/4:ℝ)) 1) : DifferentiableAt ℝ f x :=
    (hf.contDiffAt (isOpen_Ioi.mem_nhds (hi hx))).differentiableAt (by simp)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hd
    (fun x hx => (hB x hx).trans hBC) (convex_Icc (-(1/4:ℝ)) 1) hzero hrange
  calc
    _ ≤ C*‖sourceZ z.image z.p r z.alpha z.beta-sourceZ z.image z.p 0 z.alpha z.beta‖ := h
    _ ≤ C*|r| := by rw [Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (source_bounds z r hr).2.1 hC

private theorem onset_E (s : ℂ) : E (fun z _ => timeOnset (2*s) (z.p*z.alpha)) 1 (2*‖s‖) 0 := by
  intro z r hr
  have ht : 0 ≤ z.p*z.alpha := mul_nonneg z.hp z.ha.1
  have ht1 : z.p*z.alpha ≤ z.p := by nlinarith [z.hp,z.ha.2]
  constructor
  · have hc : ‖(Real.smoothTransition (z.p*z.alpha):ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg _)] using Real.smoothTransition.le_one (z.p*z.alpha)
    unfold timeOnset
    rw [norm_mul]
    calc
      _ ≤ 1*‖Complex.exp (2*s*(z.p*z.alpha:ℝ))‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ _ := by
        rw [Complex.norm_exp]
        simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.re_ofNat,Complex.im_ofNat,mul_zero,sub_zero,zero_mul,add_zero,one_mul]
        apply Real.exp_le_exp.mpr
        have hs : s.re ≤ ‖s‖ := Complex.re_le_norm s
        nlinarith [mul_le_mul_of_nonneg_right hs ht,mul_le_mul_of_nonneg_left ht1 (norm_nonneg s)]
  · rw [sub_self,norm_zero]
    positivity

/-- The complete principal-subtracted original forcing on its actual source circle,
with the fixed source-square Jacobian, onset and gradient height weight retained. -/
def forcingRemainder (u s amp : ℂ) (image : Bool) (p rho alpha beta theta x k : ℝ) : ℂ :=
  (p*(1-sourceLower image p rho alpha):ℝ)*compactForcing s amp (p*alpha) (sourceZ image p rho alpha beta)
    (sample (squareRemainder u) image p rho alpha beta theta x k/2)
    ((logCircle (unitRadius image p rho alpha beta) theta x k 1:ℂ)^(2 : ℕ)*
      (sample (gradientProductRemainder u 0 0) image p rho alpha beta theta x k+
       sample (gradientProductRemainder u 1 1) image p rho alpha beta theta x k)/2)/4

private theorem forcing_rapid (u s amp : ℂ) :
    Rapid (fun z r => forcingRemainder u s amp z.image z.p r z.alpha z.beta z.theta z.x z.k) := by
  obtain ⟨C,hC,hJ⟩ := compact_coefficient_E _ (coefficient_smooth s amp false)
  obtain ⟨D,hD,hK⟩ := compact_coefficient_E _ (coefficient_smooth s amp true)
  have hsquare := (square_rapid u []).scale (1/2)
  have hgrad := ((gradient_rapid u 0 0 []).add (gradient_rapid u 1 1 []))
  have hheight := E_mul (by positivity : 0 ≤ 4*Real.exp 6) (by positivity : 0 ≤ 4*Real.exp 6) height_E height_E
  have henergy := (hgrad.mul (D := 2*(4*Real.exp 6)*(4*Real.exp 6)) (A := 4) 2 (by positivity) (by norm_num) (by norm_num at hheight ⊢; exact hheight)).scale (1/2)
  have hsum := (hsquare.mul 0 hC le_rfl (by simpa only [Nat.cast_zero] using hJ)).add (henergy.mul 0 hD le_rfl (by simpa only [Nat.cast_zero] using hK))
  have honset := hsum.mul (D := 1) (A := 2*‖s‖) 0 zero_le_one (by positivity) (by simpa only [Nat.cast_zero] using onset_E s)
  have hjac := honset.mul (D := 2) (A := 1) 0 (by norm_num) zero_le_one (by simpa only [Nat.cast_zero] using jacobian_E)
  have hfinal := hjac.scale (1/4)
  convert hfinal using 1
  funext z r
  dsimp [forcingRemainder,coefficient,sourceSample,coordinateJet,Y,logCircle,circle]
  unfold compactForcing
  ring

/-- The original forcing remainder has arbitrary cusp decay, exponential time growth,
and a horizon Taylor estimate uniform on both entire source triangles. -/
theorem original_forcing_horizon_estimate (u s amp : ℂ) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ image : Bool, ∀ p rho alpha beta theta x k : ℝ,
      0 ≤ p → -(1/4:ℝ) ≤ rho → rho ≤ 1/4 → 0 ≤ alpha → alpha ≤ 1 →
      0 ≤ beta → beta ≤ 1 → 0 ≤ k →
      ‖forcingRemainder u s amp image p rho alpha beta theta x k‖ ≤ C*Real.exp (B*p-(N:ℝ)*k) ∧
      ‖forcingRemainder u s amp image p rho alpha beta theta x k-
        forcingRemainder u s amp image p 0 alpha beta theta x k‖ ≤ C*Real.exp (B*p-(N:ℝ)*k)*|rho| := by
  obtain ⟨C,B,hC,hB,h⟩ := forcing_rapid u s amp N
  refine ⟨C,B,hC,hB,?_⟩
  intro image p rho alpha beta theta x k hp hr0 hr1 ha0 ha1 hb0 hb1 hk
  simpa only [E,neg_mul,sub_eq_add_neg] using
    h ⟨image,p,alpha,beta,theta,x,k,hp,⟨ha0,ha1⟩,⟨hb0,hb1⟩,hk⟩ rho ⟨hr0,hr1⟩

/-- The principal terms of the same original source density, with the same Jacobian. -/
def principalForcing (u s amp : ℂ) (image : Bool) (p rho alpha beta theta x k : ℝ) : ℂ :=
  let v := logCircle (unitRadius image p rho alpha beta) theta x k
  (p*(1-sourceLower image p rho alpha):ℝ)*compactForcing s amp (p*alpha) (sourceZ image p rho alpha beta)
    (principal u v^(2 : ℕ)/2)
    ((v 1:ℂ)^(2 : ℕ)*((coordDeriv 0 (principal u) v)^(2 : ℕ)+(coordDeriv 1 (principal u) v)^(2 : ℕ))/2)/4

/-- Exact subtraction from the existing original causal-source integrand. -/
theorem forcingRemainder_eq_original (q : XiZeroCopy) (branch image : Bool) (amp : ℂ)
    (p rho alpha beta theta x k : ℝ) (hp : 0 < p)
    (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4)
    (ha : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    forcingRemainder (center q) (D4BMModularCore.physicalRate q branch) amp image p rho alpha beta theta x k =
      (p*(1-sourceLower image p rho alpha):ℝ)*
        D4BMOriginalHorizonRegularity.compactSample image q branch amp p rho x k
          (p*alpha) (sourceZ image p rho alpha beta) theta/4-
      principalForcing (center q) (D4BMModularCore.physicalRate q branch) amp image p rho alpha beta theta x k := by
  unfold D4BMOriginalHorizonRegularity.compactSample
  rw [show p-p*alpha=p*(1-alpha) by ring,← unitRadius_eq_original image hp hr0 hr1 ha hb0 hb1]
  dsimp [forcingRemainder,principalForcing,sample,squareRemainder,gradientProductRemainder,
    D4BMModularCore.fullSquarePotential,D4BMModularCore.fullGradientEnergy]
  unfold compactForcing
  ring

/-- Integral of the complete original forcing remainder over the normalized source cube. -/
def triangleRemainder (u s amp : ℂ) (image : Bool) (p rho x k : ℝ) : ℂ :=
  ∫ alpha in (0:ℝ)..1, ∫ beta in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
    forcingRemainder u s amp image p rho alpha beta (2*Real.pi*t) x k

/-- Integral of the horizon variation on the same normalized source cube. -/
def triangleVariation (u s amp : ℂ) (image : Bool) (p rho x k : ℝ) : ℂ :=
  ∫ alpha in (0:ℝ)..1, ∫ beta in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
    (forcingRemainder u s amp image p rho alpha beta (2*Real.pi*t) x k-
     forcingRemainder u s amp image p 0 alpha beta (2*Real.pi*t) x k)

private theorem average_unit (f : ℝ → ℂ) :
    D4BMNativeCircle.average f=∫ t in (0:ℝ)..1, f (2*Real.pi*t) := by
  unfold D4BMNativeCircle.average
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)]
  have h := intervalIntegral.smul_integral_comp_add_mul (a := (0:ℝ)) (b := 1) f (2*Real.pi) 0
  simp only [mul_zero,mul_one,zero_add,Complex.real_smul] at h
  rw [← h]
  have hn : (2*Real.pi:ℂ) ≠ 0 := by exact_mod_cast (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero)
  push_cast
  field_simp

/-- The source-cube remainder retains the existing original source and its exact
normalized circle average, with only its explicit principal terms subtracted. -/
theorem triangleRemainder_eq_original (q : XiZeroCopy) (branch image : Bool) (amp : ℂ)
    (p rho x k : ℝ) (hp : 0 < p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4) :
    triangleRemainder (center q) (D4BMModularCore.physicalRate q branch) amp image p rho x k=
      ∫ alpha in (0:ℝ)..1, ∫ beta in (0:ℝ)..1, D4BMNativeCircle.average (fun theta =>
        (p*(1-sourceLower image p rho alpha):ℝ)*
          D4BMOriginalHorizonRegularity.compactSample image q branch amp p rho x k
            (p*alpha) (sourceZ image p rho alpha beta) theta/4-
        principalForcing (center q) (D4BMModularCore.physicalRate q branch) amp image p rho alpha beta theta x k) := by
  apply intervalIntegral.integral_congr
  intro alpha ha
  apply intervalIntegral.integral_congr
  intro beta hb
  dsimp only
  rw [average_unit]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ha hb
  exact forcingRemainder_eq_original q branch image amp p rho alpha beta (2*Real.pi*t) x k hp hr0 hr1 ha.2 hb.1 hb.2

private theorem cube_norm_bound (f : ℝ → ℝ → ℝ → ℂ) (C : ℝ)
    (h : ∀ a ∈ Icc (0:ℝ) 1, ∀ b ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, ‖f a b t‖ ≤ C) :
    ‖∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f a b t‖ ≤ C := by
  have hi {g : ℝ → ℂ} (hg : ∀ a ∈ Icc (0:ℝ) 1, ‖g a‖ ≤ C) : ‖∫ a in (0:ℝ)..1, g a‖ ≤ C := by
    have H := intervalIntegral.norm_integral_le_of_norm_le_const (fun a ha => hg a
      (by rw [uIoc_of_le zero_le_one] at ha; exact ⟨ha.1.le,ha.2⟩))
    simpa only [sub_zero,abs_one,mul_one] using H
  apply hi
  intro a ha
  apply hi
  intro b hb
  apply hi
  exact h a ha b hb

/-- Normalized source integration preserves the uniform horizon/cusp/time envelope. -/
theorem original_source_cube_horizon_estimate (u s amp : ℂ) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ image : Bool, ∀ p rho x k : ℝ,
      0 ≤ p → -(1/4:ℝ) ≤ rho → rho ≤ 1/4 → 0 ≤ k →
      ‖triangleRemainder u s amp image p rho x k‖ ≤ C*Real.exp (B*p-(N:ℝ)*k) ∧
      ‖triangleVariation u s amp image p rho x k‖ ≤ C*Real.exp (B*p-(N:ℝ)*k)*|rho| := by
  obtain ⟨C,B,hC,hB,h⟩ := original_forcing_horizon_estimate u s amp N
  refine ⟨C,B,hC,hB,?_⟩
  intro image p rho x k hp hr0 hr1 hk
  constructor
  · apply cube_norm_bound
    intro a ha b hb t ht
    exact (h image p rho a b (2*Real.pi*t) x k hp hr0 hr1 ha.1 ha.2 hb.1 hb.2 hk).1
  · apply cube_norm_bound
    intro a ha b hb t ht
    exact (h image p rho a b (2*Real.pi*t) x k hp hr0 hr1 ha.1 ha.2 hb.1 hb.2 hk).2

private theorem forcing_expansion (s amp : ℂ) (a z : ℝ) (J K : ℂ) :
    compactForcing s amp a z J K=
      (coefficient s amp false z*J+coefficient s amp true z*K)*timeOnset (2*s) a := by
  unfold compactForcing coefficient
  simp only [Bool.false_eq_true,↓reduceIte]
  ring

private abbrev Cube := Icc (0:ℝ) 1 ×ˢ (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1)

private theorem forcing_cube_continuous (u s amp : ℂ) (image : Bool) (p rho x k : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (_hr1 : rho ≤ 1/4) :
    ContinuousOn (fun v : ℝ × ℝ × ℝ =>
      forcingRemainder u s amp image p rho v.1 v.2.1 (2*Real.pi*v.2.2) x k) Cube := by
  intro v hv
  have hz : 0 < 1+sourceZ image p rho v.1 v.2.1 :=
    sourceZ_add_one_pos image hp (by linarith) hv.1.2 hv.2.1.1 hv.2.1.2
  have hZ : Continuous (fun t : ℝ × ℝ × ℝ => sourceZ image p rho t.1 t.2.1) := by
    cases image <;> dsimp [sourceZ,sourceLower] <;> fun_prop
  have hL : Continuous (fun t : ℝ × ℝ × ℝ => sourceLower image p rho t.1) := by
    cases image <;> dsimp [sourceLower] <;> fun_prop
  have hLa := hL.continuousAt (x := v)
  have hQ : Continuous (fun t : ℝ × ℝ × ℝ => expc (p*(1-t.1))) := expc_smooth.continuous.comp (by fun_prop)
  have hF : ContinuousAt (fun t : ℝ × ℝ × ℝ => horizonFactor image p rho t.1 t.2.1) v := by
    unfold horizonFactor
    apply ContinuousAt.div
    · fun_prop
    · exact continuousAt_const.mul (continuousAt_const.add hZ.continuousAt)
    · exact mul_ne_zero (by linarith) hz.ne'
  have hR : ContinuousAt (fun t : ℝ × ℝ × ℝ => unitRadius image p rho t.1 t.2.1) v := by
    unfold unitRadius
    fun_prop
  let c : (ℝ × ℝ × ℝ) → (Fin 2 → ℝ) := fun t =>
    logCircle (unitRadius image p rho t.1 t.2.1) (2*Real.pi*t.2.2) x k
  have hC : ContinuousAt c v := by
    apply continuousAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [c,logCircle,circle,offset,height,denominator]
    all_goals fun_prop (disch := exact (denominator_pos _ _).ne')
  have hc : 0 < c v 1 := mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hsample (f : (Fin 2 → ℝ) → ℂ) (hf : ContDiffOn ℝ ∞ f D4BMAngularSeries.domain) :
      ContinuousAt (fun t : ℝ × ℝ × ℝ => sample f image p rho t.1 t.2.1 (2*Real.pi*t.2.2) x k) v := by
    exact (hf.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hc)).continuousAt.comp hC
  have hS := hsample _ (squareRemainder_jet_smooth u [])
  have hG0 := hsample _ (gradientProductRemainder_jet_smooth u 0 0 [])
  have hG1 := hsample _ (gradientProductRemainder_jet_smooth u 1 1 [])
  simp only [coordinateJet] at hS hG0 hG1
  have hcoef (b : Bool) : ContinuousAt (fun t : ℝ × ℝ × ℝ => coefficient s amp b (sourceZ image p rho t.1 t.2.1)) v :=
    ((coefficient_smooth s amp b).contDiffAt (isOpen_Ioi.mem_nhds (by change -1 < sourceZ image p rho v.1 v.2.1; linarith))).continuousAt.comp hZ.continuousAt
  have hj := hcoef false
  have hg := hcoef true
  have hY : ContinuousAt (fun t : ℝ × ℝ × ℝ => (c t 1:ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp ((continuous_apply 1).continuousAt.comp hC)
  apply ContinuousAt.continuousWithinAt
  simp only [forcingRemainder,forcing_expansion]
  change ContinuousAt (fun t : ℝ × ℝ × ℝ =>
    (p*(1-sourceLower image p rho t.1):ℝ)*
      ((coefficient s amp false (sourceZ image p rho t.1 t.2.1)*
          (sample (squareRemainder u) image p rho t.1 t.2.1 (2*Real.pi*t.2.2) x k/2)+
        coefficient s amp true (sourceZ image p rho t.1 t.2.1)*
          ((c t 1:ℂ)^(2 : ℕ)*(sample (gradientProductRemainder u 0 0) image p rho t.1 t.2.1 (2*Real.pi*t.2.2) x k+
            sample (gradientProductRemainder u 1 1) image p rho t.1 t.2.1 (2*Real.pi*t.2.2) x k)/2))*
        timeOnset (2*s) (p*t.1))/4) v
  have hJac : ContinuousAt (fun t : ℝ × ℝ × ℝ => ((p*(1-sourceLower image p rho t.1):ℝ):ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul (continuousAt_const.sub hLa))
  have hT : ContinuousAt (fun t : ℝ × ℝ × ℝ => timeOnset (2*s) (p*t.1)) v := by
    unfold timeOnset
    fun_prop
  exact (hJac.mul (((hj.mul (hS.div_const 2)).add
    (hg.mul (((hY.pow 2).mul (hG0.add hG1)).div_const 2))).mul hT)).div_const 4


private theorem cube_sub_integral (f g : ℝ × ℝ × ℝ → ℂ)
    (hf : ContinuousOn f Cube) (hg : ContinuousOn g Cube) :
    (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, (f (a,b,t)-g (a,b,t)))=
    (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f (a,b,t))-
    (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, g (a,b,t)) := by
  let μ := MeasureTheory.volume.restrict (Icc (0:ℝ) 1)
  have eqprod (f : ℝ × ℝ × ℝ → ℂ) (hf : ContinuousOn f Cube) :
      (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f (a,b,t))=
        ∫ v, f v ∂(μ.prod (μ.prod μ)) := by
    have hi : MeasureTheory.Integrable f (μ.prod (μ.prod μ)) := by
      dsimp [μ]
      rw [MeasureTheory.Measure.prod_restrict,MeasureTheory.Measure.prod_restrict]
      exact hf.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
    rw [MeasureTheory.integral_prod _ hi]
    simp only [intervalIntegral.integral_of_le zero_le_one,← MeasureTheory.integral_Icc_eq_integral_Ioc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with a ha
    have hj : MeasureTheory.Integrable (fun bt : ℝ × ℝ => f (a,bt)) (μ.prod μ) := by
      dsimp [μ]
      rw [MeasureTheory.Measure.prod_restrict]
      exact (hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun bt hbt => ⟨ha,hbt⟩)).integrableOn_compact
        (isCompact_Icc.prod isCompact_Icc)
    exact (MeasureTheory.integral_prod _ hj).symm
  have integ (f : ℝ × ℝ × ℝ → ℂ) (hf : ContinuousOn f Cube) :
      MeasureTheory.Integrable f (μ.prod (μ.prod μ)) := by
    dsimp [μ]
    rw [MeasureTheory.Measure.prod_restrict,MeasureTheory.Measure.prod_restrict]
    exact hf.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  rw [eqprod (fun v => f v-g v) (hf.sub hg),eqprod f hf,eqprod g hg]
  exact MeasureTheory.integral_sub (integ f hf) (integ g hg)

/-- The integrated variation is the difference of the actual source-cube integrals. -/
theorem triangleVariation_eq_sub (u s amp : ℂ) (image : Bool) (p rho x k : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4) :
    triangleVariation u s amp image p rho x k=
      triangleRemainder u s amp image p rho x k-triangleRemainder u s amp image p 0 x k :=
  cube_sub_integral _ _ (forcing_cube_continuous u s amp image p rho x k hp hr0 hr1)
    (forcing_cube_continuous u s amp image p 0 x k hp (by norm_num) (by norm_num))

/-- The complete direct-minus-image retarded source remainder. -/
def actionRemainder (u s amp : ℂ) (p rho x k : ℝ) : ℂ :=
  triangleRemainder u s amp false p rho x k-triangleRemainder u s amp true p rho x k

/-- The direct-minus-image horizon variation of the complete retarded source remainder. -/
def actionVariation (u s amp : ℂ) (p rho x k : ℝ) : ℂ :=
  triangleVariation u s amp false p rho x k-triangleVariation u s amp true p rho x k

/-- Exact horizon subtraction commutes with both original source integrations. -/
theorem actionVariation_eq_sub (u s amp : ℂ) (p rho x k : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4) :
    actionVariation u s amp p rho x k=actionRemainder u s amp p rho x k-actionRemainder u s amp p 0 x k := by
  rw [actionVariation,triangleVariation_eq_sub u s amp false p rho x k hp hr0 hr1,
    triangleVariation_eq_sub u s amp true p rho x k hp hr0 hr1]
  unfold actionRemainder
  ring

/-- Exponential time damping controls the original horizon variation uniformly in
its upper time cutoff, without relating that cutoff to the cusp or horizon cutoffs. -/
theorem original_source_time_horizon_estimate (u s amp : ℂ) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ w : ℂ, B+1 ≤ w.re → ∀ T rho x k : ℝ,
      0 ≤ T → -(1/4:ℝ) ≤ rho → rho ≤ 1/4 → 0 ≤ k →
      ‖∫ p in (0:ℝ)..T, Complex.exp (-w*(p:ℂ))*(actionRemainder u s amp p rho x k-actionRemainder u s amp p 0 x k)‖ ≤
        C*Real.exp (-(N:ℝ)*k)*|rho| := by
  obtain ⟨C,B,hC,hB,h⟩ := original_source_cube_horizon_estimate u s amp N
  refine ⟨2*C,B,by positivity,hB,?_⟩
  intro w hw T rho x k hT hr0 hr1 hk
  have hp (p : ℝ) (hp : 0 ≤ p) :
      ‖Complex.exp (-w*(p:ℂ))*actionVariation u s amp p rho x k‖ ≤
        (2*C*Real.exp (-(N:ℝ)*k)*|rho|)*Real.exp (-p) := by
    have ha : ‖actionVariation u s amp p rho x k‖ ≤ 2*C*Real.exp (B*p-(N:ℝ)*k)*|rho| := by
      apply (norm_sub_le _ _).trans
      have hf := (h false p rho x k hp hr0 hr1 hk).2
      have hi := (h true p rho x k hp hr0 hr1 hk).2
      linarith
    rw [norm_mul,Complex.norm_exp]
    calc
      _ ≤ Real.exp ((-w*(p:ℂ)).re)*(2*C*Real.exp (B*p-(N:ℝ)*k)*|rho|) :=
        mul_le_mul_of_nonneg_left ha (Real.exp_nonneg _)
      _ = (2*C*|rho|)*Real.exp ((B-w.re)*p-(N:ℝ)*k) := by
        simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
        rw [show Real.exp (-w.re*p)*(2*C*Real.exp (B*p-(N:ℝ)*k)*|rho|)=
          (2*C*|rho|)*(Real.exp (-w.re*p)*Real.exp (B*p-(N:ℝ)*k)) by ring,← Real.exp_add]
        congr 2
        ring
      _ ≤ (2*C*|rho|)*Real.exp (-p-(N:ℝ)*k) := by gcongr; nlinarith
      _ = _ := by rw [show -p-(N:ℝ)*k=-(N:ℝ)*k+(-p) by ring,Real.exp_add]; ring
  have hi : IntervalIntegrable (fun p : ℝ =>
      (2*C*Real.exp (-(N:ℝ)*k)*|rho|)*Real.exp (-p)) MeasureTheory.volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have heq : (∫ p in (0:ℝ)..T, Complex.exp (-w*(p:ℂ))*(actionRemainder u s amp p rho x k-actionRemainder u s amp p 0 x k))=
      ∫ p in (0:ℝ)..T, Complex.exp (-w*(p:ℂ))*actionVariation u s amp p rho x k := by
    apply intervalIntegral.integral_congr
    intro p hp'
    have hp0 : 0 ≤ p := by rw [uIcc_of_le hT] at hp'; exact hp'.1
    dsimp only
    rw [actionVariation_eq_sub u s amp p rho x k hp0 hr0 hr1]
  rw [heq]
  have hb := intervalIntegral.norm_integral_le_of_norm_le hT
    (Filter.Eventually.of_forall (fun p hp' => hp p hp'.1.le)) hi
  calc
    _ ≤ ∫ p in (0:ℝ)..T, (2*C*Real.exp (-(N:ℝ)*k)*|rho|)*Real.exp (-p) := hb
    _ = (2*C*Real.exp (-(N:ℝ)*k)*|rho|)*(1-Real.exp (-T)) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg,integral_exp,neg_zero,Real.exp_zero]
    _ ≤ _ := by nlinarith [Real.exp_nonneg (-T),mul_nonneg (by positivity : 0 ≤ 2*C*Real.exp (-(N:ℝ)*k)*|rho|) (Real.exp_nonneg (-T))]

private def Xshift (z : Site) (r : ℝ) : ℝ :=
  Real.exp z.k*offset (unitRadius z.image z.p r z.alpha z.beta) z.theta

private theorem offset_bounds (d theta : ℝ) (hd : 0 ≤ d) :
    |offset d theta| ≤ Real.exp d ∧ |offsetRadial d theta| ≤ Real.exp d := by
  have hD := denominator_pos d theta
  have hS : |Real.sin theta| ≤ denominator d theta := by
    have hid : (denominator d theta)^(2 : ℕ)-(radialNumerator d theta)^(2 : ℕ)=(Real.sin theta)^(2 : ℕ) := by
      calc
        _ = (Real.cosh d^(2 : ℕ)-Real.sinh d^(2 : ℕ))*(1-Real.cos theta^(2 : ℕ)) := by unfold denominator radialNumerator; ring
        _ = _ := by rw [Real.cosh_sq_sub_sinh_sq]; nlinarith [Real.sin_sq_add_cos_sq theta]
    nlinarith [sq_nonneg (radialNumerator d theta),sq_abs (Real.sin theta)]
  have hs := Real.sinh_nonneg_iff.mpr hd
  constructor
  · rw [offset,abs_div,abs_mul,abs_of_nonneg hs,abs_of_pos hD]
    calc
      _ ≤ Real.sinh d*denominator d theta/denominator d theta := by gcongr
      _ = Real.sinh d := mul_div_cancel_right₀ _ hD.ne'
      _ ≤ Real.exp d := by rw [← Real.cosh_add_sinh]; linarith [Real.cosh_pos d]
  · rw [offsetRadial,abs_div,abs_of_pos (sq_pos_of_pos hD)]
    calc
      _ ≤ denominator d theta/(denominator d theta)^(2 : ℕ) := div_le_div_of_nonneg_right hS (sq_nonneg _)
      _ = height d theta := by unfold height; field_simp
      _ ≤ _ := (height_bounds d theta hd).2.1

private theorem offset_E : E (fun z r => (Xshift z r:ℂ)) (4*Real.exp 6) 2 1 := by
  intro z r hr
  have he : 4*Real.exp (z.k+2*z.p+6)=4*Real.exp 6*Real.exp (2*z.p+1*z.k) := by
    rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have hv (r : ℝ) (hr : r ∈ window) :
      |Xshift z r| ≤ Real.exp (z.k+2*z.p+6) ∧
      DifferentiableAt ℝ (Xshift z) r ∧ |deriv (Xshift z) r| ≤ 4*Real.exp (z.k+2*z.p+6) := by
    have hd := unitRadius_growth z.image z.p r z.alpha z.beta z.hp hr.1 hr.2 z.ha.1 z.ha.2 z.hb.1 z.hb.2
    have hb := offset_bounds _ z.theta hd.1
    have hR := (unitRadius_hasDerivAt z.image z.p r z.alpha z.beta z.hp hr.1 hr.2 z.ha.2 z.hb.1 z.hb.2).differentiableAt.hasDerivAt
    have hX := (((offset_radial_derivatives _ z.theta).1.comp r hR).const_mul (Real.exp z.k))
    simp only [Function.comp_def] at hX
    have he' : Real.exp z.k*Real.exp (unitRadius z.image z.p r z.alpha z.beta) ≤ Real.exp (z.k+2*z.p+6) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [hd.2])
    refine ⟨?_,hX.differentiableAt,?_⟩
    · rw [Xshift,abs_mul,abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left hb.1 (Real.exp_nonneg _)).trans he'
    · change |deriv (fun r => Real.exp z.k*offset (unitRadius z.image z.p r z.alpha z.beta) z.theta) r| ≤ _
      rw [hX.deriv,abs_mul,abs_of_pos (Real.exp_pos _),abs_mul]
      have hV := (unitRadius_horizon_derivative_bound z.image z.p r z.alpha z.beta z.hp hr.1 hr.2 z.ha.2 z.hb.1 z.hb.2).2
      calc
        _ ≤ Real.exp z.k*(Real.exp (unitRadius z.image z.p r z.alpha z.beta)*4) := by
          gcongr
          exact hb.2
        _ = 4*(Real.exp z.k*Real.exp (unitRadius z.image z.p r z.alpha z.beta)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left he' (by norm_num)
  constructor
  · rw [Complex.norm_real,Real.norm_eq_abs]
    exact (hv r hr).1.trans (by rw [← he]; nlinarith [Real.exp_pos (z.k+2*z.p+6)])
  · have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun s hs => (hv s hs).2.1)
      (fun s hs => (show ‖deriv (Xshift z) s‖ ≤ 4*Real.exp (z.k+2*z.p+6) by simpa only [Real.norm_eq_abs] using (hv s hs).2.2))
      (convex_Icc (-(1/4:ℝ)) (1/4)) zero_window hr
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
    simpa only [Real.norm_eq_abs,sub_zero,he] using h

private theorem forcing_base_expansion (u s amp : ℂ) (j : Fin 5) (image : Bool)
    (p rho alpha beta theta x k : ℝ) :
    D4BMOriginalBaseCircleJets.baseOperator j
      (fun x k => forcingRemainder u s amp image p rho alpha beta theta x k) x k=
    (1/4:ℂ)*(p*(1-sourceLower image p rho alpha):ℝ)*
      (timeOnset (2*s) (p*alpha)*
        (coefficient s amp false (sourceZ image p rho alpha beta)*
          ((1/2:ℂ)*D4BMOriginalBaseCircleJets.baseOperator j
            (D4BMOriginalBaseCircleJets.weighted 0 0 (squareRemainder u) (unitRadius image p rho alpha beta) theta) x k)+
        coefficient s amp true (sourceZ image p rho alpha beta)*
          ((1/2:ℂ)*(D4BMOriginalBaseCircleJets.baseOperator j
            (D4BMOriginalBaseCircleJets.weighted 0 2 (gradientProductRemainder u 0 0) (unitRadius image p rho alpha beta) theta) x k+
          D4BMOriginalBaseCircleJets.baseOperator j
            (D4BMOriginalBaseCircleJets.weighted 0 2 (gradientProductRemainder u 1 1) (unitRadius image p rho alpha beta) theta) x k)))) := by
  let d := unitRadius image p rho alpha beta
  let F := D4BMOriginalBaseCircleJets.weighted 0 0 (squareRemainder u) d theta
  let G := D4BMOriginalBaseCircleJets.weighted 0 2 (gradientProductRemainder u 0 0) d theta
  let H := D4BMOriginalBaseCircleJets.weighted 0 2 (gradientProductRemainder u 1 1) d theta
  let c := (p*(1-sourceLower image p rho alpha):ℝ)*coefficient s amp false (sourceZ image p rho alpha beta)*timeOnset (2*s) (p*alpha)/8
  let e := (p*(1-sourceLower image p rho alpha):ℝ)*coefficient s amp true (sourceZ image p rho alpha beta)*timeOnset (2*s) (p*alpha)/8
  have hF : ContDiff ℝ ∞ (fun v : ℝ × ℝ => F v.1 v.2) :=
    D4BMOriginalBaseCircleJets.weighted_base_smooth 0 0 _ (squareRemainder_jet_smooth u []) d theta
  have hG : ContDiff ℝ ∞ (fun v : ℝ × ℝ => G v.1 v.2) :=
    D4BMOriginalBaseCircleJets.weighted_base_smooth 0 2 _ (gradientProductRemainder_jet_smooth u 0 0 []) d theta
  have hH : ContDiff ℝ ∞ (fun v : ℝ × ℝ => H v.1 v.2) :=
    D4BMOriginalBaseCircleJets.weighted_base_smooth 0 2 _ (gradientProductRemainder_jet_smooth u 1 1 []) d theta
  have he : (fun x k => forcingRemainder u s amp image p rho alpha beta theta x k)=
      fun x k => c*F x k+e*(G x k+H x k) := by
    funext x k
    dsimp [forcingRemainder,F,G,H,c,e,d,D4BMOriginalBaseCircleJets.weighted,D4BMOriginalBaseCircleJets.U,
      D4BMOriginalBaseCircleJets.Y,sample,logCircle,circle]
    unfold compactForcing coefficient
    simp only [Bool.false_eq_true,↓reduceIte]
    ring
  rw [he,D4BMOriginalBaseCircleJets.baseOperator_linear j F (fun x k => G x k+H x k) c e hF (hG.add hH) x k]
  have hadd := D4BMOriginalBaseCircleJets.baseOperator_linear j G H 1 1 hG hH x k
  simp only [one_mul] at hadd
  rw [hadd]
  dsimp [c,e,F,G,H,d]
  ring

private theorem Rapid.congr {f g : Site → ℝ → ℂ} (hf : Rapid f) (he : ∀ z r, f z r=g z r) : Rapid g := by
  have h : f=g := funext (fun z => funext (he z))
  rw [← h]
  exact hf

private theorem weighted_rapid (f : (Fin 2 → ℝ) → ℂ) (hf : Rapid (sourceSample f)) (a b : ℕ) :
    Rapid (fun z r => D4BMOriginalBaseCircleJets.weighted a b f
      (unitRadius z.image z.p r z.alpha z.beta) z.theta z.x z.k) := by
  have hb (b : ℕ) : Rapid (fun z r => (Y z r:ℂ)^b*sourceSample f z r) := by
    induction b with
    | zero => simpa only [pow_zero,one_mul] using hf
    | succ b ih =>
      have h := ih.mul (D := 4*Real.exp 6) (A := 2) 1 (by positivity) (by norm_num)
        (by simpa only [Nat.cast_one] using height_E)
      apply h.congr
      intro z r
      rw [pow_succ]
      ring
  have hab (a : ℕ) : Rapid (fun z r => (Xshift z r:ℂ)^a*((Y z r:ℂ)^b*sourceSample f z r)) := by
    induction a with
    | zero => simpa only [pow_zero,one_mul] using hb b
    | succ a ih =>
      have h := ih.mul (D := 4*Real.exp 6) (A := 2) 1 (by positivity) (by norm_num)
        (by simpa only [Nat.cast_one] using offset_E)
      apply h.congr
      intro z r
      rw [pow_succ]
      ring
  apply (hab a).congr
  intro z r
  dsimp [D4BMOriginalBaseCircleJets.weighted,D4BMOriginalBaseCircleJets.U,D4BMOriginalBaseCircleJets.Y,
    Xshift,Y,sourceSample,sample]
  ring

private theorem weighted_operator_rapid (f : (Fin 2 → ℝ) → ℂ)
    (hf : ContDiffOn ℝ ∞ f D4BMAngularSeries.domain)
    (hjet : ∀ word : List (Fin 2), Rapid (sourceSample (coordinateJet word f)))
    (a b : ℕ) (j : Fin 5) :
    Rapid (fun z r => D4BMOriginalBaseCircleJets.baseOperator j
      (D4BMOriginalBaseCircleJets.weighted a b f (unitRadius z.image z.p r z.alpha z.beta) z.theta) z.x z.k) := by
  let W (a b : ℕ) (word : List (Fin 2)) (z : Site) (r : ℝ) :=
    D4BMOriginalBaseCircleJets.weighted a b (coordinateJet word f)
      (unitRadius z.image z.p r z.alpha z.beta) z.theta z.x z.k
  have hw (a b : ℕ) (word : List (Fin 2)) : Rapid (W a b word) := weighted_rapid _ (hjet word) a b
  fin_cases j
  · exact hw a b []
  · have h := (((hw a b []).scale ((a:ℂ)+(b:ℂ))).add (hw (a+1) b [0])).add (hw a (b+1) [1])
    apply h.congr
    intro z r
    exact (D4BMOriginalBaseCircleJets.weighted_height a b f hf _ z.theta z.x z.k).deriv.symm
  · apply (hw a b [0,0]).congr
    intro z r
    exact (D4BMOriginalBaseCircleJets.weighted_horizontal_second a b f hf _ z.theta z.x z.k).symm
  · have h := ((((((hw a b []).scale (((a:ℂ)+(b:ℂ))^(2 : ℕ))).add
        (((hw (a+1) b [0]).add (hw a (b+1) [1])).scale (2*((a:ℂ)+(b:ℂ))+1))).add
        (hw (a+2) b [0,0])).add (hw (a+1) (b+1) [1,0])).add
        (hw (a+1) (b+1) [0,1])).add (hw a (b+2) [1,1])
    apply h.congr
    intro z r
    exact (D4BMOriginalBaseCircleJets.weighted_height_second a b f hf _ z.theta z.x z.k).symm

  · apply (hw a b [0]).congr
    intro z r
    exact (D4BMOriginalBaseCircleJets.weighted_horizontal a b f hf _ z.theta z.x z.k).deriv.symm

private theorem forcing_base_rapid (u s amp : ℂ) (j : Fin 5) :
    Rapid (fun z r => D4BMOriginalBaseCircleJets.baseOperator j
      (fun x k => forcingRemainder u s amp z.image z.p r z.alpha z.beta z.theta x k) z.x z.k) := by
  obtain ⟨C,hC,hJ⟩ := compact_coefficient_E _ (coefficient_smooth s amp false)
  obtain ⟨D,hD,hK⟩ := compact_coefficient_E _ (coefficient_smooth s amp true)
  have hsquare := (weighted_operator_rapid _ (squareRemainder_jet_smooth u []) (square_rapid u) 0 0 j).scale (1/2)
  have hgrad := ((weighted_operator_rapid _ (gradientProductRemainder_jet_smooth u 0 0 []) (gradient_rapid u 0 0) 0 2 j).add
    (weighted_operator_rapid _ (gradientProductRemainder_jet_smooth u 1 1 []) (gradient_rapid u 1 1) 0 2 j)).scale (1/2)
  have hsum := (hsquare.mul 0 hC le_rfl (by simpa only [Nat.cast_zero] using hJ)).add
    (hgrad.mul 0 hD le_rfl (by simpa only [Nat.cast_zero] using hK))
  have honset := hsum.mul (D := 1) (A := 2*‖s‖) 0 zero_le_one (by positivity) (by simpa only [Nat.cast_zero] using onset_E s)
  have hjac := honset.mul (D := 2) (A := 1) 0 (by norm_num) zero_le_one (by simpa only [Nat.cast_zero] using jacobian_E)
  have hfinal := hjac.scale (1/4)
  apply hfinal.congr
  intro z r
  simpa only [coordinateJet,mul_assoc] using (forcing_base_expansion u s amp j z.image z.p r z.alpha z.beta z.theta z.x z.k).symm

/-- All actual angular base jets required by the complete metric current have
uniform horizon Taylor bounds, with arbitrary independent cusp decay. -/
theorem original_forcing_base_jet_horizon_estimate (u s amp : ℂ) (j : Fin 5) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ image : Bool, ∀ p rho alpha beta theta x k : ℝ,
      0 ≤ p → -(1/4:ℝ) ≤ rho → rho ≤ 1/4 → 0 ≤ alpha → alpha ≤ 1 →
      0 ≤ beta → beta ≤ 1 → 0 ≤ k →
      let F := fun rho => D4BMOriginalBaseCircleJets.baseOperator j
        (fun x k => forcingRemainder u s amp image p rho alpha beta theta x k) x k
      ‖F rho‖ ≤ C*Real.exp (B*p-(N:ℝ)*k) ∧
      ‖F rho-F 0‖ ≤ C*Real.exp (B*p-(N:ℝ)*k)*|rho| := by
  obtain ⟨C,B,hC,hB,h⟩ := forcing_base_rapid u s amp j N
  refine ⟨C,B,hC,hB,?_⟩
  intro image p rho alpha beta theta x k hp hr0 hr1 ha0 ha1 hb0 hb1 hk
  simpa only [E,neg_mul,sub_eq_add_neg] using
    h ⟨image,p,alpha,beta,theta,x,k,hp,⟨ha0,ha1⟩,⟨hb0,hb1⟩,hk⟩ rho ⟨hr0,hr1⟩

end
end RHTower.D4BMOriginalHorizonForcingBound

namespace RHTower.D4BMOriginalHorizonForcingBound
open D4BMOriginalBaseCircleJets
open D4BMNativeCircle D4BMSquareCuspJets D4BMGlobalAngularResponse
open D4BMOriginalHorizonRadiusDerivative D4BMOriginalHorizonSourceJets
open D4BMRetardedHorizonGeometry D4BMNativeSourceJetGrowth D4BMLaplaceRadial D4BMJointSource
noncomputable section
set_option autoImplicit false

private def clip (t : ℝ) : ℝ := max 0 (min 1 t)
private theorem clip_mem (t : ℝ) : clip t ∈ Icc (0:ℝ) 1 := by
  unfold clip
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)
private theorem clip_eq (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) : clip t=t := by
  simp only [clip,min_eq_right ht.2,max_eq_right ht.1]
private theorem clip_continuous : Continuous clip := by unfold clip; fun_prop

private theorem forcing_base_smooth (u s amp : ℂ) (image : Bool) (p rho a b theta : ℝ) :
    ContDiff ℝ ∞ (fun v : ℝ × ℝ => forcingRemainder u s amp image p rho a b theta v.1 v.2) := by
  have he (x k : ℝ) := forcing_base_expansion u s amp 0 image p rho a b theta x k
  change ∀ x k : ℝ, forcingRemainder u s amp image p rho a b theta x k=_ at he
  simp_rw [he]
  have hS := weighted_base_smooth 0 0 _ (squareRemainder_jet_smooth u []) (unitRadius image p rho a b) theta
  have hG0 := weighted_base_smooth 0 2 _ (gradientProductRemainder_jet_smooth u 0 0 []) (unitRadius image p rho a b) theta
  have hG1 := weighted_base_smooth 0 2 _ (gradientProductRemainder_jet_smooth u 1 1 []) (unitRadius image p rho a b) theta
  exact contDiff_const.mul (contDiff_const.mul
    ((contDiff_const.mul (contDiff_const.mul hS)).add (contDiff_const.mul (contDiff_const.mul (hG0.add hG1)))))

private theorem forcing_clipped_joint_continuous (u s amp : ℂ) (image : Bool) (p rho : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (j : Fin 5) :
    Continuous (fun v : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => baseOperator j
      (fun x k => forcingRemainder u s amp image p rho (clip v.2.1) (clip v.2.2.1) (2*Real.pi*v.2.2.2) x k)
      v.1.1 v.1.2) := by
  have ha : Continuous (fun v : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => clip v.2.1) := clip_continuous.comp (by fun_prop)
  have hb : Continuous (fun v : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => clip v.2.2.1) := clip_continuous.comp (by fun_prop)
  have hZ : Continuous (fun v : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => sourceZ image p rho (clip v.2.1) (clip v.2.2.1)) := by
    cases image <;> dsimp [sourceZ,sourceLower] <;> fun_prop
  have hL : Continuous (fun v : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => sourceLower image p rho (clip v.2.1)) := by
    cases image <;> dsimp [sourceLower] <;> fun_prop
  have hQ : Continuous (fun v : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => expc (p*(1-clip v.2.1))) :=
    expc_smooth.continuous.comp (continuous_const.mul (continuous_const.sub ha))
  apply continuous_iff_continuousAt.mpr
  intro v
  have hz : 0 < 1+sourceZ image p rho (clip v.2.1) (clip v.2.2.1) :=
    sourceZ_add_one_pos image hp (by linarith) (clip_mem _).2 (clip_mem _).1 (clip_mem _).2
  have hF : ContinuousAt (fun t : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => horizonFactor image p rho (clip t.2.1) (clip t.2.2.1)) v := by
    unfold horizonFactor
    apply ContinuousAt.div
    · fun_prop
    · exact continuousAt_const.mul (continuousAt_const.add hZ.continuousAt)
    · exact mul_ne_zero (by linarith) hz.ne'
  have hR : ContinuousAt (fun t : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => unitRadius image p rho (clip t.2.1) (clip t.2.2.1)) v := by
    unfold unitRadius
    fun_prop
  have hC : ContinuousAt (fun t : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      (![unitRadius image p rho (clip t.2.1) (clip t.2.2.1),2*Real.pi*t.2.2.2,t.1.1,t.1.2] : Fin 4 → ℝ)) v := by
    apply continuousAt_pi.mpr
    intro i
    fin_cases i
    · exact hR
    · dsimp; fun_prop
    · dsimp; fun_prop
    · dsimp; fun_prop
  have hW (a b : ℕ) (f : (Fin 2 → ℝ) → ℂ) (hf : ContDiffOn ℝ ∞ f D4BMAngularSeries.domain) :=
    (weighted_operator_smooth a b f hf j).continuous.continuousAt.comp hC
  have hcoef (b : Bool) : ContinuousAt (fun t : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      coefficient s amp b (sourceZ image p rho (clip t.2.1) (clip t.2.2.1))) v :=
    ((coefficient_smooth s amp b).contDiffAt (isOpen_Ioi.mem_nhds
      (by change -1 < sourceZ image p rho (clip v.2.1) (clip v.2.2.1); linarith))).continuousAt.comp hZ.continuousAt
  have hJac : ContinuousAt (fun t : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      ((p*(1-sourceLower image p rho (clip t.2.1)):ℝ):ℂ)) v :=
    Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.mul (continuousAt_const.sub hL.continuousAt))
  have hT : ContinuousAt (fun t : (ℝ × ℝ) × (ℝ × ℝ × ℝ) => timeOnset (2*s) (p*clip t.2.1)) v := by
    unfold timeOnset
    fun_prop
  simp_rw [forcing_base_expansion]
  exact (continuousAt_const.mul hJac).mul (hT.mul
    (((hcoef false).mul (continuousAt_const.mul (hW 0 0 _ (squareRemainder_jet_smooth u [])))).add
      ((hcoef true).mul (continuousAt_const.mul
        ((hW 0 2 _ (gradientProductRemainder_jet_smooth u 0 0 [])).add
          (hW 0 2 _ (gradientProductRemainder_jet_smooth u 1 1 [])))))))

end
end RHTower.D4BMOriginalHorizonForcingBound

namespace RHTower.D4BMOriginalHorizonForcingBound
open D4BMOriginalBaseCircleJets
noncomputable section
set_option autoImplicit false

/-- Derivative interchange for the unchanged original causal-source remainder,
including first and second log-height and horizontal base derivatives. -/
theorem original_source_cube_base_jet (u s amp : ℂ) (image : Bool) (p rho x k : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (j : Fin 5) :
    baseOperator j (triangleRemainder u s amp image p rho) x k=
      ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        baseOperator j (fun x k => forcingRemainder u s amp image p rho a b (2*Real.pi*t) x k) x k := by
  let f (x k a b t : ℝ) := forcingRemainder u s amp image p rho (clip a) (clip b) (2*Real.pi*t) x k
  have hS (a b t : ℝ) : ContDiff ℝ ∞ (fun v : ℝ × ℝ => f v.1 v.2 a b t) :=
    forcing_base_smooth u s amp image p rho (clip a) (clip b) (2*Real.pi*t)
  have hC (j : Fin 5) := forcing_clipped_joint_continuous u s amp image p rho hp hr0 j
  have he (j : Fin 5) (x k : ℝ) :
      (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, baseOperator j (fun x k => f x k a b t) x k)=
      ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        baseOperator j (fun x k => forcingRemainder u s amp image p rho a b (2*Real.pi*t) x k) x k := by
    apply intervalIntegral.integral_congr
    intro a ha
    apply intervalIntegral.integral_congr
    intro b hb
    simp only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ha hb
    dsimp only [f]
    rw [clip_eq a ha,clip_eq b hb]
  have hv : (fun x k => ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1, f x k a b t)=
      triangleRemainder u s amp image p rho := by
    funext x k
    exact he 0 x k
  rw [← hv,cube_baseOperator f hS hC j x k]
  exact he j x k

end
end RHTower.D4BMOriginalHorizonForcingBound

namespace RHTower.D4BMOriginalHorizonForcingBound
open D4BMOriginalBaseCircleJets
noncomputable section
set_option autoImplicit false

private theorem forcing_base_cube_continuous (u s amp : ℂ) (image : Bool) (p rho x k : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (j : Fin 5) :
    ContinuousOn (fun v : ℝ × ℝ × ℝ => baseOperator j
      (fun x k => forcingRemainder u s amp image p rho v.1 v.2.1 (2*Real.pi*v.2.2) x k) x k) Cube := by
  have hc := (forcing_clipped_joint_continuous u s amp image p rho hp hr0 j).comp
    (show Continuous (fun v : ℝ × ℝ × ℝ => ((x,k),v)) by fun_prop)
  apply hc.continuousOn.congr
  intro v hv
  dsimp only [Function.comp_def]
  rw [clip_eq _ hv.1,clip_eq _ hv.2.1]

/-- The original direct-minus-image action has the same actual base jets as the
integrated difference of its original forcing jets. -/
theorem original_action_base_jet (u s amp : ℂ) (p rho x k : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4) (j : Fin 5) :
    baseOperator j (actionRemainder u s amp p rho) x k=
      ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        (baseOperator j (fun x k => forcingRemainder u s amp false p rho a b (2*Real.pi*t) x k) x k-
        baseOperator j (fun x k => forcingRemainder u s amp true p rho a b (2*Real.pi*t) x k) x k) := by
  let f (image : Bool) (x k a b t : ℝ) := forcingRemainder u s amp image p rho (clip a) (clip b) (2*Real.pi*t) x k
  have hS (image : Bool) (a b t : ℝ) : ContDiff ℝ ∞ (fun v : ℝ × ℝ => f image v.1 v.2 a b t) :=
    forcing_base_smooth u s amp image p rho (clip a) (clip b) (2*Real.pi*t)
  have hlin (j : Fin 5) (x k a b t : ℝ) :
      baseOperator j (fun x k => f false x k a b t-f true x k a b t) x k=
      baseOperator j (fun x k => f false x k a b t) x k-baseOperator j (fun x k => f true x k a b t) x k := by
    simpa only [one_mul,neg_one_mul,sub_eq_add_neg] using baseOperator_linear j
      (fun x k => f false x k a b t) (fun x k => f true x k a b t) 1 (-1) (hS false a b t) (hS true a b t) x k
  have hC (j : Fin 5) : Continuous (fun v : (ℝ × ℝ) × (ℝ × ℝ × ℝ) =>
      baseOperator j (fun x k => f false x k v.2.1 v.2.2.1 v.2.2.2-f true x k v.2.1 v.2.2.1 v.2.2.2) v.1.1 v.1.2) := by
    simp_rw [hlin]
    exact (forcing_clipped_joint_continuous u s amp false p rho hp hr0 j).sub
      (forcing_clipped_joint_continuous u s amp true p rho hp hr0 j)
  have he (j : Fin 5) (x k : ℝ) :
      (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        baseOperator j (fun x k => f false x k a b t-f true x k a b t) x k)=
      ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
        (baseOperator j (fun x k => forcingRemainder u s amp false p rho a b (2*Real.pi*t) x k) x k-
        baseOperator j (fun x k => forcingRemainder u s amp true p rho a b (2*Real.pi*t) x k) x k) := by
    simp_rw [hlin]
    apply intervalIntegral.integral_congr
    intro a ha
    apply intervalIntegral.integral_congr
    intro b hb
    simp only [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ha hb
    dsimp only [f]
    rw [clip_eq a ha,clip_eq b hb]
  have hv : (fun x k => ∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
      (f false x k a b t-f true x k a b t))=actionRemainder u s amp p rho := by
    funext x k
    rw [show (∫ a in (0:ℝ)..1, ∫ b in (0:ℝ)..1, ∫ t in (0:ℝ)..1,
      (f false x k a b t-f true x k a b t))=_ from he 0 x k]
    dsimp only [baseOperator,Matrix.cons_val_zero]
    exact cube_sub_integral
      (fun v : ℝ × ℝ × ℝ => forcingRemainder u s amp false p rho v.1 v.2.1 (2*Real.pi*v.2.2) x k)
      (fun v : ℝ × ℝ × ℝ => forcingRemainder u s amp true p rho v.1 v.2.1 (2*Real.pi*v.2.2) x k)
      (forcing_cube_continuous u s amp false p rho x k hp hr0 hr1)
      (forcing_cube_continuous u s amp true p rho x k hp hr0 hr1)
  rw [← hv,cube_baseOperator (fun x k a b t => f false x k a b t-f true x k a b t)
    (fun a b t => (hS false a b t).sub (hS true a b t)) hC j x k]
  exact he j x k

/-- The original action's actual base derivatives have uniform horizon Taylor
bounds with independent arbitrary cusp decay. -/
theorem original_action_base_jet_horizon_estimate (u s amp : ℂ) (j : Fin 5) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ p rho x k : ℝ,
      0 ≤ p → -(1/4:ℝ) ≤ rho → rho ≤ 1/4 → 0 ≤ k →
      ‖baseOperator j (actionRemainder u s amp p rho) x k‖ ≤ C*Real.exp (B*p-(N:ℝ)*k) ∧
      ‖baseOperator j (actionRemainder u s amp p rho) x k-
        baseOperator j (actionRemainder u s amp p 0) x k‖ ≤ C*Real.exp (B*p-(N:ℝ)*k)*|rho| := by
  obtain ⟨C,B,hC,hB,h⟩ := original_forcing_base_jet_horizon_estimate u s amp j N
  refine ⟨2*C,B,by positivity,hB,?_⟩
  intro p rho x k hp hr0 hr1 hk
  let F (r : ℝ) (v : ℝ × ℝ × ℝ) :=
    baseOperator j (fun x k => forcingRemainder u s amp false p r v.1 v.2.1 (2*Real.pi*v.2.2) x k) x k-
    baseOperator j (fun x k => forcingRemainder u s amp true p r v.1 v.2.1 (2*Real.pi*v.2.2) x k) x k
  have hF (r : ℝ) (hr : -(1/4:ℝ) ≤ r) : ContinuousOn (F r) Cube :=
    (forcing_base_cube_continuous u s amp false p r x k hp hr j).sub
      (forcing_base_cube_continuous u s amp true p r x k hp hr j)
  rw [original_action_base_jet u s amp p rho x k hp hr0 hr1 j,
    original_action_base_jet u s amp p 0 x k hp (by norm_num) (by norm_num) j]
  constructor
  · apply cube_norm_bound
    intro a ha b hb t ht
    have hd := (h false p rho a b (2*Real.pi*t) x k hp hr0 hr1 ha.1 ha.2 hb.1 hb.2 hk).1
    have hi := (h true p rho a b (2*Real.pi*t) x k hp hr0 hr1 ha.1 ha.2 hb.1 hb.2 hk).1
    exact (norm_sub_le _ _).trans (by linarith)
  · rw [← cube_sub_integral (F rho) (F 0) (hF rho hr0) (hF 0 (by norm_num))]
    apply cube_norm_bound
    intro a ha b hb t ht
    dsimp [F]
    rw [show ∀ A B C D : ℂ, (A-B)-(C-D)=(A-C)-(B-D) by intros; ring]
    have hd := (h false p rho a b (2*Real.pi*t) x k hp hr0 hr1 ha.1 ha.2 hb.1 hb.2 hk).2
    have hi := (h true p rho a b (2*Real.pi*t) x k hp hr0 hr1 ha.1 ha.2 hb.1 hb.2 hk).2
    exact (norm_sub_le _ _).trans (by linarith)

end
end RHTower.D4BMOriginalHorizonForcingBound

namespace RHTower.D4BMOriginalHorizonForcingBound
open D4BMOriginalBaseCircleJets
noncomputable section
set_option autoImplicit false

/-- Uniform time/horizon/cusp comparison for actual base derivatives of the complete
original direct-minus-image source action. -/
theorem original_action_base_jet_time_horizon_estimate (u s amp : ℂ) (j : Fin 5) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ w : ℂ, B+1 ≤ w.re → ∀ T rho x k : ℝ,
      0 ≤ T → -(1/4:ℝ) ≤ rho → rho ≤ 1/4 → 0 ≤ k →
      ‖∫ p in (0:ℝ)..T, Complex.exp (-w*(p:ℂ))*(baseOperator j (actionRemainder u s amp p rho) x k-baseOperator j (actionRemainder u s amp p 0) x k)‖ ≤
        C*Real.exp (-(N:ℝ)*k)*|rho| := by
  obtain ⟨C,B,hC,hB,h⟩ := original_action_base_jet_horizon_estimate u s amp j N
  refine ⟨C,B,hC,hB,?_⟩
  intro w hw T rho x k hT hr0 hr1 hk
  have hp (p : ℝ) (hp : 0 ≤ p) :
      ‖Complex.exp (-w*(p:ℂ))*(baseOperator j (actionRemainder u s amp p rho) x k-baseOperator j (actionRemainder u s amp p 0) x k)‖ ≤
        (C*Real.exp (-(N:ℝ)*k)*|rho|)*Real.exp (-p) := by
    have ha := (h p rho x k hp hr0 hr1 hk).2
    rw [norm_mul,Complex.norm_exp]
    calc
      _ ≤ Real.exp ((-w*(p:ℂ)).re)*(C*Real.exp (B*p-(N:ℝ)*k)*|rho|) :=
        mul_le_mul_of_nonneg_left ha (Real.exp_nonneg _)
      _ = (C*|rho|)*Real.exp ((B-w.re)*p-(N:ℝ)*k) := by
        simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
        rw [show Real.exp (-w.re*p)*(C*Real.exp (B*p-(N:ℝ)*k)*|rho|)=
          (C*|rho|)*(Real.exp (-w.re*p)*Real.exp (B*p-(N:ℝ)*k)) by ring,← Real.exp_add]
        congr 2
        ring
      _ ≤ (C*|rho|)*Real.exp (-p-(N:ℝ)*k) := by gcongr; nlinarith
      _ = _ := by rw [show -p-(N:ℝ)*k=-(N:ℝ)*k+(-p) by ring,Real.exp_add]; ring
  have hi : IntervalIntegrable (fun p : ℝ =>
      (C*Real.exp (-(N:ℝ)*k)*|rho|)*Real.exp (-p)) MeasureTheory.volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hb := intervalIntegral.norm_integral_le_of_norm_le hT
    (Filter.Eventually.of_forall (fun p hp' => hp p hp'.1.le)) hi
  calc
    _ ≤ ∫ p in (0:ℝ)..T, (C*Real.exp (-(N:ℝ)*k)*|rho|)*Real.exp (-p) := hb
    _ = (C*Real.exp (-(N:ℝ)*k)*|rho|)*(1-Real.exp (-T)) := by
      rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_comp_neg,integral_exp,neg_zero,Real.exp_zero]
    _ ≤ _ := by nlinarith [Real.exp_nonneg (-T),mul_nonneg (by positivity : 0 ≤ C*Real.exp (-(N:ℝ)*k)*|rho|) (Real.exp_nonneg (-T))]

end
end RHTower.D4BMOriginalHorizonForcingBound
