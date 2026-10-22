import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMNativeSourceJetGrowth
import Mathlib.Analysis.Calculus.MeanValue

/-! Uniform horizon Taylor estimates for actual source jets on both complete original
source triangles. The moving source coordinate is retained in the radius derivative. -/
open Set
namespace RHTower.D4BMOriginalHorizonRadiusDerivative
open D4BMRetardedHorizonGeometry
noncomputable section
set_option autoImplicit false

def sourceZSlope (image : Bool) (p alpha beta : ℝ) : ℝ :=
  if image then 0 else (1-beta)*Real.exp (-(p*(1-alpha)))

def factorLogRate (image : Bool) (p rho alpha beta : ℝ) : ℝ :=
  Real.exp (-(p*(1-alpha)))/(1-rho*Real.exp (-(p*(1-alpha))))+
    1/(1+rho)+sourceZSlope image p alpha beta/(1+sourceZ image p rho alpha beta)

def unitRadius (image : Bool) (p rho alpha beta : ℝ) : ℝ :=
  2*Real.arsinh (Real.sqrt ((1-alpha)*beta)*Real.sqrt (horizonFactor image p rho alpha beta))

theorem unitRadius_eq_original (image : Bool) {p rho alpha beta : ℝ}
    (hp : 0 < p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4)
    (ha : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    unitRadius image p rho alpha beta =
      Real.arcosh (max 1 (compactInvariant image (Real.exp (p*(1-alpha))) rho
        (sourceZ image p rho alpha beta))) :=
  (compact_radius image hp (by linarith) (by linarith) ha hb0 hb1).symm

private theorem sourceZ_derivative (image : Bool) (p rho alpha beta : ℝ) :
    HasDerivAt (fun r => sourceZ image p r alpha beta) (sourceZSlope image p alpha beta) rho := by
  cases image
  · have h := (hasDerivAt_id rho).mul_const (Real.exp (-(p*(1-alpha))))
    apply (h.add ((h.const_sub 1).mul_const beta)).congr_deriv
    dsimp [sourceZSlope]
    ring
  · simpa only [sourceZ,sourceLower,sourceZSlope,if_true,one_mul] using
      (hasDerivAt_const rho (Real.exp (-(p*(1-alpha)))+(1-Real.exp (-(p*(1-alpha))))*beta))

private theorem chart_bounds (image : Bool) (p rho alpha beta : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4)
    (ha : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    let e := Real.exp (-(p*(1-alpha)))
    0 ≤ e ∧ e ≤ 1 ∧ (3/4:ℝ) ≤ 1-rho*e ∧ (3/4:ℝ) ≤ 1+rho ∧
      (3/4:ℝ) ≤ 1+sourceZ image p rho alpha beta ∧
      0 ≤ sourceZSlope image p alpha beta ∧ sourceZSlope image p alpha beta ≤ 1 := by
  let e := Real.exp (-(p*(1-alpha)))
  have he0 : 0 ≤ e := Real.exp_nonneg _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have hre : -(1/4:ℝ) ≤ rho*e ∧ rho*e ≤ 1/4 := by
    constructor <;> nlinarith [mul_nonneg (by linarith : 0 ≤ rho+1/4) he0,
      mul_nonneg (by linarith : 0 ≤ 1/4-rho) he0]
  let L := sourceLower image p rho alpha
  have hL : -(1/4:ℝ) ≤ L := by
    cases image
    · exact hre.1
    · change -(1/4:ℝ) ≤ 1*e
      simpa only [one_mul] using (show -(1/4:ℝ) ≤ e by linarith)
  have hZ : (3/4:ℝ) ≤ 1+sourceZ image p rho alpha beta := by
    change (3/4:ℝ) ≤ 1+(L+(1-L)*beta)
    nlinarith [mul_nonneg (sub_nonneg.mpr hb1) (by linarith : 0 ≤ L+1/4)]
  refine ⟨he0,he1,by linarith [hre.2],by linarith,hZ,?_⟩
  cases image
  · change 0 ≤ (1-beta)*e ∧ (1-beta)*e ≤ 1
    constructor
    · positivity
    · nlinarith [mul_nonneg hb0 he0]
  · simp [sourceZSlope]

/-- Relative source-factor speed is uniformly nonnegative and bounded on both triangles. -/
theorem factorLogRate_bounds (image : Bool) (p rho alpha beta : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4)
    (ha : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    0 ≤ factorLogRate image p rho alpha beta ∧ factorLogRate image p rho alpha beta ≤ 4 := by
  obtain ⟨he0,he1,hN,hR,hZ,hS0,hS1⟩ := chart_bounds image p rho alpha beta hp hr0 hr1 ha hb0 hb1
  have hN0 : 0 < 1-rho*Real.exp (-(p*(1-alpha))) := by linarith
  have hR0 : 0 < 1+rho := by linarith
  have hZ0 : 0 < 1+sourceZ image p rho alpha beta := by linarith
  have h1 : Real.exp (-(p*(1-alpha)))/(1-rho*Real.exp (-(p*(1-alpha)))) ≤ (4/3:ℝ) :=
    (div_le_iff₀ hN0).mpr (by linarith)
  have h2 : 1/(1+rho) ≤ (4/3:ℝ) := (div_le_iff₀ hR0).mpr (by linarith)
  have h3 : sourceZSlope image p alpha beta/(1+sourceZ image p rho alpha beta) ≤ (4/3:ℝ) :=
    (div_le_iff₀ hZ0).mpr (by linarith)
  unfold factorLogRate
  constructor
  · exact add_nonneg (add_nonneg (div_nonneg he0 hN0.le) (one_div_nonneg.mpr hR0.le))
      (div_nonneg hS0 hZ0.le)
  · linarith

/-- Exact source-factor derivative, including the moving direct source endpoint. -/
theorem horizonFactor_hasDerivAt (image : Bool) (p rho alpha beta : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4)
    (ha : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    HasDerivAt (fun r => horizonFactor image p r alpha beta)
      (-horizonFactor image p rho alpha beta*factorLogRate image p rho alpha beta) rho := by
  obtain ⟨_,_,hN,hR,hZ,_,_⟩ := chart_bounds image p rho alpha beta hp hr0 hr1 ha hb0 hb1
  have hN0 : 1-rho*Real.exp (-(p*(1-alpha))) ≠ 0 := by linarith
  have hR0 : 1+rho ≠ 0 := by linarith
  have hZ0 : 1+sourceZ image p rho alpha beta ≠ 0 := by linarith
  have hn := (((hasDerivAt_id rho).mul_const (Real.exp (-(p*(1-alpha))))).const_sub 1).const_mul
    (p*expc (p*(1-alpha)))
  have hd := ((hasDerivAt_id rho).const_add 1).mul ((sourceZ_derivative image p rho alpha beta).const_add 1)
  apply (hn.div hd (mul_ne_zero hR0 hZ0)).congr_deriv
  simp only [Pi.mul_apply,id_eq]
  dsimp only [horizonFactor,factorLogRate]
  generalize he : Real.exp (-(p*(1-alpha))) = e at hN0 ⊢
  generalize hz : sourceZ image p rho alpha beta = z at hZ0 ⊢
  generalize ha : p*expc (p*(1-alpha)) = A
  generalize hc : sourceZSlope image p alpha beta = c
  have hN1 : 1-e*rho ≠ 0 := by simpa only [mul_comm] using hN0
  field_simp [hN0,hN1,hR0,hZ0]
  ring

/-- The actual radius differentiates smoothly through both collapsed-circle edges. -/
theorem unitRadius_hasDerivAt (image : Bool) (p rho alpha beta : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4)
    (ha : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    let t := Real.sqrt ((1-alpha)*beta)*Real.sqrt (horizonFactor image p rho alpha beta)
    HasDerivAt (fun r => unitRadius image p r alpha beta)
      (-t/Real.sqrt (1+t^(2 : ℕ))*factorLogRate image p rho alpha beta) rho := by
  rcases hp.eq_or_lt with h | hp
  · subst p
    simpa [unitRadius,horizonFactor] using (hasDerivAt_const rho (0:ℝ))
  · have hF := horizonFactor_pos image (p:=p) (rho:=rho) (alpha:=alpha) (beta:=beta)
      hp (by linarith) (by linarith) ha hb0 hb1
    have hs : Real.sqrt (horizonFactor image p rho alpha beta) ≠ 0 := (Real.sqrt_pos.mpr hF).ne'
    have h := (((horizonFactor_hasDerivAt image p rho alpha beta hp.le hr0 hr1 ha hb0 hb1).sqrt hF.ne').const_mul
      (Real.sqrt ((1-alpha)*beta))).arsinh.const_mul 2
    apply h.congr_deriv
    simp only [smul_eq_mul]
    have he := Real.sq_sqrt hF.le
    field_simp [hs]
    rw [he]

/-- Increasing the horizon coordinate contracts every original source radius,
at a speed at most four, independently of source time and both source coordinates. -/
theorem unitRadius_horizon_derivative_bound (image : Bool) (p rho alpha beta : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4)
    (ha : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    deriv (fun r => unitRadius image p r alpha beta) rho ≤ 0 ∧
      |deriv (fun r => unitRadius image p r alpha beta) rho| ≤ 4 := by
  rw [(unitRadius_hasDerivAt image p rho alpha beta hp hr0 hr1 ha hb0 hb1).deriv]
  let t := Real.sqrt ((1-alpha)*beta)*Real.sqrt (horizonFactor image p rho alpha beta)
  have ht : 0 ≤ t := by positivity
  have hs : 0 < Real.sqrt (1+t^(2 : ℕ)) := Real.sqrt_pos.mpr (by positivity)
  have hts : t ≤ Real.sqrt (1+t^(2 : ℕ)) := by nlinarith [Real.sq_sqrt (show 0 ≤ 1+t^(2 : ℕ) by positivity)]
  have hq0 : 0 ≤ t/Real.sqrt (1+t^(2 : ℕ)) := div_nonneg ht hs.le
  have hq1 : t/Real.sqrt (1+t^(2 : ℕ)) ≤ 1 := (div_le_one hs).mpr hts
  have hL := factorLogRate_bounds image p rho alpha beta hp hr0 hr1 ha hb0 hb1
  change -t/Real.sqrt (1+t^(2 : ℕ))*factorLogRate image p rho alpha beta ≤ 0 ∧
    |-t/Real.sqrt (1+t^(2 : ℕ))*factorLogRate image p rho alpha beta| ≤ 4
  rw [neg_div,neg_mul,abs_neg,abs_of_nonneg (mul_nonneg hq0 hL.1)]
  constructor
  · exact neg_nonpos.mpr (mul_nonneg hq0 hL.1)
  · exact (mul_le_mul_of_nonneg_right hq1 hL.1).trans (by simpa using hL.2)

/-- The original source-square radius grows at most linearly with the unchanged source time. -/
theorem unitRadius_growth (image : Bool) (p rho alpha beta : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4)
    (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    0 ≤ unitRadius image p rho alpha beta ∧ unitRadius image p rho alpha beta ≤ 2*p+6 := by
  let F := horizonFactor image p rho alpha beta
  let A := Real.sqrt ((1-alpha)*beta)
  let t := A*Real.sqrt F
  have hc0 : 0 ≤ (1-alpha)*beta := mul_nonneg (sub_nonneg.mpr ha1) hb0
  have hc1 : (1-alpha)*beta ≤ 1 := by nlinarith [mul_nonneg ha0 hb0]
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hA1 : A ≤ 1 := by nlinarith [Real.sq_sqrt hc0]
  have hF := D4BMNativeSourceJetGrowth.horizonFactor_uniform_bounds image p rho alpha beta
    hp hr0 hr1 ha0 ha1 hb0 hb1
  have he : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hFhi : F ≤ 4*(Real.exp p)^(2 : ℕ) := by
    have hm := mul_le_mul_of_nonneg_right he (Real.exp_nonneg p)
    dsimp [F]
    nlinarith [hF.2]
  have hFlo : 0 ≤ F := (by positivity : 0 ≤ 3*p/10).trans hF.1
  have hroot : Real.sqrt F ≤ 2*Real.exp p := by
    nlinarith [Real.sq_sqrt hFlo,Real.sqrt_nonneg F,Real.exp_pos p]
  have ht0 : 0 ≤ t := mul_nonneg hA0 (Real.sqrt_nonneg F)
  have ht : t ≤ 2*Real.exp p :=
    (mul_le_mul_of_nonneg_right hA1 (Real.sqrt_nonneg F)).trans (by simpa using hroot)
  have hS : Real.sqrt (1+t^(2 : ℕ)) ≤ 1+t := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1+t^(2 : ℕ) by positivity),Real.sqrt_nonneg (1+t^(2 : ℕ))]
  have he1 : 1 ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  have he3 : (5:ℝ) ≤ Real.exp 3 := by
    have h1 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have h3 := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) h1 3
    have hE : Real.exp (3:ℝ)=(Real.exp 1)^(3 : ℕ) := by simp [← Real.exp_nat_mul]
    rw [hE]
    norm_num at h3
    linarith
  have hb : Real.arsinh t ≤ p+3 := by
    rw [← Real.exp_le_exp,Real.exp_arsinh,Real.exp_add]
    have hh := mul_le_mul_of_nonneg_left he3 (Real.exp_nonneg p)
    nlinarith
  change 0 ≤ 2*Real.arsinh t ∧ 2*Real.arsinh t ≤ 2*p+6
  exact ⟨mul_nonneg (by norm_num) (Real.arsinh_nonneg_iff.mpr ht0),by linarith⟩


end
end RHTower.D4BMOriginalHorizonRadiusDerivative


open Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMOriginalHorizonSourceJets
open D4BMNativeCircle D4BMSquareCuspJets D4BMGlobalAngularResponse D4BMAngularSeries
open D4BMOriginalHorizonRadiusDerivative D4BMRetardedHorizonGeometry D4BMNativeSourceJetGrowth
open GaloisForLFunctions.HTGeometry.ScalarTwoJet
noncomputable section
set_option autoImplicit false

private abbrev P := Fin 2 → ℝ

/-- A genuine angular source jet on the original compact source-square circle. -/
def sample (f : P → ℂ) (image : Bool) (p rho alpha beta theta x k : ℝ) : ℂ :=
  f (logCircle (unitRadius image p rho alpha beta) theta x k)

theorem sample_eq_original (f : P → ℂ) (image : Bool) {p rho alpha beta : ℝ}
    (hp : 0 < p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4)
    (ha : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) (theta x k : ℝ) :
    sample f image p rho alpha beta theta x k =
      f (logCircle (Real.arcosh (max 1 (compactInvariant image (Real.exp (p*(1-alpha))) rho
        (sourceZ image p rho alpha beta)))) theta x k) := by
  rw [sample,unitRadius_eq_original image hp hr0 hr1 ha hb0 hb1]

private theorem radial_coefficients (d theta : ℝ) (hd : 0 ≤ d) :
    |offsetRadial d theta| ≤ Real.exp d ∧ |heightRadial d theta| ≤ Real.exp d := by
  have hD := denominator_pos d theta
  have hid : (denominator d theta)^(2 : ℕ)-(radialNumerator d theta)^(2 : ℕ)=(Real.sin theta)^(2 : ℕ) := by
    calc
      _ = (Real.cosh d^(2 : ℕ)-Real.sinh d^(2 : ℕ))*(1-Real.cos theta^(2 : ℕ)) := by
        unfold denominator radialNumerator
        ring
      _ = _ := by rw [Real.cosh_sq_sub_sinh_sq]; nlinarith [Real.sin_sq_add_cos_sq theta]
  have hS : |Real.sin theta| ≤ denominator d theta := by
    nlinarith [sq_nonneg (radialNumerator d theta),sq_abs (Real.sin theta)]
  have hN : |radialNumerator d theta| ≤ denominator d theta := by
    nlinarith [sq_nonneg (Real.sin theta),sq_abs (radialNumerator d theta)]
  have hlo : Real.exp (-d) ≤ denominator d theta := by
    rw [← Real.cosh_sub_sinh]
    unfold denominator
    nlinarith [Real.sinh_nonneg_iff.mpr hd,Real.cos_le_one theta]
  have hh : 1/denominator d theta ≤ Real.exp d := by
    calc
      _ ≤ 1/Real.exp (-d) := one_div_le_one_div_of_le (Real.exp_pos _) hlo
      _ = _ := by rw [Real.exp_neg]; field_simp
  have bound (a : ℝ) (ha : |a| ≤ denominator d theta) : |a/(denominator d theta)^(2 : ℕ)| ≤ Real.exp d := by
    rw [abs_div,abs_of_pos (sq_pos_of_pos hD)]
    calc
      _ ≤ denominator d theta/(denominator d theta)^(2 : ℕ) := div_le_div_of_nonneg_right ha (sq_nonneg _)
      _ = 1/denominator d theta := by field_simp
      _ ≤ _ := hh
  exact ⟨bound _ hS,bound _ (by simpa only [abs_neg] using hN)⟩

private def radialJet (f : P → ℂ) (d theta x k : ℝ) : ℂ :=
  (Real.exp k*offsetRadial d theta:ℝ)*coordDeriv 0 f (logCircle d theta x k)+
    (Real.exp k*heightRadial d theta:ℝ)*coordDeriv 1 f (logCircle d theta x k)

private theorem radial_hasDerivAt (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain)
    (d theta x k : ℝ) : HasDerivAt (fun r => f (logCircle r theta x k)) (radialJet f d theta x k) d := by
  have hz : 0 < logCircle d theta x k 1 :=
    mul_pos (Real.exp_pos _) (one_div_pos.mpr (denominator_pos _ _))
  have hF := (hf.contDiffAt ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz)).differentiableAt
    (by simp)
  have hC : HasDerivAt (fun r => logCircle r theta x k) (radialVelocity d theta k) d := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact ((offset_radial_derivatives d theta).1.const_mul (Real.exp k)).const_add x
    · exact (height_radial_derivatives d theta).1.const_mul (Real.exp k)
  apply (hF.hasFDerivAt.comp_hasDerivAt d hC).congr_deriv
  change (fderiv ℝ f (logCircle d theta x k)) (radialVelocity d theta k)=_
  rw [pi_eq_sum_univ' (radialVelocity d theta k),map_sum]
  simp [Fin.sum_univ_two,radialVelocity,radialJet,coordDeriv,Complex.real_smul]

private theorem radial_bound (f : P → ℂ) (N : ℕ)
    (h0 : ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ d theta x k : ℝ, 0 ≤ d → 0 ≤ k →
      Real.exp k*‖coordDeriv 0 f (logCircle d theta x k)‖ ≤ C*Real.exp (B*d-(N:ℝ)*k))
    (h1 : ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ d theta x k : ℝ, 0 ≤ d → 0 ≤ k →
      Real.exp k*‖coordDeriv 1 f (logCircle d theta x k)‖ ≤ C*Real.exp (B*d-(N:ℝ)*k)) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ d theta x k : ℝ, 0 ≤ d → 0 ≤ k →
      ‖radialJet f d theta x k‖ ≤ C*Real.exp (B*d-(N:ℝ)*k) := by
  obtain ⟨C,B,hC,hB,h0⟩ := h0
  obtain ⟨D,A,hD,hA,h1⟩ := h1
  refine ⟨C+D,B+A+1,add_nonneg hC hD,by positivity,?_⟩
  intro d theta x k hd hk
  have hc := radial_coefficients d theta hd
  have hn : ‖radialJet f d theta x k‖ ≤
      Real.exp d*(Real.exp k*‖coordDeriv 0 f (logCircle d theta x k)‖+
        Real.exp k*‖coordDeriv 1 f (logCircle d theta x k)‖) := by
    unfold radialJet
    apply (norm_add_le _ _).trans
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos k)]
    calc
      _ ≤ (Real.exp k*Real.exp d)*‖coordDeriv 0 f (logCircle d theta x k)‖+
        (Real.exp k*Real.exp d)*‖coordDeriv 1 f (logCircle d theta x k)‖ := by
          gcongr
          · exact hc.1
          · exact hc.2
      _ = _ := by ring
  calc
    _ ≤ Real.exp d*(C*Real.exp (B*d-(N:ℝ)*k)+D*Real.exp (A*d-(N:ℝ)*k)) :=
      hn.trans (mul_le_mul_of_nonneg_left (add_le_add (h0 d theta x k hd hk) (h1 d theta x k hd hk)) (Real.exp_nonneg _))
    _ ≤ Real.exp d*((C+D)*Real.exp ((B+A)*d-(N:ℝ)*k)) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      rw [add_mul]
      gcongr <;> nlinarith
    _ = _ := by rw [mul_left_comm,← Real.exp_add]; congr 2; ring

private theorem sample_hasDerivAt (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain)
    (image : Bool) (p rho alpha beta theta x k : ℝ)
    (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4)
    (ha : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) :
    HasDerivAt (fun r => sample f image p r alpha beta theta x k)
      (deriv (fun r => unitRadius image p r alpha beta) rho •
        radialJet f (unitRadius image p rho alpha beta) theta x k) rho := by
  have hR := (unitRadius_hasDerivAt image p rho alpha beta hp hr0 hr1 ha hb0 hb1).differentiableAt.hasDerivAt
  exact (radial_hasDerivAt f hf _ theta x k).scomp rho hR

private theorem horizon_bound (f : P → ℂ) (hf : ContDiffOn ℝ ∞ f domain) (N : ℕ)
    (hR : ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ d theta x k : ℝ, 0 ≤ d → 0 ≤ k →
      ‖radialJet f d theta x k‖ ≤ C*Real.exp (B*d-(N:ℝ)*k)) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ image : Bool, ∀ p rho alpha beta theta x k : ℝ,
      0 ≤ p → -(1/4:ℝ) ≤ rho → rho ≤ 1/4 → 0 ≤ alpha → alpha ≤ 1 →
      0 ≤ beta → beta ≤ 1 → 0 ≤ k →
      ‖deriv (fun r => sample f image p r alpha beta theta x k) rho‖ ≤ C*Real.exp (B*p-(N:ℝ)*k) ∧
      ‖sample f image p rho alpha beta theta x k-sample f image p 0 alpha beta theta x k‖ ≤
        C*Real.exp (B*p-(N:ℝ)*k)*|rho| := by
  obtain ⟨C,B,hC,hB,hR⟩ := hR
  let D := 4*C*Real.exp (6*B)
  have hb (image : Bool) (p rho alpha beta theta x k : ℝ)
      (hp : 0 ≤ p) (hr0 : -(1/4:ℝ) ≤ rho) (hr1 : rho ≤ 1/4)
      (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hb0 : 0 ≤ beta) (hb1 : beta ≤ 1) (hk : 0 ≤ k) :
      ‖deriv (fun r => sample f image p r alpha beta theta x k) rho‖ ≤ D*Real.exp ((2*B)*p-(N:ℝ)*k) := by
    rw [(sample_hasDerivAt f hf image p rho alpha beta theta x k hp hr0 hr1 ha1 hb0 hb1).deriv,norm_smul,Real.norm_eq_abs]
    have hd := unitRadius_growth image p rho alpha beta hp hr0 hr1 ha0 ha1 hb0 hb1
    have hv := (unitRadius_horizon_derivative_bound image p rho alpha beta hp hr0 hr1 ha1 hb0 hb1).2
    calc
      _ ≤ 4*(C*Real.exp (B*unitRadius image p rho alpha beta-(N:ℝ)*k)) :=
        mul_le_mul hv (hR _ theta x k hd.1 hk) (norm_nonneg _) (by norm_num)
      _ ≤ 4*(C*Real.exp (B*(2*p+6)-(N:ℝ)*k)) := by gcongr; exact hd.2
      _ = _ := by
        dsimp [D]
        rw [show B*(2*p+6)-(N:ℝ)*k=6*B+((2*B)*p-(N:ℝ)*k) by ring,Real.exp_add]
        ring
  refine ⟨D,2*B,by dsimp [D]; positivity,by positivity,?_⟩
  intro image p rho alpha beta theta x k hp hr0 hr1 ha0 ha1 hb0 hb1 hk
  refine ⟨hb image p rho alpha beta theta x k hp hr0 hr1 ha0 ha1 hb0 hb1 hk,?_⟩
  have hd (r : ℝ) (hr : r ∈ Icc (-(1/4:ℝ)) (1/4)) :
      DifferentiableAt ℝ (fun r => sample f image p r alpha beta theta x k) r :=
    (sample_hasDerivAt f hf image p r alpha beta theta x k hp hr.1 hr.2 ha1 hb0 hb1).differentiableAt
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hd
    (fun r hr => hb image p r alpha beta theta x k hp hr.1 hr.2 ha0 ha1 hb0 hb1 hk)
    (convex_Icc (-(1/4:ℝ)) (1/4)) (show (0:ℝ) ∈ Icc (-(1/4:ℝ)) (1/4) by norm_num) ⟨hr0,hr1⟩
  simpa only [sub_zero,Real.norm_eq_abs] using h

/-- All actual square-source jets have uniform horizon derivative and first-order
Taylor bounds, with arbitrary base cusp decay and exponential source-time allowance. -/
theorem square_jet_horizon_estimate (u : ℂ) (word : List (Fin 2)) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ image : Bool, ∀ p rho alpha beta theta x k : ℝ,
      0 ≤ p → -(1/4:ℝ) ≤ rho → rho ≤ 1/4 → 0 ≤ alpha → alpha ≤ 1 →
      0 ≤ beta → beta ≤ 1 → 0 ≤ k →
      ‖deriv (fun r => sample (coordinateJet word (squareRemainder u)) image p r alpha beta theta x k) rho‖ ≤
        C*Real.exp (B*p-(N:ℝ)*k) ∧
      ‖sample (coordinateJet word (squareRemainder u)) image p rho alpha beta theta x k-
        sample (coordinateJet word (squareRemainder u)) image p 0 alpha beta theta x k‖ ≤
        C*Real.exp (B*p-(N:ℝ)*k)*|rho| := by
  apply horizon_bound _ (squareRemainder_jet_smooth u word) N
  apply radial_bound _ N
  · simpa only [coordinateJet,Nat.cast_one,one_mul] using squareRemainder_circle_jet_bound u (0::word) N 1
  · simpa only [coordinateJet,Nat.cast_one,one_mul] using squareRemainder_circle_jet_bound u (1::word) N 1

/-- The full gradient-product source has the same independent horizon/cusp Taylor estimate. -/
theorem gradient_jet_horizon_estimate (u : ℂ) (i j : Fin 2) (word : List (Fin 2)) (N : ℕ) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ ∀ image : Bool, ∀ p rho alpha beta theta x k : ℝ,
      0 ≤ p → -(1/4:ℝ) ≤ rho → rho ≤ 1/4 → 0 ≤ alpha → alpha ≤ 1 →
      0 ≤ beta → beta ≤ 1 → 0 ≤ k →
      ‖deriv (fun r => sample (coordinateJet word (gradientProductRemainder u i j)) image p r alpha beta theta x k) rho‖ ≤
        C*Real.exp (B*p-(N:ℝ)*k) ∧
      ‖sample (coordinateJet word (gradientProductRemainder u i j)) image p rho alpha beta theta x k-
        sample (coordinateJet word (gradientProductRemainder u i j)) image p 0 alpha beta theta x k‖ ≤
        C*Real.exp (B*p-(N:ℝ)*k)*|rho| := by
  apply horizon_bound _ (gradientProductRemainder_jet_smooth u i j word) N
  apply radial_bound _ N
  · simpa only [coordinateJet,Nat.cast_one,one_mul] using gradientProductRemainder_circle_jet_bound u i j (0::word) N 1
  · simpa only [coordinateJet,Nat.cast_one,one_mul] using gradientProductRemainder_circle_jet_bound u i j (1::word) N 1

end
end RHTower.D4BMOriginalHorizonSourceJets
