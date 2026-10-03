import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicSignedVariation
import GaloisForLFunctions.RHTower.ChebyshevThetaPowerLog
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Complete signed Gaussian prime cubic rows

The actual physical cubic cancels after completing the middle prime coordinate
and summing row norms over every full-band pair with
`m^2 / 10000000 < |p-r| ≤ m^3`, at the existing exponential conductors.
The normalized total tends to zero. Exact logarithmic unweighting, the source
quantitative theta estimate and two signed integrations supply uniform prime
Fourier control. The moving saddle window, excluded contraction and both
physical kernel remainders are retained in the transport to actual rows.

Both Jordan parts of this same family diverge after the identical normalization.
Global prime mass and finite cell deletion supply actual pairs; the complete
physical two-sign sector construction supplies the corresponding q-variation.

This leaf addresses the indicated annulus; `ChiPrimeGaussianCubicNearCancellation`
subsequently removes its lower gap cutoff. The full signed cubic remains open.
Neither result asserts a Gaussian moment law, a BAG self-return certificate or RH.
-/

noncomputable section
open Complex MeasureTheory Set Filter Finset
open scoped Topology
namespace RHTower
open GaloisForLFunctions.RHTower

private theorem row_profile_smooth : ContDiffOn ℝ 2 primeGaussianProfile (Ioi (0:ℝ)) :=
  ((Complex.ofRealCLM.contDiff.comp bagPhysicalHeightWindow.contDiff).contDiffOn).mul
    contDiffOn_smoothAFECutoff_pos

private theorem row_profile_jet :
    (∀ x ∈ Icc (1:ℝ) 2, HasDerivAt primeGaussianProfile (deriv primeGaussianProfile x) x) ∧
    (∀ x ∈ Icc (1:ℝ) 2, HasDerivAt (deriv primeGaussianProfile) (deriv (deriv primeGaussianProfile) x) x) ∧
    ContinuousOn primeGaussianProfile (Icc (1:ℝ) 2) ∧
    ContinuousOn (deriv primeGaussianProfile) (Icc (1:ℝ) 2) ∧
    ContinuousOn (deriv (deriv primeGaussianProfile)) (Icc (1:ℝ) 2) := by
  have hs : Icc (1:ℝ) 2 ⊆ Ioi (0:ℝ) := fun x hx => lt_of_lt_of_le (by norm_num) hx.1
  have hd : ContDiffOn ℝ 1 (deriv primeGaussianProfile) (Ioi (0:ℝ)) :=
    row_profile_smooth.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdd : ContDiffOn ℝ 0 (deriv (deriv primeGaussianProfile)) (Ioi (0:ℝ)) :=
    hd.deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact ⟨fun x hx => (row_profile_smooth.differentiableOn (by norm_num)).hasDerivAt (Ioi_mem_nhds (hs hx)),
    fun x hx => (hd.differentiableOn (by norm_num)).hasDerivAt (Ioi_mem_nhds (hs hx)),
    row_profile_smooth.continuousOn.mono hs,hd.continuousOn.mono hs,hdd.continuousOn.mono hs⟩

private theorem row_profile_boundary {x : ℝ} (hx : x=1 ∨ x=2) :
    primeGaussianProfile x=0 ∧ deriv primeGaussianProfile x=0 := by
  have hx0 : 0<x := by rcases hx with rfl|rfl <;> norm_num
  have hw : bagPhysicalHeightWindow x=0 :=
    bagPhysicalHeightWindow.zero_of_le_dist (by
      change (1/2:ℝ) ≤ dist x (3/2)
      rcases hx with rfl|rfl <;> norm_num [Real.dist_eq])
  have hmin : IsLocalMin (fun y : ℝ => bagPhysicalHeightWindow y) x :=
    Filter.Eventually.of_forall (fun y => by change bagPhysicalHeightWindow x ≤ bagPhysicalHeightWindow y; rw [hw]; exact bagPhysicalHeightWindow.nonneg)
  have hw' : deriv (fun y : ℝ => bagPhysicalHeightWindow y) x=0 := hmin.deriv_eq_zero
  constructor
  · simp [primeGaussianProfile,hw]
  · have hdw := ((bagPhysicalHeightWindow.contDiff (n:=1)).differentiable (by norm_num) x).hasDerivAt
    have hdv := (contDiffOn_smoothAFECutoff_pos.differentiableOn (by norm_num)).hasDerivAt (Ioi_mem_nhds hx0)
    have hh := hdw.ofReal_comp.mul hdv
    change HasDerivAt primeGaussianProfile _ x at hh
    rw [hw,hw'] at hh
    simpa only [Complex.ofReal_zero,zero_mul,mul_zero,add_zero] using hh.deriv

private theorem row_fourier_twice
    (f f' f'' : ℝ → ℂ) {B τ : ℝ} (hτ : τ≠0)
    (hf : ∀ x ∈ Icc (1:ℝ) 2, HasDerivAt f (f' x) x)
    (hf' : ∀ x ∈ Icc (1:ℝ) 2, HasDerivAt f' (f'' x) x)
    (hc : ContinuousOn f' (Icc (1:ℝ) 2))
    (hc' : ContinuousOn f'' (Icc (1:ℝ) 2))
    (hf1 : f 1=0) (hf2 : f 2=0) (hf'1 : f' 1=0) (hf'2 : f' 2=0)
    (hB : ∀ x ∈ Icc (1:ℝ) 2, ‖f'' x‖≤B) :
    ‖∫ x in (1:ℝ)..2, f x * bourgainOscillation (τ*x)‖ ≤ B/τ^2 := by
  let a : ℂ := (τ:ℂ)*I
  let e : ℝ → ℂ := fun x => bourgainOscillation (τ*x)
  have ha : a≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hτ) I_ne_zero
  have he (x:ℝ) : HasDerivAt e (a*e x) x := by
    have h := (((Complex.ofRealCLM.hasDerivAt (x:=x)).const_mul (τ:ℂ)).mul_const I).cexp
    simpa only [e,a,bourgainOscillation,Complex.ofReal_mul,Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one,mul_assoc,mul_comm,mul_left_comm] using h
  have hec : Continuous e := by
    exact continuous_iff_continuousAt.mpr (fun x => (he x).continuousAt)
  have hei : IntervalIntegrable (fun x => a*e x) volume 1 2 :=
    (continuous_const.mul hec).intervalIntegrable _ _
  have hfi : IntervalIntegrable f' volume 1 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr hc.integrableOn_Icc
  have hfii : IntervalIntegrable f'' volume 1 2 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr hc'.integrableOn_Icc
  have h1 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => hf x (by simpa only [uIcc_of_le (by norm_num : (1:ℝ)≤2)] using hx))
    (fun x _ => he x) hfi hei
  have h2 := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun x hx => hf' x (by simpa only [uIcc_of_le (by norm_num : (1:ℝ)≤2)] using hx))
    (fun x _ => he x) hfii hei
  simp only [hf1,hf2,hf'1,hf'2,zero_mul,sub_self,zero_sub] at h1 h2
  have factor (g:ℝ→ℂ) : (∫ x in (1:ℝ)..2, g x*(a*e x)) =
      a*(∫ x in (1:ℝ)..2,g x*e x) := by
    simp_rw [show ∀ x, g x*(a*e x)=a*(g x*e x) by intro x;ring]
    exact intervalIntegral.integral_const_mul _ _
  rw [factor] at h1 h2
  have hidentity : a^2*(∫ x in (1:ℝ)..2,f x*e x) = ∫ x in (1:ℝ)..2,f'' x*e x := by
    linear_combination a*h1-h2
  have hn : ‖∫ x in (1:ℝ)..2,f'' x*e x‖≤B := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (C:=B) (fun x hx => show ‖f'' x*e x‖≤B from by
        rw [norm_mul,show ‖e x‖=1 from norm_bourgainOscillation _ ,mul_one]
        exact hB x (by simpa only [uIcc_of_le (by norm_num : (1:ℝ)≤2)] using
          (show x ∈ uIcc (1:ℝ) 2 from uIoc_subset_uIcc hx)))
    norm_num at hb ⊢
    exact hb
  have han : ‖a‖^2=τ^2 := by simp [a,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [← hidentity,norm_mul,norm_pow,han] at hn
  exact (le_div_iff₀ (sq_pos_of_ne_zero hτ)).mpr (by simpa [mul_comm] using hn)

private def rowInvDenom (l x : ℝ) : ℂ := (1+(l:ℂ)*(Real.log x:ℂ))⁻¹
private def rowLogProfile (l x : ℝ) : ℂ := primeGaussianProfile x * rowInvDenom l x
private def rowLogProfileD (l x : ℝ) : ℂ :=
  deriv primeGaussianProfile x * rowInvDenom l x -
    primeGaussianProfile x*(l:ℂ)*(x:ℂ)⁻¹*rowInvDenom l x^2
private def rowLogProfileDD (l x : ℝ) : ℂ :=
  deriv (deriv primeGaussianProfile) x * rowInvDenom l x -
    2*deriv primeGaussianProfile x*(l:ℂ)*(x:ℂ)⁻¹*rowInvDenom l x^2 +
    primeGaussianProfile x*(l:ℂ)*((x:ℂ)⁻¹)^2*rowInvDenom l x^2 +
    2*primeGaussianProfile x*(l:ℂ)^2*((x:ℂ)⁻¹)^2*rowInvDenom l x^3

private theorem row_denom_pos {l x:ℝ} (hl:0≤l) (hx:1≤x) : 1≤1+l*Real.log x := by
  have := mul_nonneg hl (Real.log_nonneg hx)
  linarith

private theorem row_inv_deriv {l x:ℝ} (hl:0≤l) (hx:1≤x) :
    HasDerivAt (rowInvDenom l) (-(l:ℂ)*(x:ℂ)⁻¹*rowInvDenom l x^2) x := by
  have hx0 : 0<x := by linarith
  have hd : (1+(l:ℂ)*(Real.log x:ℂ))≠0 := by
    have : (1+l*Real.log x:ℝ)≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (row_denom_pos hl hx))
    exact_mod_cast this
  have hh := (((Real.hasDerivAt_log hx0.ne').ofReal_comp).const_mul (l:ℂ)).const_add 1
  have hi := hh.inv hd
  apply hi.congr_deriv
  simp only [rowInvDenom,Complex.ofReal_inv,div_eq_mul_inv,inv_pow]
  ring

private theorem row_log_profile_deriv {l x:ℝ} (hl:0≤l) (hx:x∈Icc (1:ℝ) 2) :
    HasDerivAt (rowLogProfile l) (rowLogProfileD l x) x := by
  have hh := (row_profile_jet.1 x hx).mul (row_inv_deriv hl hx.1)
  apply hh.congr_deriv
  dsimp only [rowLogProfileD]
  ring

private theorem row_log_profile_deriv_second {l x:ℝ} (hl:0≤l) (hx:x∈Icc (1:ℝ) 2) :
    HasDerivAt (rowLogProfileD l) (rowLogProfileDD l x) x := by
  have hx0 : 0<x := by linarith [hx.1]
  have hxc : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hi := row_inv_deriv hl hx.1
  have hf := row_profile_jet.1 x hx
  have hf' := row_profile_jet.2.1 x hx
  have hxi := (Complex.ofRealCLM.hasDerivAt (x:=x)).inv hxc
  have hh := (hf'.mul hi).sub ((((hf.mul_const (l:ℂ)).mul hxi).mul (hi.pow 2)))
  apply hh.congr_deriv
  dsimp [rowLogProfileDD]
  simp only [div_eq_mul_inv,inv_pow]
  ring

private theorem row_log_profile_continuous (l:ℝ) (hl:0≤l) :
    ContinuousOn (rowLogProfile l) (Icc (1:ℝ) 2) ∧
    ContinuousOn (rowLogProfileD l) (Icc (1:ℝ) 2) ∧
    ContinuousOn (rowLogProfileDD l) (Icc (1:ℝ) 2) := by
  have hi : ContinuousOn (rowInvDenom l) (Icc (1:ℝ) 2) :=
    fun x hx => (row_inv_deriv hl hx.1).continuousAt.continuousWithinAt
  have hxi : ContinuousOn (fun x:ℝ => (x:ℂ)⁻¹) (Icc (1:ℝ) 2) := by
    intro x hx
    exact (((Complex.ofRealCLM.hasDerivAt (x:=x)).inv
      (Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le (by norm_num) hx.1)))).continuousAt).continuousWithinAt
  obtain ⟨_,_,hf,hf',hf''⟩ := row_profile_jet
  refine ⟨hf.mul hi, (hf'.mul hi).sub (((hf.mul continuousOn_const).mul hxi).mul (hi.pow 2)),?_⟩
  exact (((hf''.mul hi).sub
    (((((continuousOn_const.mul hf').mul continuousOn_const).mul hxi).mul (hi.pow 2)))).add
      (((hf.mul continuousOn_const).mul (hxi.pow 2)).mul (hi.pow 2))).add
        (((((continuousOn_const.mul hf).mul continuousOn_const).mul (hxi.pow 2)).mul (hi.pow 3)))

private theorem row_inv_norm {l x:ℝ} (hl:0≤l) (hx:1≤x) : ‖rowInvDenom l x‖≤1 := by
  have hd := row_denom_pos hl hx
  rw [rowInvDenom,norm_inv,show (1+(l:ℂ)*(Real.log x:ℂ))=((1+l*Real.log x:ℝ):ℂ) by push_cast;rfl,
    Complex.norm_of_nonneg (by linarith : 0≤1+l*Real.log x)]
  exact inv_le_one_of_one_le₀ hd

private theorem row_log_profile_bounds :
    ∃ B:ℝ, 0<B ∧ ∀ l∈Icc (0:ℝ) 1, ∀ x∈Icc (1:ℝ) 2,
      ‖rowLogProfile l x‖≤B ∧ ‖rowLogProfileD l x‖≤2*B ∧ ‖rowLogProfileDD l x‖≤6*B := by
  obtain ⟨_,_,hf,hf',hf''⟩ := row_profile_jet
  obtain ⟨B0,hB0⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  obtain ⟨B1,hB1⟩ := isCompact_Icc.exists_bound_of_continuousOn hf'
  obtain ⟨B2,hB2⟩ := isCompact_Icc.exists_bound_of_continuousOn hf''
  let B := |B0|+|B1|+|B2|+1
  have hB : 0<B := by dsimp [B];positivity
  refine ⟨B,hB,?_⟩
  intro l hl x hx
  have h0 : ‖primeGaussianProfile x‖≤B := (hB0 x hx).trans (by dsimp [B]; nlinarith [le_abs_self B0,abs_nonneg B1,abs_nonneg B2])
  have h1 : ‖deriv primeGaussianProfile x‖≤B := (hB1 x hx).trans (by dsimp [B]; nlinarith [le_abs_self B1,abs_nonneg B0,abs_nonneg B2])
  have h2 : ‖deriv (deriv primeGaussianProfile) x‖≤B := (hB2 x hx).trans (by dsimp [B]; nlinarith [le_abs_self B2,abs_nonneg B0,abs_nonneg B1])
  have hi := row_inv_norm hl.1 hx.1
  have hlc : ‖(l:ℂ)‖≤1 := by rw [Complex.norm_of_nonneg hl.1];exact hl.2
  have hxi : ‖(x:ℂ)⁻¹‖≤1 := by
    rw [norm_inv,Complex.norm_of_nonneg (by linarith [hx.1])]
    exact inv_le_one_of_one_le₀ hx.1
  have hm0 : ‖primeGaussianProfile x*rowInvDenom l x‖≤B := by
    rw [norm_mul]; calc
      _ ≤ B*1 := mul_le_mul h0 hi (norm_nonneg _) hB.le
      _ = B := mul_one B
  have hterm (z:ℂ) (hz:‖z‖≤B) : ‖z*(l:ℂ)*(x:ℂ)⁻¹*rowInvDenom l x^2‖≤B := by
    rw [norm_mul,norm_mul,norm_mul,norm_pow]
    calc
      _ ≤ B*1*1*1^2 := by gcongr
      _ = B := by ring
  have hm1 : ‖deriv primeGaussianProfile x*rowInvDenom l x‖≤B := by
    rw [norm_mul];calc
      _ ≤ B*1 := mul_le_mul h1 hi (norm_nonneg _) hB.le
      _ = B := mul_one B
  have hm2 : ‖deriv (deriv primeGaussianProfile) x*rowInvDenom l x‖≤B := by
    rw [norm_mul];calc
      _ ≤ B*1 := mul_le_mul h2 hi (norm_nonneg _) hB.le
      _ = B := mul_one B
  refine ⟨hm0, ?_,?_⟩
  · dsimp only [rowLogProfileD]
    exact (norm_sub_le _ _).trans (by linarith [hterm _ h0])
  · dsimp only [rowLogProfileDD]
    have hb1 : ‖2*deriv primeGaussianProfile x*(l:ℂ)*(x:ℂ)⁻¹*rowInvDenom l x^2‖≤2*B := by
      rw [show 2*deriv primeGaussianProfile x*(l:ℂ)*(x:ℂ)⁻¹*rowInvDenom l x^2 =
      2*(deriv primeGaussianProfile x*(l:ℂ)*(x:ℂ)⁻¹*rowInvDenom l x^2) by ring,norm_mul]
      rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
      exact mul_le_mul_of_nonneg_left (hterm _ h1) (by norm_num)
    have hb2 : ‖primeGaussianProfile x*(l:ℂ)*((x:ℂ)⁻¹)^2*rowInvDenom l x^2‖≤B := by
      simp only [norm_mul,norm_pow]
      calc
        _ ≤ B*1*1^2*1^2 := by gcongr
        _ = B := by ring
    have hb3 : ‖2*primeGaussianProfile x*(l:ℂ)^2*((x:ℂ)⁻¹)^2*rowInvDenom l x^3‖≤2*B := by
      simp only [norm_mul,norm_pow]
      rw [show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
      calc
        _ ≤ 2*B*1^2*1^2*1^3 := by gcongr
        _ = 2*B := by ring
    exact (norm_add_le _ _).trans ((add_le_add ((norm_add_le _ _).trans
    (add_le_add ((norm_sub_le _ _).trans (add_le_add hm2 hb1)) hb2)) hb3).trans (by linarith))

private theorem row_log_profile_boundary {l x:ℝ} (hx:x=1 ∨ x=2) :
    rowLogProfile l x=0 ∧ rowLogProfileD l x=0 := by
  obtain ⟨hf,hf'⟩ := row_profile_boundary hx
  simp [rowLogProfile,rowLogProfileD,hf,hf']


/-- The actual cumulative prime logarithmic weight has every fixed log-power
error bound, uniformly beyond the base point. -/
theorem eventually_primeProfileCum_log_error (k:ℕ) :
    ∀ᶠ N:ℝ in atTop, 1<Real.log N ∧ ∀ x:ℝ, N≤x →
      ‖primeProfileCum (primeResidueLogCoefficient 1 0) x-(x:ℂ)‖≤x/(Real.log N)^k := by
  obtain ⟨c,C,X,hc,hC,hX,hθ⟩ := exists_chebyshev_theta_power_log
  have ht : Tendsto (fun N:ℝ => (Real.log N)^((1:ℝ)/10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hdec0 := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10*k:ℝ) c hc).comp ht
  have hdec : Tendsto (fun N:ℝ => C*(Real.log N)^k*
      Real.exp (-(c*(Real.log N)^((1:ℝ)/10)))) atTop (𝓝 0) := by
    have he : (fun N:ℝ => C*(Real.log N)^k*Real.exp (-(c*(Real.log N)^((1:ℝ)/10)))) =ᶠ[atTop]
        (fun N:ℝ => C*((Real.log N)^((1:ℝ)/10))^(10*k:ℝ)*Real.exp (-c*(Real.log N)^((1:ℝ)/10))) := by
      filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with N hN
      rw [← Real.rpow_mul hN.le]
      simp only [show (1:ℝ)/10*(10*k:ℝ)=(k:ℝ) by ring,Real.rpow_natCast]
      ring
    have hb : Tendsto (fun N:ℝ => C*((Real.log N)^((1:ℝ)/10))^(10*k:ℝ)*
        Real.exp (-c*(Real.log N)^((1:ℝ)/10))) atTop (𝓝 0) := by
      simpa [mul_assoc] using (tendsto_const_nhds.mul hdec0 :
      Tendsto (fun N:ℝ => C*(((Real.log N)^((1:ℝ)/10))^(10*k:ℝ)*
        Real.exp (-c*(Real.log N)^((1:ℝ)/10)))) atTop (𝓝 (C*0)))
    exact hb.congr' he.symm
  filter_upwards [hdec.eventually_le_const (by norm_num : (0:ℝ)<1),
    Real.tendsto_log_atTop.eventually_gt_atTop 1,eventually_ge_atTop X] with N hsmall hL hNX
  refine ⟨hL,?_⟩
  intro x hNx
  have hN3 : 3≤N := hX.trans hNX
  have hx3 : 3≤x := hN3.trans hNx
  have hNL : 0<Real.log N := by linarith
  have heq : primeProfileCum (primeResidueLogCoefficient 1 0) x=(Chebyshev.theta x:ℂ) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    rw [Finset.sum_filter]
    simp only [primeProfileCum,primeResidueLogCoefficient,Nat.mod_one,and_true]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> rfl
  have hmono : Real.exp (-(c*(Real.log x)^((1:ℝ)/10))) ≤
      Real.exp (-(c*(Real.log N)^((1:ℝ)/10))) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hNL.le (Real.log_le_log (by linarith) hNx) (by norm_num)) hc.le)
  rw [heq,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  have hbase := hθ x (hNX.trans hNx)
  have hcoef : C*Real.exp (-(c*(Real.log N)^((1:ℝ)/10))) ≤ 1/(Real.log N)^k := by
    apply (le_div_iff₀ (pow_pos hNL k)).mpr
    nlinarith only [hsmall]
  calc
    _ ≤ C*x*Real.exp (-(c*(Real.log x)^((1:ℝ)/10))) := hbase
    _ ≤ C*x*Real.exp (-(c*(Real.log N)^((1:ℝ)/10))) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = x*(C*Real.exp (-(c*(Real.log N)^((1:ℝ)/10)))) := by ring
    _ ≤ x*(1/(Real.log N)^k) := mul_le_mul_of_nonneg_left hcoef (by linarith)
    _ = x/(Real.log N)^k := by ring

private theorem row_profile_unweight_sum {N:ℝ} (hN:1<N) (τ:ℝ) :
    (∑ q∈Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊,
      (rowLogProfile (1/Real.log N) ((q:ℝ)/N)*bourgainOscillation (τ*((q:ℝ)/N)))*
        primeResidueLogCoefficient 1 0 q) =
    (Real.log N:ℂ)*∑ q∈primeProfileBand N,
      primeGaussianProfile ((q:ℝ)/N)*bourgainOscillation (τ*((q:ℝ)/N)) := by
  rw [Finset.mul_sum,primeProfileBand,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hp:q.Prime
  · have hqN : N<(q:ℝ) := (Nat.floor_lt (by linarith : 0≤N)).mp (Finset.mem_Ioc.mp hq).1
    have hq0 : 0<(q:ℝ) := by linarith
    have hL : Real.log N≠0 := (Real.log_pos hN).ne'
    have hqL : Real.log (q:ℝ)≠0 := (Real.log_pos (hN.trans hqN)).ne'
    have hLC : (Real.log N:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL
    have hqLC : (Real.log (q:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hqL
    simp only [primeResidueLogCoefficient,hp,Nat.mod_one,and_self,ite_true]
    dsimp only [rowLogProfile,rowInvDenom]
    rw [Real.log_div hq0.ne' (by linarith : N≠0)]
    push_cast only [Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_one]
    have hden : 1+1/(Real.log N:ℂ)*((Real.log (q:ℝ):ℂ)-(Real.log N:ℂ)) =
        (Real.log (q:ℝ):ℂ)/(Real.log N:ℂ) := by field_simp;ring
    rw [hden,inv_div]
    field_simp [hqLC]
  · simp [primeResidueLogCoefficient,hp]

private theorem row_osc_deriv (τ x:ℝ) :
    HasDerivAt (fun y => bourgainOscillation (τ*y))
      (((τ:ℂ)*I)*bourgainOscillation (τ*x)) x := by
  have h := (((Complex.ofRealCLM.hasDerivAt (x:=x)).const_mul (τ:ℂ)).mul_const I).cexp
  simpa only [bourgainOscillation,Complex.ofReal_mul,Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one,mul_assoc,mul_comm,mul_left_comm] using h

private theorem row_osc_continuous (τ:ℝ) : Continuous (fun x => bourgainOscillation (τ*x)) :=
  continuous_iff_continuousAt.mpr (fun x => (row_osc_deriv τ x).continuousAt)

/-- The literal full-band Gaussian prime profile has uniform signed Fourier control.
The logarithmic prime weight is removed exactly, and both integrations keep their endpoints. -/
theorem exists_primeGaussianProfile_fourier_bound :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ N:ℝ in atTop, ∀ τ:ℝ, τ≠0 →
      ‖∑ q∈primeProfileBand N,
        primeGaussianProfile ((q:ℝ)/N)*bourgainOscillation (τ*((q:ℝ)/N))‖ ≤
        C*N/Real.log N*(1/τ^2+(1+|τ|)/(Real.log N)^12) := by
  obtain ⟨B,hB,hbound⟩ := row_log_profile_bounds
  refine ⟨6*B,by positivity,?_⟩
  filter_upwards [eventually_primeProfileCum_log_error 12,eventually_gt_atTop (1:ℝ)] with N hN hN1
  intro τ hτ
  let l:ℝ := 1/Real.log N
  have hL : 0<Real.log N := by linarith [hN.1]
  have hl : l∈Icc (0:ℝ) 1 := ⟨by dsimp [l];positivity,by
    dsimp [l];exact (div_le_one hL).mpr hN.1.le⟩
  let f : ℝ→ℂ := fun x => rowLogProfile l x*bourgainOscillation (τ*x)
  let f' : ℝ→ℂ := fun x => rowLogProfileD l x*bourgainOscillation (τ*x)+
    rowLogProfile l x*(((τ:ℂ)*I)*bourgainOscillation (τ*x))
  have hderiv : ∀ x∈Icc (1:ℝ) 2, HasDerivAt f (f' x) x :=
    fun x hx => (row_log_profile_deriv hl.1 hx).mul (row_osc_deriv τ x)
  have hfc : ContinuousOn f' (Icc (1:ℝ) 2) :=
    ((row_log_profile_continuous l hl.1).2.1.mul (row_osc_continuous τ).continuousOn).add
      ((row_log_profile_continuous l hl.1).1.mul (continuousOn_const.mul (row_osc_continuous τ).continuousOn))
  have hbd : ∀ x∈Icc (1:ℝ) 2, ‖f' x‖≤3*B*(1+|τ|) := by
    intro x hx
    obtain ⟨hg,hg',_⟩ := hbound l hl x hx
    have hn := norm_add_le (rowLogProfileD l x*bourgainOscillation (τ*x))
      (rowLogProfile l x*(((τ:ℂ)*I)*bourgainOscillation (τ*x)))
    simp only [norm_mul,norm_bourgainOscillation,norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs] at hn
    dsimp only [f']
    exact hn.trans (by nlinarith [abs_nonneg τ,mul_le_mul_of_nonneg_right hg (abs_nonneg τ)])
  have hab := scaledAbel_profile_error (primeResidueLogCoefficient 1 0) f f' 1
    (by linarith : 0<N) (by positivity : 0≤3*B*(1+|τ|))
    (by positivity : 0≤1/(Real.log N)^12) hderiv hfc
    (by dsimp [f];rw [(row_log_profile_boundary (l:=l) (Or.inl rfl)).1,zero_mul])
    (by dsimp [f];rw [(row_log_profile_boundary (l:=l) (Or.inr rfl)).1,zero_mul]) hbd
    (fun x hx => by simpa [one_mul,one_div,mul_comm,mul_left_comm,mul_assoc,div_eq_mul_inv] using hN.2 x hx.1)
  have hfour := row_fourier_twice (rowLogProfile l) (rowLogProfileD l) (rowLogProfileDD l) hτ
    (fun x hx => row_log_profile_deriv hl.1 hx)
    (fun x hx => row_log_profile_deriv_second hl.1 hx)
    (row_log_profile_continuous l hl.1).2.1 (row_log_profile_continuous l hl.1).2.2
    (row_log_profile_boundary (l:=l) (Or.inl rfl)).1 (row_log_profile_boundary (l:=l) (Or.inr rfl)).1
    (row_log_profile_boundary (l:=l) (Or.inl rfl)).2 (row_log_profile_boundary (l:=l) (Or.inr rfl)).2
    (fun x hx => (hbound l hl x hx).2.2)
  let S := ∑ q∈primeProfileBand N, primeGaussianProfile ((q:ℝ)/N)*bourgainOscillation (τ*((q:ℝ)/N))
  have hu := row_profile_unweight_sum hN1 τ
  change _=(Real.log N:ℂ)*S at hu
  change ‖(∑ q∈Finset.Ioc ⌊N⌋₊ ⌊2*N⌋₊,
    (rowLogProfile (1/Real.log N) ((q:ℝ)/N)*bourgainOscillation (τ*((q:ℝ)/N)))*
      primeResidueLogCoefficient 1 0 q)/(N:ℂ)-1*(∫ x in (1:ℝ)..2,f x)‖≤_ at hab
  rw [hu,one_mul] at hab
  have hsum := (norm_le_norm_sub_add ((Real.log N:ℂ)*S/(N:ℂ)) (∫ x in (1:ℝ)..2,f x)).trans
    (add_le_add hab hfour)
  rw [norm_div,norm_mul,Complex.norm_of_nonneg hL.le,Complex.norm_of_nonneg (by linarith : 0≤N)] at hsum
  have hNN : N≠0 := by linarith
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hL).mpr
  have hh := (div_le_iff₀ (by linarith : 0<N)).mp hsum
  dsimp only [S] at hh
  calc
    _ = Real.log N * ‖S‖ := by ring
    _ ≤ (2*(3*B*(1+|τ|))*(1/Real.log N^12)+6*B/τ^2)*N := hh
    _ = _ := by ring

/-- Every prime in the middle coordinate is retained, except the exact contraction. -/
def primeGaussianCubicCompleteRow (N : ℝ) (p r : ℕ) : ℂ :=
  ∑ q ∈ primeProfileBand N, if q=r then 0 else
    primeGaussianCubicCoefficient N p q r * primeGaussianCubicKernel N p q r

private def cubicRowFrequency (N : ℝ) (p r : ℕ) : ℝ :=
  2*Real.pi*((p:ℝ)-r)*N/r

private def cubicRowFactor (N : ℝ) (p r : ℕ) : ℂ :=
  (2*Real.pi:ℂ)*smoothAFECutoff ((p:ℝ)/N)*
    (starRingEnd ℂ) (smoothAFECutoff ((r:ℝ)/N))/(r:ℂ)

private def cubicRowFlatEntry (N : ℝ) (p q r : ℕ) : ℂ :=
  cubicRowFactor N p r * primeGaussianProfile ((q:ℝ)/N) *
    bourgainOscillation (cubicRowFrequency N p r*((q:ℝ)/N))

private theorem cubic_row_phase {N : ℝ} (hN : N≠0) (p q : ℕ) {r : ℕ}
    (hr : (r:ℝ)≠0) :
    bourgainOscillation (2*Real.pi*((p:ℝ)*q/r)) =
      bourgainOscillation (cubicRowFrequency N p r*((q:ℝ)/N)) := by
  have he : 2*Real.pi*((p:ℝ)*q/r) =
      cubicRowFrequency N p r*((q:ℝ)/N)+2*Real.pi*q := by
    dsimp [cubicRowFrequency]
    field_simp
    ring
  rw [he]
  unfold bourgainOscillation
  rw [Complex.ofReal_add,mul_add,Complex.exp_add]
  have hi : Complex.exp (I*((2*Real.pi*q:ℝ):ℂ))=1 := by
    have heq : I*((2*Real.pi*q:ℝ):ℂ) = ((q:ℤ):ℂ)*(2*Real.pi*I) := by
      push_cast
      ring
    rw [heq]
    exact Complex.exp_int_mul_two_pi_mul_I _
  rw [hi,mul_one]

private theorem cubic_row_factor_norm {N : ℝ} (hN : 0<N) {p r : ℕ}
    (hp : p∈primeProfileBand N) (hr : r∈primeProfileBand N) :
    ‖cubicRowFactor N p r‖ ≤ 8/N := by
  obtain ⟨_,hpN,_⟩ := primeProfileBand_mem hN.le hp
  obtain ⟨_,hrN,_⟩ := primeProfileBand_mem hN.le hr
  have hr0 : (0:ℝ)<r := hN.trans hrN
  have hpn := norm_smoothAFECutoff_le_one (div_pos (hN.trans hpN) hN)
  have hrn := norm_smoothAFECutoff_le_one (div_pos hr0 hN)
  dsimp [cubicRowFactor]
  rw [norm_div,norm_mul,norm_mul,Complex.norm_conj,
    show (2*↑Real.pi:ℂ)=((2*Real.pi:ℝ):ℂ) by push_cast;rfl,
    Complex.norm_of_nonneg (by positivity : 0≤2*Real.pi),Complex.norm_natCast]
  calc
    _ ≤ (2*Real.pi)*1*1/r := by gcongr
    _ ≤ 8/N := by
      apply (div_le_div_iff₀ hr0 hN).mpr
      nlinarith [Real.pi_lt_four]

private theorem cubic_row_profile_norm {x : ℝ} (hx : 0<x) :
    ‖primeGaussianProfile x‖≤1 := by
  rw [primeGaussianProfile,norm_mul,Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg]
  exact (mul_le_mul bagPhysicalHeightWindow.le_one (norm_smoothAFECutoff_le_one hx)
    (norm_nonneg _) (by norm_num)).trans_eq (by ring)

private theorem cubic_row_window_lipschitz :
    ∃ L:ℝ, 0<L ∧ ∀ x∈Icc (0:ℝ) 4, ∀ y∈Icc (0:ℝ) 4,
      |bagPhysicalHeightWindow y-bagPhysicalHeightWindow x|≤L*|y-x| := by
  have hc : Continuous (deriv (fun x:ℝ => bagPhysicalHeightWindow x)) :=
    (bagPhysicalHeightWindow.contDiff (n:=1)).continuous_deriv_one
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B|+1,by positivity,?_⟩
  intro x hx y hy
  have hb : ∀ t∈Icc (0:ℝ) 4, ‖deriv (fun x:ℝ => bagPhysicalHeightWindow x) t‖≤|B|+1 :=
    fun t ht => (hB t ht).trans (by linarith [le_abs_self B])
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (bagPhysicalHeightWindow.contDiff (n:=1)).differentiable (by norm_num) t)
      hb (convex_Icc (0:ℝ) 4) hx hy

private theorem cubic_row_window_error {N L:ℝ} (hN : 0<N) (hL : 0≤L)
    (hLip : ∀ x∈Icc (0:ℝ) 4, ∀ y∈Icc (0:ℝ) 4,
      |bagPhysicalHeightWindow y-bagPhysicalHeightWindow x|≤L*|y-x|)
    {p q r:ℕ} (hp:p∈primeProfileBand N) (hq:q∈primeProfileBand N)
    (hr:r∈primeProfileBand N) :
    |bagPhysicalHeightWindow ((p:ℝ)*q/((r:ℝ)*N))-
      bagPhysicalHeightWindow ((q:ℝ)/N)|≤2*L*|(p:ℝ)-r|/N := by
  obtain ⟨_,hpN,hp2⟩ := primeProfileBand_mem hN.le hp
  obtain ⟨_,hqN,hq2⟩ := primeProfileBand_mem hN.le hq
  obtain ⟨_,hrN,hr2⟩ := primeProfileBand_mem hN.le hr
  have hr0 : (0:ℝ)<r := hN.trans hrN
  have hq0 : (0:ℝ)<q := hN.trans hqN
  have hx : (q:ℝ)/N ∈ Icc (0:ℝ) 4 :=
    ⟨by positivity,(div_le_iff₀ hN).mpr (by linarith)⟩
  have hy : (p:ℝ)*q/((r:ℝ)*N) ∈ Icc (0:ℝ) 4 := by
    refine ⟨by positivity,(div_le_iff₀ (mul_pos hr0 hN)).mpr ?_⟩
    have hm := mul_le_mul hp2 hq2 hq0.le (by positivity : 0≤2*N)
    nlinarith
  have he : (p:ℝ)*q/((r:ℝ)*N)-(q:ℝ)/N = ((p:ℝ)-r)*q/((r:ℝ)*N) := by
    field_simp
  have hd : |(p:ℝ)*q/((r:ℝ)*N)-(q:ℝ)/N|≤2*|(p:ℝ)-r|/N := by
    rw [he,abs_div,abs_mul,abs_of_pos hq0,abs_of_pos (mul_pos hr0 hN)]
    apply (div_le_div_iff₀ (mul_pos hr0 hN) hN).mpr
    have hh : (q:ℝ)≤2*r := by linarith
    have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg ((p:ℝ)-r))
    nlinarith [mul_le_mul_of_nonneg_right hm hN.le]
  exact (hLip _ hx _ hy).trans ((mul_le_mul_of_nonneg_left hd hL).trans_eq (by ring))

private theorem cubic_row_flat_error {N L:ℝ} (hN : 0<N) (hL : 0≤L)
    (hLip : ∀ x∈Icc (0:ℝ) 4, ∀ y∈Icc (0:ℝ) 4,
      |bagPhysicalHeightWindow y-bagPhysicalHeightWindow x|≤L*|y-x|)
    {p q r:ℕ} (hp:p∈primeProfileBand N) (hq:q∈primeProfileBand N)
    (hr:r∈primeProfileBand N) :
    ‖primeGaussianCubicMainEntry N p q r-cubicRowFlatEntry N p q r‖≤
      16*L*|(p:ℝ)-r|/N^2 := by
  have hr0 : (0:ℝ)<r := hN.trans (primeProfileBand_mem hN.le hr).2.1
  have hq0 : (0:ℝ)<q := hN.trans (primeProfileBand_mem hN.le hq).2.1
  have he : primeGaussianCubicMainEntry N p q r-cubicRowFlatEntry N p q r =
    cubicRowFactor N p r*smoothAFECutoff ((q:ℝ)/N)*
      ((bagPhysicalHeightWindow ((p:ℝ)*q/((r:ℝ)*N))-
        bagPhysicalHeightWindow ((q:ℝ)/N):ℝ):ℂ)*
      bourgainOscillation (cubicRowFrequency N p r*((q:ℝ)/N)) := by
    dsimp [primeGaussianCubicMainEntry,cubicRowFlatEntry,primeGaussianProfile]
    rw [cubic_row_phase hN.ne' p q hr0.ne']
    dsimp [cubicRowFactor]
    push_cast
    ring
  rw [he,norm_mul,norm_mul,norm_mul,norm_bourgainOscillation,mul_one,
    Complex.norm_real,Real.norm_eq_abs]
  calc
    _ ≤ (8/N)*1*(2*L*|(p:ℝ)-r|/N) := by
      exact mul_le_mul (mul_le_mul (cubic_row_factor_norm hN hp hr)
        (norm_smoothAFECutoff_le_one (div_pos hq0 hN)) (norm_nonneg _) (by positivity))
        (cubic_row_window_error hN hL hLip hp hq hr) (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem cubic_row_flat_norm {N:ℝ} (hN:0<N) {p q r:ℕ}
    (hp:p∈primeProfileBand N) (hq:q∈primeProfileBand N) (hr:r∈primeProfileBand N) :
    ‖cubicRowFlatEntry N p q r‖≤8/N := by
  dsimp [cubicRowFlatEntry]
  rw [norm_mul,norm_mul,norm_bourgainOscillation,mul_one]
  exact (mul_le_mul (cubic_row_factor_norm hN hp hr)
    (cubic_row_profile_norm (div_pos (hN.trans (primeProfileBand_mem hN.le hq).2.1) hN))
    (norm_nonneg _) (by positivity)).trans_eq (mul_one _)

private theorem cubic_row_physical_to_fourier :
    ∃ C:ℝ, 0<C ∧ ∀ N:ℝ, 1<N → ∀ p∈primeProfileBand N, ∀ r∈primeProfileBand N,
      ‖primeGaussianCubicCompleteRow N p r‖ ≤
        (8/N)*‖∑ q∈primeProfileBand N,
          primeGaussianProfile ((q:ℝ)/N)*
            bourgainOscillation (cubicRowFrequency N p r*((q:ℝ)/N))‖ +
        C*(1+|(p:ℝ)-r|)/(N*Real.log N)+8/N := by
  obtain ⟨Cp,hCp,hphysical⟩ := exists_primeGaussianCubic_entry_error
  obtain ⟨L,hL,hLip⟩ := cubic_row_window_lipschitz
  let A:ℝ := 2*Real.log 4
  have hA : 0<A := by dsimp [A];positivity
  refine ⟨(Cp+16*L)*A,by positivity,?_⟩
  intro N hN p hp r hr
  have hN0 : 0<N := by linarith
  have hlog : 0<Real.log N := Real.log_pos hN
  let d:ℝ := |(p:ℝ)-r|
  let E:ℝ := (Cp+16*L)*(1+d)/N^2
  let V:ℕ→ℂ := fun q => primeGaussianCubicCoefficient N p q r*primeGaussianCubicKernel N p q r
  let F:ℕ→ℂ := fun q => cubicRowFlatEntry N p q r
  let D:ℕ→ℂ := fun q => if q=r then 0 else V q-F q
  have hE : 0≤E := by dsimp [E,d];positivity
  have hd (q:ℕ) (hq:q∈primeProfileBand N) : ‖D q‖≤E := by
    dsimp only [D]
    split_ifs with heq
    · simpa only [norm_zero] using hE
    · have he := (norm_sub_le_norm_sub_add_norm_sub (V q)
          (primeGaussianCubicMainEntry N p q r) (F q)).trans
        (add_le_add (hphysical N hN p hp q hq r hr)
          (cubic_row_flat_error hN0 hL.le hLip hp hq hr))
      refine he.trans ?_
      dsimp only [E,d]
      rw [←add_div]
      apply div_le_div_of_nonneg_right _ (sq_nonneg N)
      nlinarith [abs_nonneg ((p:ℝ)-r)]
  have hident : primeGaussianCubicCompleteRow N p r =
      (∑ q∈primeProfileBand N,D q)+(∑ q∈primeProfileBand N,F q)-F r := by
    have hpoint (q:ℕ) : (if q=r then 0 else V q)=D q+F q-(if q=r then F r else 0) := by
      dsimp [D]
      split_ifs with h <;> simp [h]
    change (∑ q∈primeProfileBand N,if q=r then 0 else V q)=_
    simp_rw [hpoint]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq']
    simp only [hr,ite_true]
  have hD : ‖∑ q∈primeProfileBand N,D q‖≤(primeProfileBand N).card*E := by
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hd).trans_eq (by simp))
  have hcount : (primeProfileBand N).card*E≤(Cp+16*L)*A*(1+d)/(N*Real.log N) := by
    have hc := primeProfileBand_card_log_le hN
    change (primeProfileBand N).card*Real.log N≤A*N at hc
    have hm := mul_le_mul_of_nonneg_right hc
      (show 0≤(Cp+16*L)*(1+d) by dsimp [d];positivity)
    dsimp [E]
    apply (le_div_iff₀ (mul_pos hN0 hlog)).mpr
    field_simp [hN0.ne']
    nlinarith
  have hF : ‖∑ q∈primeProfileBand N,F q‖≤
      (8/N)*‖∑ q∈primeProfileBand N,primeGaussianProfile ((q:ℝ)/N)*
        bourgainOscillation (cubicRowFrequency N p r*((q:ℝ)/N))‖ := by
    simp only [F,cubicRowFlatEntry,mul_assoc,←Finset.mul_sum,norm_mul]
    exact mul_le_mul_of_nonneg_right (cubic_row_factor_norm hN0 hp hr) (norm_nonneg _)
  rw [hident]
  exact (norm_sub_le _ _).trans ((add_le_add
    ((norm_add_le _ _).trans (add_le_add (hD.trans hcount) hF))
    (cubic_row_flat_norm hN0 hp hr hr)).trans_eq (by dsimp [d];ring))

private theorem cubic_row_frequency_bounds {N:ℝ} (hN:0<N) {p r:ℕ}
    (hr:r∈primeProfileBand N) :
    |(p:ℝ)-r| ≤ |cubicRowFrequency N p r| ∧
      |cubicRowFrequency N p r| ≤8*|(p:ℝ)-r| := by
  obtain ⟨_,hrN,hr2⟩ := primeProfileBand_mem hN.le hr
  have hr0 : (0:ℝ)<r := hN.trans hrN
  have he : |cubicRowFrequency N p r|=2*Real.pi*|(p:ℝ)-r| *N/r := by
    dsimp [cubicRowFrequency]
    rw [abs_div,abs_mul,abs_mul,abs_mul,abs_of_pos Real.pi_pos,
      abs_of_pos hN,abs_of_pos hr0,abs_of_pos (by norm_num : (0:ℝ)<2)]
  rw [he]
  have hd := abs_nonneg ((p:ℝ)-r)
  constructor
  · apply (le_div_iff₀ hr0).mpr
    have h1 := mul_le_mul_of_nonneg_left hr2 hd
    have h2 := mul_le_mul_of_nonneg_right (le_of_lt Real.pi_gt_three) (mul_nonneg hd hN.le)
    nlinarith
  · apply (div_le_iff₀ hr0).mpr
    have h1 := mul_le_mul_of_nonneg_left hrN.le hd
    have h2 := mul_le_mul_of_nonneg_right (le_of_lt Real.pi_lt_four) (mul_nonneg hd hN.le)
    nlinarith

/-- Complete actual noncontracting q-rows have a uniform signed bound.
Every prime q in the original band and both physical kernel errors are accounted for. -/
theorem exists_primeGaussianCubicCompleteRow_bound :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ N:ℝ in atTop, ∀ p∈primeProfileBand N, ∀ r∈primeProfileBand N,
      p≠r → ‖primeGaussianCubicCompleteRow N p r‖ ≤
        C/Real.log N*(1/|(p:ℝ)-r|^2+(1+|(p:ℝ)-r|)/(Real.log N)^12+
          (1+|(p:ℝ)-r|)/N)+C/N := by
  obtain ⟨Cf,hCf,hfour⟩ := exists_primeGaussianProfile_fourier_bound
  obtain ⟨Cp,hCp,hrow⟩ := cubic_row_physical_to_fourier
  let C:ℝ := 64*Cf+Cp+8
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [hfour,eventually_gt_atTop (1:ℝ)] with N hf hN
  intro p hp r hr hpr
  have hN0 : 0<N := by linarith
  have hL : 0<Real.log N := Real.log_pos hN
  let d:ℝ := |(p:ℝ)-r|
  have hd : 0<d := by
    apply abs_pos.mpr
    apply sub_ne_zero.mpr
    exact_mod_cast hpr
  obtain ⟨hτl,hτu⟩ := cubic_row_frequency_bounds (p:=p) hN0 hr
  have hτ : cubicRowFrequency N p r≠0 := abs_pos.mp (hd.trans_le hτl)
  have hsquare : d^2≤(cubicRowFrequency N p r)^2 := by
    nlinarith [sq_abs (cubicRowFrequency N p r)]
  have hInv : 1/(cubicRowFrequency N p r)^2≤1/d^2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hd) hsquare
  have hterm : 1/(cubicRowFrequency N p r)^2+
      (1+|cubicRowFrequency N p r|)/(Real.log N)^12 ≤
      8*(1/d^2+(1+d)/(Real.log N)^12) := by
    have hfreq : (1+|cubicRowFrequency N p r|)/(Real.log N)^12≤
        8*(1+d)/(Real.log N)^12 :=
      div_le_div_of_nonneg_right (by change _≤8*(1+d);dsimp [d];linarith)
        (pow_nonneg hL.le 12)
    have hi0 : 0≤1/d^2 := by positivity
    rw [show 8*(1+d)/(Real.log N)^12 = 8*((1+d)/(Real.log N)^12) by ring] at hfreq
    linarith
  have hFourier : (8/N)*‖∑ q∈primeProfileBand N,primeGaussianProfile ((q:ℝ)/N)*
      bourgainOscillation (cubicRowFrequency N p r*((q:ℝ)/N))‖ ≤
      (64*Cf/Real.log N)*(1/d^2+(1+d)/(Real.log N)^12) := by
    calc
      _ ≤ (8/N)*(Cf*N/Real.log N*(1/(cubicRowFrequency N p r)^2+
        (1+|cubicRowFrequency N p r|)/(Real.log N)^12)) :=
          mul_le_mul_of_nonneg_left (hf _ hτ) (by positivity)
      _ ≤ (8/N)*(Cf*N/Real.log N*(8*(1/d^2+(1+d)/(Real.log N)^12))) := by gcongr
      _ = _ := by field_simp;ring
  have hcmp : 64*Cf/Real.log N≤C/Real.log N := by
    apply div_le_div_of_nonneg_right _ hL.le
    dsimp [C];linarith
  have hcmpP : Cp/Real.log N≤C/Real.log N := by
    apply div_le_div_of_nonneg_right _ hL.le
    dsimp [C];linarith
  have hcmp8 : 8/N≤C/N := by
    apply div_le_div_of_nonneg_right _ hN0.le
    dsimp [C];linarith
  have hterm0 : 0≤1/d^2+(1+d)/(Real.log N)^12 := by positivity
  calc
    _ ≤ (8/N)*‖∑ q∈primeProfileBand N,primeGaussianProfile ((q:ℝ)/N)*
        bourgainOscillation (cubicRowFrequency N p r*((q:ℝ)/N))‖+
        Cp*(1+d)/(N*Real.log N)+8/N := hrow N hN p hp r hr
    _ ≤ (64*Cf/Real.log N)*(1/d^2+(1+d)/(Real.log N)^12)+
        Cp*(1+d)/(N*Real.log N)+8/N := by gcongr
    _ = (64*Cf/Real.log N)*(1/d^2+(1+d)/(Real.log N)^12)+
        (Cp/Real.log N)*((1+d)/N)+8/N := by ring
    _ ≤ (C/Real.log N)*(1/d^2+(1+d)/(Real.log N)^12)+
        (C/Real.log N)*((1+d)/N)+C/N := by
          exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hcmp hterm0)
            (mul_le_mul_of_nonneg_right hcmpP (by positivity))) hcmp8
    _ = _ := by dsimp [d];ring

private theorem cubic_close_card (S:Finset ℕ) (r h:ℕ) :
    (S.filter (fun (p:ℕ) => |(p:ℝ)-r| ≤(h:ℝ))).card≤2*h+1 := by
  have hsub : S.filter (fun (p:ℕ) => |(p:ℝ)-r| ≤(h:ℝ)) ⊆ Finset.Icc (r-h) (r+h) := by
    intro p hp
    obtain ⟨hl,hu⟩ := abs_le.mp (Finset.mem_filter.mp hp).2
    have hpr : p≤r+h := by exact_mod_cast (show (p:ℝ)≤r+h by linarith)
    have hrp : r≤p+h := by exact_mod_cast (show (r:ℝ)≤p+h by linarith)
    exact Finset.mem_Icc.mpr ⟨by omega,hpr⟩
  refine (Finset.card_le_card hsub).trans ?_
  rw [Nat.card_Icc]
  omega

/-- Full-band prime pairs in the indicated nonzero gap annulus; order `(r,p)`. -/
def primeGaussianCubicGapPairs (N D:ℝ) (H:ℕ) : Finset (ℕ×ℕ) :=
  (primeProfileBand N).biUnion (fun r =>
    ((primeProfileBand N).filter (fun (p:ℕ) => D< |(p:ℝ)-r| ∧ |(p:ℝ)-r| ≤(H:ℝ))).image
      (fun (p:ℕ) => (r,p)))

private theorem cubic_gap_pair_mem {N D:ℝ} {H r p:ℕ}
    (h:(r,p)∈primeGaussianCubicGapPairs N D H) :
    r∈primeProfileBand N ∧ p∈primeProfileBand N ∧ D< |(p:ℝ)-r| ∧ |(p:ℝ)-r| ≤(H:ℝ) := by
  obtain ⟨s,hs,ht⟩ := Finset.mem_biUnion.mp h
  obtain ⟨q,hq,he⟩ := Finset.mem_image.mp ht
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
  exact ⟨hs,(Finset.mem_filter.mp hq).1,(Finset.mem_filter.mp hq).2⟩

private theorem cubic_gap_pair_card (N D:ℝ) (H:ℕ) :
    (primeGaussianCubicGapPairs N D H).card≤(primeProfileBand N).card*(2*H+1) := by
  unfold primeGaussianCubicGapPairs
  calc
    _ ≤ ∑ r∈primeProfileBand N,
        (((primeProfileBand N).filter (fun (p:ℕ) => D< |(p:ℝ)-r| ∧ |(p:ℝ)-r| ≤(H:ℝ))).image
          (fun (p:ℕ) => (r,p))).card := Finset.card_biUnion_le
    _ ≤ ∑ _r∈primeProfileBand N, (2*H+1) := by
      apply Finset.sum_le_sum
      intro r hr
      refine (Finset.card_image_le).trans ?_
      refine (Finset.card_le_card ?_).trans (cubic_close_card (primeProfileBand N) r H)
      intro p hp
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).1,(Finset.mem_filter.mp hp).2.2⟩
    _ = _ := by simp

/-- Sum of norms after each q-row has been completed, at the physical cubic scale. -/
def primeGaussianCubicGapRowMass (N D:ℝ) (H:ℕ) : ℝ :=
  ∑ rp∈primeGaussianCubicGapPairs N D H,
    ‖primeGaussianCubicCompleteRow N rp.2 rp.1‖

private theorem cubic_gap_rows_bound :
    ∃ C:ℝ, 0<C ∧ ∀ᶠ N:ℝ in atTop, ∀ D:ℝ, 0<D → ∀ H:ℕ,
      (Real.log N)^2/N*primeGaussianCubicGapRowMass N D H ≤
        C*(2*(H:ℝ)+1)*(1/D^2+(1+H)/(Real.log N)^12+
          (1+H)/N+Real.log N/N) := by
  obtain ⟨C,hC,hrow⟩ := exists_primeGaussianCubicCompleteRow_bound
  let A:ℝ := 2*Real.log 4
  have hA : 0<A := by dsimp [A];positivity
  refine ⟨A*C,by positivity,?_⟩
  filter_upwards [hrow,eventually_gt_atTop (1:ℝ)] with N hr hN
  intro D hD H
  have hN0 : 0<N := by linarith
  have hL : 0<Real.log N := Real.log_pos hN
  let B:ℝ := C/Real.log N*(1/D^2+(1+H)/(Real.log N)^12+(1+H)/N)+C/N
  have hB : 0≤B := by dsimp [B];positivity
  have hb (rp:ℕ×ℕ) (hp:rp∈primeGaussianCubicGapPairs N D H) :
      ‖primeGaussianCubicCompleteRow N rp.2 rp.1‖≤B := by
    obtain ⟨hrr,hpp,hdlo,hdhi⟩ := cubic_gap_pair_mem hp
    have hneq : rp.2≠rp.1 := by
      intro he
      rw [he,sub_self,abs_zero] at hdlo
      linarith
    refine (hr _ hpp _ hrr hneq).trans ?_
    have hi : 1/|(rp.2:ℝ)-rp.1|^2≤1/D^2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos hD) (by nlinarith [abs_nonneg ((rp.2:ℝ)-rp.1)])
    dsimp [B]
    gcongr
  have hs : primeGaussianCubicGapRowMass N D H≤
      (primeProfileBand N).card*(2*(H:ℝ)+1)*B := by
    calc
      _ ≤ ∑ _rp∈primeGaussianCubicGapPairs N D H, B := Finset.sum_le_sum hb
      _ = (primeGaussianCubicGapPairs N D H).card*B := by simp
      _ ≤ (primeProfileBand N).card*(2*(H:ℝ)+1)*B := by
        apply mul_le_mul_of_nonneg_right _ hB
        exact_mod_cast cubic_gap_pair_card N D H
  have hc : (primeProfileBand N).card≤A*N/Real.log N :=
    (le_div_iff₀ hL).mpr (primeProfileBand_card_log_le hN)
  calc
    _ ≤ (Real.log N)^2/N*((primeProfileBand N).card*(2*(H:ℝ)+1)*B) := by gcongr
    _ ≤ (Real.log N)^2/N*((A*N/Real.log N)*(2*(H:ℝ)+1)*B) := by gcongr
    _ = _ := by dsimp [B];field_simp

private theorem cubic_row_conductor_eq (m:ℕ) :
    (primeGaussianHyperbolicConductor m:ℝ) = ((10000000:ℝ)^4)^m := by
  change (((10000000:ℕ)^(4*m):ℕ):ℝ)=_
  rw [Nat.cast_pow,pow_mul]
  norm_cast

private theorem cubic_row_conductor_log (m:ℕ) :
    Real.log (primeGaussianHyperbolicConductor m:ℝ) = (4*Real.log 10000000)*(m:ℝ) := by
  rw [cubic_row_conductor_eq,Real.log_pow,Real.log_pow]
  ring

private theorem cubic_row_band_budget_tendsto :
    Tendsto (fun m:ℕ => (2*(m:ℝ)^3+1)*
      (1/((m:ℝ)^2/10000000)^2+(1+(m:ℝ)^3)/(Real.log (primeGaussianHyperbolicConductor m:ℝ))^12+
        (1+(m:ℝ)^3)/(primeGaussianHyperbolicConductor m:ℝ)+
        Real.log (primeGaussianHyperbolicConductor m:ℝ)/(primeGaussianHyperbolicConductor m:ℝ)))
      atTop (𝓝 0) := by
  let K:ℝ := 10000000
  let a:ℝ := 4*Real.log K
  have ha : 0<a := by dsimp [a,K];positivity
  have hinv (k:ℕ) (hk:k≠0) : Tendsto (fun m:ℕ => 1/(m:ℝ)^k) atTop (𝓝 0) := by
    exact tendsto_const_div_pow 1 k hk
  have hp (k:ℕ) : Tendsto (fun m:ℕ => (m:ℝ)^k/(primeGaussianHyperbolicConductor m:ℝ))
      atTop (𝓝 0) := by
    simpa only [cubic_row_conductor_eq] using
      tendsto_pow_const_div_const_pow_of_one_lt k
        (show (1:ℝ)<(10000000:ℝ)^4 from one_lt_pow₀ (by norm_num) (by norm_num))
  have hb : Tendsto (fun m:ℕ => 2+1/(m:ℝ)^3) atTop (𝓝 2) := by
    simpa only [add_zero] using tendsto_const_nhds.add (hinv 3 (by norm_num))
  have hc : Tendsto (fun m:ℕ => 1+1/(m:ℝ)^3) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add (hinv 3 (by norm_num))
  have hdec := (((hb.mul ((hinv 1 (by norm_num)).const_mul (K^2))).add
      ((hb.mul hc).mul ((hinv 6 (by norm_num)).const_mul (1/a^12)))).add
        ((hb.mul hc).mul (hp 6))).add ((hb.mul (hp 4)).const_mul a)
  simp only [pow_one,mul_zero,add_zero] at hdec
  apply hdec.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with m hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<1) hm)
  have hN0 : (0:ℝ)<primeGaussianHyperbolicConductor m := by
    rw [cubic_row_conductor_eq];positivity
  rw [cubic_row_conductor_log]
  change _=(2*(m:ℝ)^3+1)*(1/((m:ℝ)^2/K)^2+
    (1+(m:ℝ)^3)/(a*(m:ℝ))^12+(1+(m:ℝ)^3)/(primeGaussianHyperbolicConductor m:ℝ)+
      (a*(m:ℝ))/(primeGaussianHyperbolicConductor m:ℝ))
  field_simp [hm0.ne',ha.ne',hN0.ne']
  ring

/-- Cancellation after completing every q-row on a widening actual prime-pair band.
This is the norm of each complete row, summed over ALL pairs in the annulus. -/
theorem tendsto_primeGaussianCubicGapRowMass :
    Tendsto (fun m:ℕ =>
      (Real.log (primeGaussianHyperbolicConductor m:ℝ))^2/(primeGaussianHyperbolicConductor m:ℝ)*
        primeGaussianCubicGapRowMass (primeGaussianHyperbolicConductor m)
          ((m:ℝ)^2/10000000) (m^3)) atTop (𝓝 0) := by
  obtain ⟨C,hC,hbound⟩ := cubic_gap_rows_bound
  have ht := cubic_row_band_budget_tendsto.const_mul C
  simp only [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · filter_upwards [tendsto_primeGaussianHyperbolicConductor.eventually_gt_atTop 0] with m hm
    exact mul_nonneg (div_nonneg (sq_nonneg _) hm.le)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  · filter_upwards [tendsto_primeGaussianHyperbolicConductor.eventually hbound,
      eventually_ge_atTop (1:ℕ)] with m hm hm1
    have hm0 : (0:ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0<1) hm1)
    have hb := hm ((m:ℝ)^2/10000000) (by positivity) (m^3)
    push_cast at hb
    simpa only [mul_assoc] using hb

/-- The two Jordan parts on precisely the complete-row gap family. -/
def primeGaussianCubicGapSignedVariation (negative:Bool) (N D:ℝ) (H:ℕ) : ℝ :=
  ∑ rp∈primeGaussianCubicGapPairs N D H, primeGaussianCubicSignedRow negative N rp

private theorem cubic_signed_row_nonneg (b:Bool) (N:ℝ) (rp:ℕ×ℕ) :
    0≤primeGaussianCubicSignedRow b N rp := by
  apply Finset.sum_nonneg
  intro q hq
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

private theorem cubic_polylog_pair_subset {m:ℕ} (hm:0 < m) :
    primeGaussianPolylogPairs m ⊆ primeGaussianCubicGapPairs
      (primeGaussianHyperbolicConductor m) ((m:ℝ)^2/10000000) (m^3) := by
  rintro ⟨r,p⟩ hrp
  obtain ⟨hr,hp,hrl,hru,hpl,hpu,hdl,hdu⟩ := primeGaussianPolylogPairs_mem hm hrp
  have hN : (0:ℝ)<primeGaussianHyperbolicConductor m := by
    rw [cubic_row_conductor_eq];positivity
  have hrb : r∈primeProfileBand (primeGaussianHyperbolicConductor m) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨(Nat.floor_lt hN.le).mpr (by linarith),Nat.le_floor (by linarith)⟩,hr⟩
  have hpb : p∈primeProfileBand (primeGaussianHyperbolicConductor m) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
      ⟨(Nat.floor_lt hN.le).mpr (by linarith),Nat.le_floor (by linarith)⟩,hp⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨r,hrb,Finset.mem_image.mpr ⟨p,?_,rfl⟩⟩
  exact Finset.mem_filter.mpr ⟨hpb,hdl,by exact_mod_cast hdu⟩

private theorem cubic_polylog_gap_scales :
    ∀ᶠ m:ℕ in atTop, 0 < m ∧ 256≤(m:ℝ)^2/10000000 ∧
      (m:ℝ)^3≤(primeGaussianNearWidth m:ℝ) := by
  have ht := tendsto_pow_const_div_const_pow_of_one_lt 3
    (by norm_num : (1:ℝ)<10000000)
  have hs : Tendsto (fun m:ℕ => (m:ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0) :
      Tendsto (fun x:ℝ => x^2) atTop atTop).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  filter_upwards [ht.eventually_le_const (by norm_num : (0:ℝ)<1),
    hs.eventually_ge_atTop (256*10000000),eventually_ge_atTop (1:ℕ)] with m hm hs hm1
  refine ⟨by omega,by exact (le_div_iff₀ (by norm_num : (0:ℝ)<10000000)).mpr hs,?_⟩
  have hh := (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<10000000) m)).mp hm
  change (m:ℝ)^3≤((10000000:ℕ)^m:ℕ)
  simpa using hh

private theorem exists_cubic_gap_signed_mass :
    ∃ A:ℝ, 0<A ∧ ∀ᶠ m:ℕ in atTop, ∀ b:Bool,
      A*(m:ℝ)^2 ≤
        (Real.log (primeGaussianHyperbolicConductor m:ℝ))^2/(primeGaussianHyperbolicConductor m:ℝ)*
          primeGaussianCubicGapSignedVariation b (primeGaussianHyperbolicConductor m)
            ((m:ℝ)^2/10000000) (m^3) := by
  obtain ⟨c,hc,hpairs⟩ := exists_primeGaussianPolylogPairs_mass
  obtain ⟨a,ha,hrow⟩ := exists_primeGaussianCentralPair_signed_row
  let L:ℝ := 4*Real.log 10000000
  have hL : 0<L := by dsimp [L];positivity
  refine ⟨c*a/L,by positivity,?_⟩
  filter_upwards [hpairs,hrow,cubic_polylog_gap_scales,
    tendsto_primeGaussianHyperbolicConductor.eventually_gt_atTop 1] with m hm hr hs hN1
  intro b
  have hN : (0:ℝ)<primeGaussianHyperbolicConductor m := by linarith
  have hlog : 0<Real.log (primeGaussianHyperbolicConductor m:ℝ) := Real.log_pos hN1
  have hm0 : (0:ℝ) < m := by exact_mod_cast hs.1
  have hrows : ((primeGaussianPolylogPairs m).card:ℝ)*(a/Real.log (primeGaussianHyperbolicConductor m:ℝ)) ≤
      primeGaussianCubicGapSignedVariation b (primeGaussianHyperbolicConductor m)
        ((m:ℝ)^2/10000000) (m^3) := by
    calc
      _ = ∑ _rp∈primeGaussianPolylogPairs m, a/Real.log (primeGaussianHyperbolicConductor m:ℝ) := by simp
      _ ≤ ∑ rp∈primeGaussianPolylogPairs m,
          primeGaussianCubicSignedRow b (primeGaussianHyperbolicConductor m) rp := by
        apply Finset.sum_le_sum
        rintro ⟨r,p⟩ hrp
        obtain ⟨hrP,hpP,hrl,hru,hpl,hpu,hdl,hdu⟩ := primeGaussianPolylogPairs_mem hs.1 hrp
        exact hr b r p ⟨hrP,hpP,hrl,hru,hpl,hpu⟩ (hs.2.1.trans hdl.le) (hdu.trans hs.2.2)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (cubic_polylog_pair_subset hs.1)
        (fun rp _ _ => cubic_signed_row_nonneg b _ rp)
  have hmass := (mul_le_mul_of_nonneg_right hm
    (div_nonneg ha.le hlog.le)).trans hrows
  have hnorm := mul_le_mul_of_nonneg_left hmass
    (show 0≤(Real.log (primeGaussianHyperbolicConductor m:ℝ))^2/(primeGaussianHyperbolicConductor m:ℝ) by positivity)
  calc
    _ = (Real.log (primeGaussianHyperbolicConductor m:ℝ))^2/(primeGaussianHyperbolicConductor m:ℝ)*
        (c*(primeGaussianHyperbolicConductor m:ℝ)*(m:ℝ)^3/
          (Real.log (primeGaussianHyperbolicConductor m:ℝ))^2*
            (a/Real.log (primeGaussianHyperbolicConductor m:ℝ))) := by
      rw [cubic_row_conductor_log]
      change c*a/L*(m:ℝ)^2 = (L*(m:ℝ))^2/(primeGaussianHyperbolicConductor m:ℝ)*
        (c*(primeGaussianHyperbolicConductor m:ℝ)*(m:ℝ)^3/(L*(m:ℝ))^2*(a/(L*(m:ℝ))))
      field_simp [hL.ne',hm0.ne',hN.ne']
    _ ≤ _ := hnorm

/-- Each signed part of the SAME cancelled complete-row family diverges.
Together with `tendsto_primeGaussianCubicGapRowMass`, this is actual cancellation
of individually divergent physical prime contributions. -/
theorem tendsto_primeGaussianCubicGapSignedVariation (negative:Bool) :
    Tendsto (fun m:ℕ =>
      (Real.log (primeGaussianHyperbolicConductor m:ℝ))^2/(primeGaussianHyperbolicConductor m:ℝ)*
        primeGaussianCubicGapSignedVariation negative (primeGaussianHyperbolicConductor m)
          ((m:ℝ)^2/10000000) (m^3)) atTop atTop := by
  obtain ⟨A,hA,hmass⟩ := exists_cubic_gap_signed_mass
  have ht : Tendsto (fun m:ℕ => (m:ℝ)^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ)≠0) :
      Tendsto (fun x:ℝ => x^2) atTop atTop).comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply tendsto_atTop.2
  intro B
  filter_upwards [hmass,ht.eventually_ge_atTop (B/A)] with m hm hb
  have hB : B≤A*(m:ℝ)^2 := by simpa only [mul_comm] using (div_le_iff₀ hA).mp hb
  exact hB.trans (hm negative)

end RHTower
