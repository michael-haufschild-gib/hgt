import GaloisForLFunctions.RHTower.Suzuki.SuzukiLagariasMeromorphicInner
import GaloisForLFunctions.RHTower.FarFieldAnchor
import GaloisForLFunctions.RHTower.SelbergThetaHorizontalTransform
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.HTGeometry.VerticalContourShift
import Mathlib.Analysis.MellinInversion

/-!
# Analytic boundary symbol of the literal horizontal theta source

The proved safe-half-plane Mellin symbol has one mean pole and a pole-cleared
numerator analytic throughout `Re z >= -1`. The critical-strip Xi zero bound and
the Lagarias half-shift limit control its Xi ratio without a critical-line premise.

On the spectral boundary, the arithmetic phase has modulus one. Its even real
coefficient is exactly half the squared modulus of `1 + phase`, hence lies in
`[0,2]`. Uniform Gamma/zeta estimates supply exponential vertical decay and
absolute line integrability over the full strip needed for a contour shift.

This module identifies and controls the analytic symbol. Its transfer to the
literal native scalar integral is a separate contour-and-pairing step.
-/

open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate
namespace RHTower.SelbergThetaHorizontalBoundary
noncomputable section

private theorem strip_half : XiZeroHalfPlaneBound (1/2) := by
  intro rho hz
  by_contra hn
  have hh : 1 < rho.re := by push Not at hn; linarith
  exact xi_ne_zero_of_one_lt_re hh hz

private theorem half_shift_bound (w : ℂ) (hw : w.im < 0) :
    ‖XiC (w+(1/2:ℂ)*I)‖ ≤ ‖XiC (w-(1/2:ℂ)*I)‖ := by
  have hf : Continuous (fun c : ℝ => ‖XiC (w+(c:ℂ)*I)‖) :=
    (XiC_differentiable.continuous.comp (by fun_prop)).norm
  have hg : Continuous (fun c : ℝ => ‖XiC (w-(c:ℂ)*I)‖) :=
    (XiC_differentiable.continuous.comp (by fun_prop)).norm
  have h := le_on_closure
    (s := Ioi (1/2:ℝ))
    (f := fun c : ℝ => ‖XiC (w+(c:ℂ)*I)‖)
    (g := fun c : ℝ => ‖XiC (w-(c:ℂ)*I)‖)
    (fun c hc => (norm_XiC_vertical_shift_lt_of_halfPlaneBound hc strip_half w hw).le)
    hf.continuousOn hg.continuousOn
    (x := (1/2:ℝ)) (by simpa only [closure_Ioi, mem_Ici] using (le_rfl : (1/2:ℝ) ≤ 1/2))
  simpa using h

private theorem native_scattering_xi_bound {s : ℂ} (hs : 1/2 < s.re) :
    ‖xi (2*s-1)/xi (2*s)‖ ≤ 1 := by
  have hw : (-I*(2*s-1)).im < 0 := by
    simp [Complex.mul_im]
    linarith
  have h := half_shift_bound (-I*(2*s-1)) hw
  have h1 : 1/2+(-I*(2*s-1)+(1/2:ℂ)*I)*I = 2*s-1 := by
    linear_combination -(2*s-3/2)*I_sq
  have h2 : 1/2+(-I*(2*s-1)-(1/2:ℂ)*I)*I = 2*s := by
    linear_combination -(2*s-1/2)*I_sq
  simp only [XiC,h1,h2] at h
  rw [norm_div]
  exact (div_le_one (norm_pos_iff.mpr (xi_ne_zero_of_one_lt_re (by simp; linarith)))).2 h


/-- The pole-free Xi quotient appearing in the completed scattering ratio. -/
def scatteringCore (z : ℂ) : ℂ := xi (z+1)/xi (z+2)

/-- The literal horizontal Mellin numerator with its mean pole cleared. -/
def poleNumerator (z : ℂ) : ℂ :=
  xi (z+3/2)*(z+(z+2)*scatteringCore z)

/-- Meromorphic continuation of the literal horizontal Mellin transform. -/
def symbol (z : ℂ) : ℂ := poleNumerator z/z

/-- Residue of the horizontal source at its mean pole. -/
def mainTerm : ℂ := poleNumerator 0

private theorem denominator_ne {z : ℂ} (hz : -1 ≤ z.re) : xi (z+2) ≠ 0 := by
  apply xi_ne_zero_of_one_le_re
  change 1 ≤ z.re+2
  linarith

/-- The complete Xi quotient is contractive down to the spectral boundary. -/
theorem norm_scatteringCore_le {z : ℂ} (hz : -1 ≤ z.re) :
    ‖scatteringCore z‖ ≤ 1 := by
  rcases eq_or_lt_of_le hz with he | he
  · have hc : z+1 = 1-conj (z+2) := by
      apply Complex.ext <;> simp
      linarith
    rw [scatteringCore,hc,xi_one_sub,xi_conj,norm_div,norm_conj,
      div_self (norm_pos_iff.mpr (denominator_ne hz)).ne']
  · have hs : 1/2 < ((z+2)/2).re := by simp; linarith
    have h := native_scattering_xi_bound hs
    have h1 : 2*((z+2)/2)-1 = z+1 := by ring
    have h2 : 2*((z+2)/2) = z+2 := by ring
    change ‖xi (2*((z+2)/2)-1)/xi (2*((z+2)/2))‖ ≤ 1 at h
    rw [h1,h2] at h
    exact h

private theorem scatteringCore_analytic {z : ℂ} (hz : -1 ≤ z.re) :
    AnalyticAt ℂ scatteringCore z := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => z+1) z := by fun_prop
  have h2 : AnalyticAt ℂ (fun z : ℂ => z+2) z := by fun_prop
  exact ((xi_differentiable.analyticAt _).comp h1).div
    ((xi_differentiable.analyticAt _).comp h2) (denominator_ne hz)

/-- The pole-cleared numerator is analytic at every point of the closed contour strip. -/
theorem poleNumerator_analytic {z : ℂ} (hz : -1 ≤ z.re) :
    AnalyticAt ℂ poleNumerator z := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => z+3/2) z := by fun_prop
  exact ((xi_differentiable.analyticAt _).comp h1).mul
    (analyticAt_id.add ((analyticAt_id.add analyticAt_const).mul (scatteringCore_analytic hz)))

/-- The source symbol is analytic off its unique mean pole in this half-plane. -/
theorem symbol_analytic {z : ℂ} (hz : -1 ≤ z.re) (hne : z ≠ 0) :
    AnalyticAt ℂ symbol z :=
  (poleNumerator_analytic hz).div analyticAt_id hne

private theorem symbol_factored {z : ℂ} (hne : z ≠ 0) :
    symbol z = xi (z+3/2)*(1+(z+2)/z*scatteringCore z) := by
  unfold symbol poleNumerator
  field_simp

private theorem xi_eq_lambda {z : ℂ} (hz : 0 < z.re) (hne : z ≠ 1) :
    xi z = z*(z-1)/2*reflectedCompletedLambda z := by
  have h0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [xi_eq_half_mul h0 hne,reflectedCompletedLambda,riemannZeta_def_of_ne_zero h0]
  field_simp [Complex.Gammaℝ_ne_zero_of_re_pos hz]

/-- On the absolute-convergence half-plane, this is exactly the proved source symbol. -/
theorem symbol_eq_source {z : ℂ} (hz : 0 < z.re) :
    symbol z = xi (z+3/2)*(1+reflectedCompletedLambda (z+1)/reflectedCompletedLambda (z+2)) := by
  have h0 : z ≠ 0 := by intro h; simp [h] at hz
  have h1 : z+1 ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : z+2 ≠ 1 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1p : 0 < (z+1).re := by simp; linarith
  have h2p : 0 < (z+2).re := by simp; linarith
  have hd := denominator_ne (z := z) (by linarith)
  have he1 := xi_eq_lambda h1p h1
  have he2 := xi_eq_lambda h2p h2
  have hL : reflectedCompletedLambda (z+2) ≠ 0 := by
    intro h
    rw [he2,h,mul_zero] at hd
    exact hd rfl
  rw [symbol_factored h0,scatteringCore]
  congr 2
  rw [he1,he2]
  have ha : z+1 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  have hb : z+2 ≠ 0 := by intro h; have := congrArg Complex.re h; simp at this; linarith
  field_simp
  ring

/-- The actual horizontal theta mean has this Mellin transform, with absolute convergence. -/
theorem source_hasMellin {z : ℂ} (hz : 0 < z.re) :
    HasMellin (fun a : ℝ => (SelbergThetaCommonForcingPairing.horizontalWeight (a^2):ℂ)) z
      (symbol z) := by
  rw [symbol_eq_source hz]
  exact SelbergThetaHorizontalTransform.horizontalWeight_square_hasMellin hz

/-- Exact residue expressed only in entire Xi values. -/
theorem mainTerm_eq : mainTerm = xi (3/2)/xi 2 := by
  simp [mainTerm,poleNumerator,scatteringCore,xi_one]
  ring

/-- Uniform domination of the source symbol away from the compact portion of the strip. -/
theorem norm_symbol_le {z : ℂ} (hz : -1 ≤ z.re) (him : 1 ≤ |z.im|) :
    ‖symbol z‖ ≤ 4*‖xi (z+3/2)‖ := by
  have hn : 1 ≤ ‖z‖ := him.trans (Complex.abs_im_le_norm z)
  have hp : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hn
  have hne : z ≠ 0 := norm_pos_iff.mp hp
  have hq : ‖(z+2)/z‖ ≤ 3 := by
    rw [norm_div,div_le_iff₀ hp]
    have h := norm_add_le z (2:ℂ)
    norm_num at h
    linarith
  rw [symbol_factored hne,norm_mul]
  have h : ‖1+(z+2)/z*scatteringCore z‖ ≤ 4 := by
    calc _ ≤ ‖(1:ℂ)‖+‖(z+2)/z*scatteringCore z‖ := norm_add_le _ _
         _ ≤ 1+3*1 := by
           rw [norm_one,norm_mul]
           have hp := mul_le_mul hq (norm_scatteringCore_le hz) (norm_nonneg _) (by norm_num)
           linarith
         _ = 4 := by norm_num
  calc _ ≤ ‖xi (z+3/2)‖*4 := mul_le_mul_of_nonneg_left h (norm_nonneg _)
       _ = _ := mul_comm _ _

/-- Uniform exponential vertical decay on the entire Xi strip required by the source contour. -/
theorem xi_strip_decay :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ z : ℂ,
      1/2 ≤ z.re → z.re ≤ 2 → 2 ≤ |z.im| →
      ‖xi z‖ ≤ C*|z.im|^N*Real.exp (-(Real.pi*|z.im|/4)) := by
  obtain ⟨C,N,hC,hG⟩ := GaloisForLFunctions.HTGeometry.exists_bound_norm_Gamma_vertical_strip
    (a := (1/4:ℝ)) (by norm_num) 1
  obtain ⟨D,M,hD,hZ⟩ := exists_bound_norm_riemannZeta_strip 2
  refine ⟨2*C*D,N+M+2,by positivity,?_⟩
  intro z hlo hhi ht
  have hp : 0 < |z.im| := by linarith
  have hz0 : z ≠ 0 := by intro h; norm_num [h] at ht
  have hz1 : z ≠ 1 := by intro h; norm_num [h] at ht
  have hg := hG (z.re/2) (z.im/2) (by linarith) (by linarith)
    (by rw [abs_div]; norm_num; linarith)
  have he : ((z.re/2:ℝ):ℂ)+((z.im/2:ℝ):ℂ)*I = z/2 := by
    apply Complex.ext <;> simp
  rw [he] at hg
  have ht2 : |z.im/2| ≤ |z.im| := by rw [abs_div]; norm_num
  have hgg : ‖Complex.Gamma (z/2)‖ ≤ C*|z.im|^N*Real.exp (-(Real.pi*|z.im|/4)) := by
    have hex : -(Real.pi*|z.im/2|/2) = -(Real.pi*|z.im|/4) := by
      rw [abs_div]; norm_num; ring
    rw [hex] at hg
    exact hg.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) ht2 N) hC)
      (Real.exp_pos _).le)
  have hpi : Real.pi^(-z.re/2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by linarith)
  have hgr : ‖Complex.Gammaℝ z‖ ≤ C*|z.im|^N*Real.exp (-(Real.pi*|z.im|/4)) := by
    rw [GaloisForLFunctions.HTGeometry.norm_Gammaℝ]
    calc _ ≤ 1*(C*|z.im|^N*Real.exp (-(Real.pi*|z.im|/4))) :=
            mul_le_mul hpi hgg (norm_nonneg _) zero_le_one
         _ = _ := one_mul _
  have hn : ‖z‖ ≤ 2*|z.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_pos (by linarith : 0 < z.re)] at h
    linarith
  have hn1 : ‖z-1‖ ≤ 2*|z.im| := by
    have h := Complex.norm_le_abs_re_add_abs_im (z-1)
    have hr : |z.re-1| ≤ 1 := abs_le.mpr ⟨by linarith,by linarith⟩
    simp only [Complex.sub_re,Complex.one_re,Complex.sub_im,Complex.one_im,sub_zero] at h
    linarith
  have hzz : ‖riemannZeta z‖ ≤ D*|z.im|^M := by
    have h := hZ z.re z.im (abs_le.mpr ⟨by linarith, hhi⟩) (by linarith)
    simpa only [Complex.re_add_im] using h
  rw [xi_eq_lambda (by linarith) hz1,reflectedCompletedLambda]
  simp only [norm_mul,norm_div,Complex.norm_ofNat]
  calc _ ≤ (2*|z.im|)*(2*|z.im|)/2 *
          ((C*|z.im|^N*Real.exp (-(Real.pi*|z.im|/4)))*(D*|z.im|^M)) := by
          gcongr
       _ = _ := by rw [pow_add,pow_add,pow_two]; ring

/-- The complete arithmetic scattering phase on the spectral boundary. -/
def boundaryPhase (t : ℝ) : ℂ :=
  ((-1+(t:ℂ)*I)+2)/(-1+(t:ℂ)*I)*scatteringCore (-1+(t:ℂ)*I)

/-- Real coefficient in the even part of the boundary source symbol. -/
def boundaryWeight (t : ℝ) : ℝ := 1+(boundaryPhase t).re

private theorem boundary_ne (t : ℝ) : (-1+(t:ℂ)*I:ℂ) ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  norm_num at hr

/-- Exact boundary value, retaining both parabolic and arithmetic contributions. -/
theorem symbol_boundary (t : ℝ) :
    symbol (-1+(t:ℂ)*I) = XiC (t:ℂ)*(1+boundaryPhase t) := by
  rw [symbol_factored (boundary_ne t)]
  have he : (-1+(t:ℂ)*I)+3/2 = 1/2+(t:ℂ)*I := by ring
  rw [he]
  rfl

/-- The full boundary scattering phase is unimodular. -/
theorem norm_boundaryPhase (t : ℝ) : ‖boundaryPhase t‖ = 1 := by
  let z : ℂ := -1+(t:ℂ)*I
  have hz : -1 ≤ z.re := by simp [z]
  have hc : z+1 = 1-conj (z+2) := by
    apply Complex.ext <;> simp [z]
    norm_num
  have hd : ‖scatteringCore z‖ = 1 := by
    rw [scatteringCore,hc,xi_one_sub,xi_conj,norm_div,norm_conj,
      div_self (norm_pos_iff.mpr (denominator_ne hz)).ne']
  have he : z+2 = -conj z := by
    apply Complex.ext <;> simp [z]
    norm_num
  change ‖(z+2)/z*scatteringCore z‖ = 1
  rw [norm_mul,hd,mul_one,norm_div,he,norm_neg,norm_conj,
    div_self (norm_pos_iff.mpr (boundary_ne t)).ne']

/-- The actual arithmetic coefficient lies between zero and two. -/
theorem boundaryWeight_bounds (t : ℝ) : 0 ≤ boundaryWeight t ∧ boundaryWeight t ≤ 2 := by
  have h := Complex.abs_re_le_norm (boundaryPhase t)
  rw [norm_boundaryPhase] at h
  have hr := abs_le.mp h
  unfold boundaryWeight
  constructor <;> linarith

/-- The boundary coefficient has an exact squared-modulus representation. -/
theorem boundaryWeight_eq_half_sq (t : ℝ) :
    boundaryWeight t = ‖1+boundaryPhase t‖^2/2 := by
  rw [Complex.sq_norm,Complex.normSq_add,Complex.normSq_eq_norm_sq,
    Complex.normSq_eq_norm_sq,norm_boundaryPhase]
  simp only [norm_one,one_pow,one_mul,Complex.conj_re]
  unfold boundaryWeight
  ring

/-- Frequency reflection conjugates the complete arithmetic phase. -/
theorem boundaryPhase_neg (t : ℝ) : boundaryPhase (-t) = conj (boundaryPhase t) := by
  have hz : (-1+((-t:ℝ):ℂ)*I:ℂ) = conj (-1+(t:ℂ)*I) := by
    apply Complex.ext <;> simp
  unfold boundaryPhase scatteringCore
  rw [hz]
  simp only [map_mul,map_div₀,map_add,map_one,map_ofNat,← xi_conj]

/-- The real boundary coefficient is even. -/
theorem boundaryWeight_neg (t : ℝ) : boundaryWeight (-t) = boundaryWeight t := by
  rw [boundaryWeight,boundaryWeight,boundaryPhase_neg,Complex.conj_re]

/-- The coefficient vanishes at the removable zero-frequency seam. -/
theorem boundaryWeight_zero : boundaryWeight 0 = 0 := by
  norm_num [boundaryWeight,boundaryPhase,scatteringCore,xi_zero,xi_one]


/-- Each vertical Xi line across the required closed strip is absolutely integrable. -/
theorem xi_line_integrable {c : ℝ} (hc : 1/2 ≤ c) (hc' : c ≤ 2) :
    Integrable (fun t : ℝ => xi ((c:ℂ)+(t:ℂ)*I)) := by
  obtain ⟨C,N,hC,hb⟩ := xi_strip_decay
  let g : ℝ → ℝ := fun t => C*|t|^N*Real.exp (-(Real.pi*|t|/4))
  have hg : Integrable g := by
    have h := (integrable_abs_pow_mul_exp_neg_mul_abs N
      (c := Real.pi/4) (by positivity)).const_mul C
    have he (t : ℝ) : -(Real.pi*|t|/4) = -(Real.pi/4)*|t| := by ring
    simpa only [g,he,mul_assoc] using h
  have ht : Continuous (fun t : ℝ => xi ((c:ℂ)+(t:ℂ)*I)) :=
    xi_differentiable.continuous.comp (by fun_prop)
  have hm : IntegrableOn (fun t : ℝ => xi ((c:ℂ)+(t:ℂ)*I)) (Icc (-2:ℝ) 2) :=
    ht.continuousOn.integrableOn_compact isCompact_Icc
  have ho : IntegrableOn (fun t : ℝ => xi ((c:ℂ)+(t:ℂ)*I)) (Icc (-2:ℝ) 2)ᶜ := by
    apply hg.integrableOn.mono' ht.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with t ht
    have ha : 2 ≤ |t| := by
      by_contra hn
      apply ht
      have hh := abs_lt.mp (lt_of_not_ge hn)
      exact ⟨hh.1.le,hh.2.le⟩
    simpa only [g,Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_mul,
      add_zero,zero_add,sub_zero] using hb ((c:ℂ)+(t:ℂ)*I) (by simpa using hc)
        (by simpa using hc') (by simpa using ha)
  rw [← integrableOn_univ,← union_compl_self (Icc (-2:ℝ) 2)]
  exact hm.union ho


end
end RHTower.SelbergThetaHorizontalBoundary
