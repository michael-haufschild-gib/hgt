import GaloisForLFunctions.RHTower.ChiCubicPhysicalAmplitudeBudgets
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Uniform decay of the actual reciprocal height integrals

The selected Gaussian/logarithmic slice has uniform mass and first variation.
For every fixed height-window jet order, compact joint smoothness bounds that
jet and its height derivative. Both complex frequency denominators and their
height derivative retain product decay on the physical band.

The exact full-line identity `(1+iD) ∫ exp(-iD/r) f =
∫ exp(-iD/r) (f - deriv(r²f))` pays the defect direction, including `D = 0`.
Support away from zero proves every derivative and integrability obligation.
The final theorem retains the original selected amplitude and all window jets;
its constant is uniform in shrinking width, logarithmic parameter, physical
coordinates, and every real frequency/defect. No variation, cancellation or
interchange bound is assumed. Tangential assembly and full frequency energy
remain subsequent obligations.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace


private theorem oscillation_norm (t : ℝ) : ‖bourgainOscillation t‖=1 := by
  rw [bourgainOscillation,Complex.norm_exp]
  simp

private theorem reciprocal_measurable (D : ℝ) :
    AEStronglyMeasurable (fun r : ℝ => bourgainOscillation (-D/r)) volume := by
  apply Measurable.aestronglyMeasurable
  unfold bourgainOscillation
  fun_prop

private theorem reciprocal_integrable (D : ℝ) {f : ℝ→ℂ} (hf : Integrable f) :
    Integrable (fun r : ℝ => bourgainOscillation (-D/r)*f r) :=
  hf.bdd_mul (reciprocal_measurable D) (Eventually.of_forall
    (fun r => (oscillation_norm (-D/r)).le))

private theorem reciprocal_deriv (D r : ℝ) (hr : r≠0) :
    HasDerivAt (fun x : ℝ => bourgainOscillation (-D/x))
      (Complex.I*(D : ℂ)/(r : ℂ)^2*bourgainOscillation (-D/r)) r := by
  have hd := ((((hasDerivAt_id r).inv hr).const_mul (-D)).ofReal_comp.const_mul Complex.I).cexp
  convert hd using 1
  · funext x
    simp [bourgainOscillation,div_eq_mul_inv]
  · simp only [id_eq,Pi.inv_apply,bourgainOscillation,div_eq_mul_inv,Complex.ofReal_mul,
      Complex.ofReal_neg,Complex.ofReal_inv,Complex.ofReal_pow,Complex.ofReal_one]
    ring

private theorem reciprocal_resolvent {f : ℝ→ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : ∀x : ℝ, x∉Icc (1 : ℝ) 2 → f x=0) (D : ℝ) :
    (1+Complex.I*(D : ℂ))*(∫r : ℝ, bourgainOscillation (-D/r)*f r) =
      ∫r : ℝ, bourgainOscillation (-D/r)*(f r-deriv (fun t : ℝ => (t : ℂ)^2*f t) r) := by
  have hsub : tsupport f⊆Icc (1 : ℝ) 2 :=
    closure_minimal (Function.support_subset_iff'.mpr hs) isClosed_Icc
  have hcompact : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (Function.support_subset_iff'.mpr hs)
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hcompact
  let g : ℝ→ℂ := fun r => (r : ℂ)^2*f r
  have hg : ContDiff ℝ ∞ g := (Complex.ofRealCLM.contDiff.pow 2).mul hf
  have hgc : HasCompactSupport g := hcompact.mul_left
  have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have hgdi : Integrable (deriv g) :=
    (hg.continuous_deriv (by simp)).integrable_of_hasCompactSupport hgc.deriv
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hphase (r : ℝ) :
      deriv (fun x : ℝ => bourgainOscillation (-D/x)) r*g r =
        (Complex.I*(D : ℂ))*(bourgainOscillation (-D/r)*f r) := by
    by_cases hr : r=0
    · have hz : f 0=0 := hs 0 (by norm_num)
      simp [g,hr,hz]
    · rw [(reciprocal_deriv D r hr).deriv]
      dsimp only [g]
      field_simp [Complex.ofReal_ne_zero.mpr hr]
  have hleft : Integrable (fun r : ℝ =>
      fderiv ℝ (fun x : ℝ => bourgainOscillation (-D/x)) r 1*g r) := by
    change Integrable (fun r : ℝ => deriv (fun x : ℝ => bourgainOscillation (-D/x)) r*g r)
    simp_rw [hphase]
    exact (reciprocal_integrable D hfi).const_mul _
  have hright : Integrable (fun r : ℝ =>
      bourgainOscillation (-D/r)*fderiv ℝ g r 1) := reciprocal_integrable D hgdi
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (v := (1 : ℝ)) hleft hright (reciprocal_integrable D hgi)
    (fun r hr => (reciprocal_deriv D r (by
      have hh := hsub (tsupport_mul_subset_right hr)
      exact (lt_of_lt_of_le zero_lt_one hh.1).ne')).differentiableAt)
    (fun r _ => hgd r)
  change (∫r : ℝ, bourgainOscillation (-D/r)*deriv g r)=
    -(∫r : ℝ, deriv (fun x : ℝ => bourgainOscillation (-D/x)) r*g r) at hibp
  simp_rw [hphase] at hibp
  rw [integral_const_mul] at hibp
  simp_rw [mul_sub]
  rw [integral_sub (reciprocal_integrable D hfi) (reciprocal_integrable D hgdi),hibp]
  ring

private theorem reciprocal_resolvent_bound {f : ℝ→ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : ∀x : ℝ, x∉Icc (1 : ℝ) 2 → f x=0) (D : ℝ) :
    (1+|D|)*‖∫r : ℝ, bourgainOscillation (-D/r)*f r‖ ≤
      2*((∫r : ℝ, ‖f r‖)+
        ∫r : ℝ, ‖deriv (fun t : ℝ => (t : ℂ)^2*f t) r‖) := by
  have hcompact : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (Function.support_subset_iff'.mpr hs)
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hcompact
  let g : ℝ→ℂ := fun r => (r : ℂ)^2*f r
  have hg : ContDiff ℝ ∞ g := (Complex.ofRealCLM.contDiff.pow 2).mul hf
  have hgc : HasCompactSupport g := hcompact.mul_left
  have hgdi : Integrable (deriv g) :=
    (hg.continuous_deriv (by simp)).integrable_of_hasCompactSupport hgc.deriv
  have hcoef : 1+|D|≤2*‖1+Complex.I*(D : ℂ)‖ := by
    have hre := Complex.abs_re_le_norm (1+Complex.I*(D : ℂ))
    have him := Complex.abs_im_le_norm (1+Complex.I*(D : ℂ))
    simp only [Complex.add_re,Complex.one_re,Complex.mul_re,Complex.I_re,
      Complex.ofReal_re,Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,
      sub_zero,add_zero,abs_one] at hre
    simp only [Complex.add_im,Complex.one_im,Complex.mul_im,Complex.I_re,
      Complex.ofReal_re,Complex.I_im,Complex.ofReal_im,zero_mul,one_mul,zero_add] at him
    linarith
  have hb : ‖∫r : ℝ, bourgainOscillation (-D/r)*(f r-deriv g r)‖≤
      (∫r : ℝ, ‖f r‖)+(∫r : ℝ, ‖deriv g r‖) := by
    calc ‖∫r : ℝ, bourgainOscillation (-D/r)*(f r-deriv g r)‖
        ≤ ∫r : ℝ, ‖f r‖+‖deriv g r‖ :=
          norm_integral_le_of_norm_le (hfi.norm.add hgdi.norm) (Eventually.of_forall
            (fun r => by rw [norm_mul,oscillation_norm,one_mul]; exact norm_sub_le _ _))
      _ = _ := integral_add hfi.norm hgdi.norm
  calc (1+|D|)*‖∫r : ℝ, bourgainOscillation (-D/r)*f r‖
      ≤ 2*‖1+Complex.I*(D : ℂ)‖*‖∫r : ℝ, bourgainOscillation (-D/r)*f r‖ :=
        mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    _ = 2*‖∫r : ℝ, bourgainOscillation (-D/r)*(f r-deriv g r)‖ := by
      rw [mul_assoc,←norm_mul,reciprocal_resolvent hf hs D]
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (by norm_num)

private theorem reciprocal_variation_bound {f : ℝ→ℂ} (hf : ContDiff ℝ ∞ f)
    (hs : ∀x : ℝ, x∉Icc (1 : ℝ) 2 → f x=0) (D : ℝ) :
    (1+|D|)*‖∫r : ℝ, bourgainOscillation (-D/r)*f r‖ ≤
      10*((∫r : ℝ, ‖f r‖)+(∫r : ℝ, ‖deriv f r‖)) := by
  have hcompact : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (Function.support_subset_iff'.mpr hs)
  have hsub : tsupport f⊆Icc (1 : ℝ) 2 :=
    closure_minimal (Function.support_subset_iff'.mpr hs) isClosed_Icc
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hcompact
  have hfdi : Integrable (deriv f) :=
    (hf.continuous_deriv (by simp)).integrable_of_hasCompactSupport hcompact.deriv
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  let g : ℝ→ℂ := fun r => (r : ℂ)^2*f r
  have hg : ContDiff ℝ ∞ g := (Complex.ofRealCLM.contDiff.pow 2).mul hf
  have hgc : HasCompactSupport g := hcompact.mul_left
  have hgdi : Integrable (deriv g) :=
    (hg.continuous_deriv (by simp)).integrable_of_hasCompactSupport hgc.deriv
  have hd (r : ℝ) : deriv g r=2*(r : ℂ)*f r+(r : ℂ)^2*deriv f r := by
    have hh := (((hasDerivAt_id r).ofReal_comp.pow 2).mul (hfd r).hasDerivAt).deriv
    change deriv g r = _ at hh
    simpa using hh
  have hpoint (r : ℝ) : ‖deriv g r‖≤4*‖f r‖+4*‖deriv f r‖ := by
    rw [hd]
    by_cases hr : r∈Icc (1 : ℝ) 2
    · have hn : ‖(r : ℂ)‖≤2 := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith only [hr.1])]
        exact hr.2
      calc ‖2*(r : ℂ)*f r+(r : ℂ)^2*deriv f r‖
          ≤ ‖2*(r : ℂ)*f r‖+‖(r : ℂ)^2*deriv f r‖ := norm_add_le _ _
        _ ≤ _ := by
          simp only [norm_mul,norm_pow,Complex.norm_ofNat]
          gcongr <;> nlinarith [norm_nonneg (r : ℂ)]
    · have hz := hs r hr
      have hdz : deriv f r=0 := deriv_of_notMem_tsupport (fun hh => hr (hsub hh))
      simp only [hz,hdz,mul_zero,add_zero,norm_zero]
      exact le_rfl
  have hi : (∫r : ℝ, ‖deriv g r‖)≤
      4*(∫r : ℝ, ‖f r‖)+4*(∫r : ℝ, ‖deriv f r‖) := by
    calc (∫r : ℝ, ‖deriv g r‖)≤∫r : ℝ, 4*‖f r‖+4*‖deriv f r‖ :=
        integral_mono hgdi.norm ((hfi.norm.const_mul 4).add (hfdi.norm.const_mul 4)) hpoint
      _ = _ := by rw [integral_add (hfi.norm.const_mul 4) (hfdi.norm.const_mul 4)]
                  simp only [integral_const_mul]
  have hb := reciprocal_resolvent_bound hf hs D
  change (1+|D|)*‖∫r : ℝ, bourgainOscillation (-D/r)*f r‖ ≤
      2*((∫r : ℝ, ‖f r‖)+(∫r : ℝ, ‖deriv g r‖)) at hb
  have hnn : 0≤∫r : ℝ, ‖deriv f r‖ := integral_nonneg (fun r => norm_nonneg _)
  linarith

private def bandInverse (a r : ℝ) : ℂ := ((r : ℂ)+Complex.I*(a : ℂ))⁻¹

private theorem band_nonzero (a : ℝ) {r : ℝ} (hr : 1≤r) :
    (r : ℂ)+Complex.I*(a : ℂ) ≠ 0 := by
  intro hh
  have he := congrArg Complex.re hh
  simp at he
  linarith

private theorem band_inverse_bounds (a : ℝ) {r : ℝ} (hr : 1≤r) :
    ‖bandInverse a r‖≤1 ∧ (1+|a|)*‖bandInverse a r‖≤2 := by
  have hn : 0<‖(r : ℂ)+Complex.I*(a : ℂ)‖ := norm_pos_iff.mpr (band_nonzero a hr)
  have hre := Complex.abs_re_le_norm ((r : ℂ)+Complex.I*(a : ℂ))
  have him := Complex.abs_im_le_norm ((r : ℂ)+Complex.I*(a : ℂ))
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
    Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,add_zero] at hre
  simp only [Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
    Complex.ofReal_re,Complex.I_im,zero_mul,one_mul,zero_add] at him
  have hrn : 1≤‖(r : ℂ)+Complex.I*(a : ℂ)‖ := hr.trans ((le_abs_self r).trans hre)
  have hw : 1+|a|≤2*‖(r : ℂ)+Complex.I*(a : ℂ)‖ := by linarith
  simp only [bandInverse,norm_inv]
  refine ⟨(inv_le_one₀ hn).mpr hrn,?_⟩
  rw [←div_eq_mul_inv]
  exact (div_le_iff₀ hn).mpr hw

private theorem band_inverse_deriv (a : ℝ) {r : ℝ} (hr : 1≤r) :
    HasDerivAt (bandInverse a) (-(bandInverse a r)^2) r := by
  have hd := (((hasDerivAt_id r).ofReal_comp).add_const (Complex.I*(a : ℂ))).inv
    (band_nonzero a hr)
  change HasDerivAt (bandInverse a) (-1/((r : ℂ)+Complex.I*(a : ℂ))^2) r at hd
  have he : (-1 : ℂ)/((r : ℂ)+Complex.I*(a : ℂ))^2 = -(bandInverse a r)^2 := by
    simp [bandInverse,div_eq_mul_inv]
  rw [he] at hd
  exact hd

private def bandMultiplier (a b r : ℝ) : ℂ := bandInverse a r*bandInverse b r

private theorem band_multiplier_smooth (a b : ℝ) {r : ℝ} (hr : 1≤r) :
    ContDiffAt ℝ ∞ (bandMultiplier a b) r := by
  exact ((Complex.ofRealCLM.contDiff.contDiffAt.add contDiffAt_const).inv
    (band_nonzero a hr)).mul
    ((Complex.ofRealCLM.contDiff.contDiffAt.add contDiffAt_const).inv (band_nonzero b hr))

private theorem band_multiplier_bounds (a b : ℝ) {r : ℝ} (hr : 1≤r) :
    ((1+|a|)*(1+|b|))*‖bandMultiplier a b r‖≤4 ∧
    ((1+|a|)*(1+|b|))*‖deriv (bandMultiplier a b) r‖≤8 := by
  obtain ⟨ha,hwa⟩ := band_inverse_bounds a hr
  obtain ⟨hb,hwb⟩ := band_inverse_bounds b hr
  have hna := norm_nonneg (bandInverse a r)
  have hnb := norm_nonneg (bandInverse b r)
  have hfirst : ((1+|a|)*(1+|b|))*‖bandMultiplier a b r‖≤4 := by
    rw [bandMultiplier,norm_mul]
    calc ((1+|a|)*(1+|b|))*(‖bandInverse a r‖*‖bandInverse b r‖)
        = ((1+|a|)*‖bandInverse a r‖)*((1+|b|)*‖bandInverse b r‖) := by ring
      _ ≤ 2*2 := mul_le_mul hwa hwb (by positivity) (by norm_num)
      _ = 4 := by ring
  have hd : deriv (bandMultiplier a b) r =
      -(bandInverse a r)^2*bandInverse b r-bandInverse a r*(bandInverse b r)^2 := by
    have hh := ((band_inverse_deriv a hr).mul (band_inverse_deriv b hr)).deriv
    change deriv (bandMultiplier a b) r = _ at hh
    simpa only [sub_eq_add_neg,mul_neg] using hh
  have hderiv : ‖deriv (bandMultiplier a b) r‖≤2*‖bandMultiplier a b r‖ := by
    rw [hd,bandMultiplier,norm_mul]
    calc ‖-(bandInverse a r)^2*bandInverse b r-bandInverse a r*(bandInverse b r)^2‖
        ≤ ‖-(bandInverse a r)^2*bandInverse b r‖+
            ‖bandInverse a r*(bandInverse b r)^2‖ := norm_sub_le _ _
      _ = ‖bandInverse a r‖^2*‖bandInverse b r‖+
          ‖bandInverse a r‖*‖bandInverse b r‖^2 := by simp only [norm_mul,norm_neg,norm_pow]
      _ ≤ ‖bandInverse a r‖*‖bandInverse b r‖+
          ‖bandInverse a r‖*‖bandInverse b r‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (by nlinarith : ‖bandInverse a r‖^2≤‖bandInverse a r‖) hnb)
          (mul_le_mul_of_nonneg_left (by nlinarith : ‖bandInverse b r‖^2≤‖bandInverse b r‖) hna)
      _ = _ := by ring
  refine ⟨hfirst,?_⟩
  calc ((1+|a|)*(1+|b|))*‖deriv (bandMultiplier a b) r‖
      ≤ ((1+|a|)*(1+|b|))*(2*‖bandMultiplier a b r‖) :=
        mul_le_mul_of_nonneg_left hderiv (by positivity)
    _ = 2*(((1+|a|)*(1+|b|))*‖bandMultiplier a b r‖) := by ring
    _ ≤ 8 := by linarith


/-- Literal height-window derivative generated by tangential integration by parts. -/
def bagCubicReciprocalWindowJet (j : ℕ) (pq : ℝ×ℝ) (r : ℝ) : ℂ :=
  ((iteratedDeriv j (bagPhysicalHeightWindow : ℝ→ℝ) (pq.1*pq.2/r) : ℝ) : ℂ)/(r : ℂ)^j

private theorem window_derivatives_smooth (j : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv j (bagPhysicalHeightWindow : ℝ→ℝ)) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using bagPhysicalHeightWindow.contDiff
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

private theorem window_jet_smooth (j : ℕ) (z : (ℝ×ℝ)×ℝ) (hz : z.2≠0) :
    ContDiffAt ℝ ∞ (fun w : (ℝ×ℝ)×ℝ => bagCubicReciprocalWindowJet j w.1 w.2) z := by
  have hn : ContDiffAt ℝ ∞ (fun w : (ℝ×ℝ)×ℝ =>
      ((iteratedDeriv j (bagPhysicalHeightWindow : ℝ→ℝ) (w.1.1*w.1.2/w.2) : ℝ) : ℂ)) z :=
    (Complex.ofRealCLM.contDiff.comp (window_derivatives_smooth j)).contDiffAt.comp z
      ((contDiffAt_fst.fst.mul contDiffAt_fst.snd).div contDiffAt_snd hz)
  have hd : ContDiffAt ℝ ∞ (fun w : (ℝ×ℝ)×ℝ => (w.2 : ℂ)^j) z :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z contDiffAt_snd).pow j
  have h : ContDiffAt ℝ ∞ (fun w : (ℝ×ℝ)×ℝ =>
      ((iteratedDeriv j (bagPhysicalHeightWindow : ℝ→ℝ) (w.1.1*w.1.2/w.2) : ℝ) : ℂ)*
        ((w.2 : ℂ)^j)⁻¹) z := hn.mul (hd.inv (pow_ne_zero j (Complex.ofReal_ne_zero.mpr hz)))
  simpa only [bagCubicReciprocalWindowJet,div_eq_mul_inv] using h

private theorem window_jet_bounds (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀p∈Icc (1 : ℝ) 2, ∀q∈Icc (1 : ℝ) 2,
      ∀r∈Icc (1 : ℝ) 2, ‖bagCubicReciprocalWindowJet j (p,q) r‖+‖deriv (bagCubicReciprocalWindowJet j (p,q)) r‖≤C := by
  let K := (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2) ×ˢ Icc (1 : ℝ) 2
  have hc : ContinuousOn (fun w : (ℝ×ℝ)×ℝ =>
      ‖bagCubicReciprocalWindowJet j w.1 w.2‖+‖deriv (bagCubicReciprocalWindowJet j w.1) w.2‖) K := by
    intro z hz
    have hzn : z.2≠0 := (lt_of_lt_of_le zero_lt_one hz.2.1).ne'
    have hf := window_jet_smooth j z hzn
    have hcomp : ContDiffAt ℝ ∞
        (fun w : ((ℝ×ℝ)×ℝ)×ℝ => bagCubicReciprocalWindowJet j w.1.1 w.2) (z,z.2) :=
      hf.comp (z,z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    have hd : ContDiffAt ℝ ∞
        (fun w : (ℝ×ℝ)×ℝ => fderiv ℝ (bagCubicReciprocalWindowJet j w.1) w.2) z :=
      hcomp.fderiv contDiffAt_snd (by simp)
    have hd' : ContDiffAt ℝ ∞
        (fun w : (ℝ×ℝ)×ℝ => deriv (bagCubicReciprocalWindowJet j w.1) w.2) z :=
      hd.clm_apply (contDiffAt_const (c := (1 : ℝ)))
    exact (hf.continuousAt.norm.add hd'.continuousAt.norm).continuousWithinAt
  obtain ⟨C,hC⟩ := ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc).exists_bound_of_continuousOn hc
  refine ⟨max C 0+1,by positivity,fun p hp q hq r hr => ?_⟩
  have hh := hC ((p,q),r) ⟨⟨hp,hq⟩,hr⟩
  change |‖bagCubicReciprocalWindowJet j (p,q) r‖+‖deriv (bagCubicReciprocalWindowJet j (p,q)) r‖|≤C at hh
  exact (le_abs_self _).trans (hh.trans (by linarith [le_max_left C 0]))


/-- Original conjugated slice and window jet, with both full complex frequency denominators. -/
def bagCubicReciprocalHeightAmplitude (j : ℕ) (δ h : ℝ) (pq : ℝ×ℝ) (a b r : ℝ) : ℂ :=
  star (bagCubicNormalizedSlice δ h r)*bagCubicReciprocalWindowJet j pq r*bandMultiplier a b r

private theorem height_amplitude_off (j : ℕ)
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (pq : ℝ×ℝ) (a b : ℝ) {r : ℝ} (hr : r∉Icc (1 : ℝ) 2) :
    bagCubicReciprocalHeightAmplitude j δ.1 h.1 pq a b r=0 := by
  simp only [bagCubicReciprocalHeightAmplitude,(bagCubicNormalizedSlice_properties δ h).2 r hr,star_zero,zero_mul]

private theorem height_amplitude_smooth (j : ℕ)
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (pq : ℝ×ℝ) (a b : ℝ) : ContDiff ℝ ∞ (bagCubicReciprocalHeightAmplitude j δ.1 h.1 pq a b) := by
  have hF := (bagCubicNormalizedSlice_properties δ h).1
  have hstar : ContDiff ℝ ∞ (fun r => star (bagCubicNormalizedSlice δ.1 h.1 r)) :=
    Complex.conjCLE.contDiff.comp hF
  rw [contDiff_iff_contDiffAt]
  intro r
  by_cases hr : r∈Icc (1 : ℝ) 2
  · have hW : ContDiffAt ℝ ∞ (bagCubicReciprocalWindowJet j pq) r :=
      (window_jet_smooth j (pq,r) (lt_of_lt_of_le zero_lt_one hr.1).ne').comp r
        (contDiffAt_const.prodMk contDiffAt_id)
    exact (hstar.contDiffAt.mul hW).mul (band_multiplier_smooth a b hr.1)
  · have heq : bagCubicReciprocalHeightAmplitude j δ.1 h.1 pq a b =ᶠ[𝓝 r] (fun _ => (0 : ℂ)) := by
      filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hr] with t ht
      exact height_amplitude_off j δ h pq a b ht
    exact contDiffAt_const.congr_of_eventuallyEq heq

private theorem height_amplitude_bounds (j : ℕ)
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (pq : ℝ×ℝ) (a b C : ℝ) (hC : 0≤C)
    (hw : ∀r∈Icc (1 : ℝ) 2, ‖bagCubicReciprocalWindowJet j pq r‖+‖deriv (bagCubicReciprocalWindowJet j pq) r‖≤C)
    (r : ℝ) :
    ((1+|a|)*(1+|b|))*‖bagCubicReciprocalHeightAmplitude j δ.1 h.1 pq a b r‖≤
      4*C*‖bagCubicNormalizedSlice δ.1 h.1 r‖ ∧
    ((1+|a|)*(1+|b|))*‖deriv (bagCubicReciprocalHeightAmplitude j δ.1 h.1 pq a b) r‖≤
      12*C*‖bagCubicNormalizedSlice δ.1 h.1 r‖+
        4*C*‖deriv (bagCubicNormalizedSlice δ.1 h.1) r‖ := by
  let F := bagCubicNormalizedSlice δ.1 h.1
  let W := bagCubicReciprocalWindowJet j pq
  let K := bandMultiplier a b
  let m := (1+|a|)*(1+|b|)
  have hm : 0 ≤ m := by positivity
  by_cases hr : r∈Icc (1 : ℝ) 2
  · have hw0 : ‖W r‖≤C := (le_add_of_nonneg_right (norm_nonneg _)).trans (hw r hr)
    have hw1 : ‖deriv W r‖≤C := (le_add_of_nonneg_left (norm_nonneg _)).trans (hw r hr)
    obtain ⟨hk0,hk1⟩ := band_multiplier_bounds a b hr.1
    have hF : Differentiable ℝ F := (bagCubicNormalizedSlice_properties δ h).1.differentiable (by simp)
    have hW : DifferentiableAt ℝ W r :=
      ((window_jet_smooth j (pq,r) (lt_of_lt_of_le zero_lt_one hr.1).ne').comp r
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by simp)
    have hK : DifferentiableAt ℝ K r := (band_multiplier_smooth a b hr.1).differentiableAt (by simp)
    have hd : deriv (bagCubicReciprocalHeightAmplitude j δ.1 h.1 pq a b) r =
        (star (deriv F r)*W r+star (F r)*deriv W r)*K r+star (F r)*W r*deriv K r := by
      have hh := (((hF r).hasDerivAt.star.mul hW.hasDerivAt).mul hK.hasDerivAt).deriv
      change deriv (bagCubicReciprocalHeightAmplitude j δ.1 h.1 pq a b) r = _ at hh
      exact hh
    constructor
    · change m*‖star (F r)*W r*K r‖≤4*C*‖F r‖
      simp only [norm_mul,norm_star]
      calc m*(‖F r‖*‖W r‖*‖K r‖)=‖F r‖*‖W r‖*(m*‖K r‖) := by ring
        _ ≤ ‖F r‖*C*4 := by gcongr
        _ = _ := by ring
    · rw [hd]
      have hn : ‖(star (deriv F r)*W r+star (F r)*deriv W r)*K r+
          star (F r)*W r*deriv K r‖ ≤
          (‖deriv F r‖*‖W r‖+‖F r‖*‖deriv W r‖)*‖K r‖+
            ‖F r‖*‖W r‖*‖deriv K r‖ := by
        calc _ ≤ ‖(star (deriv F r)*W r+star (F r)*deriv W r)*K r‖+
            ‖star (F r)*W r*deriv K r‖ := norm_add_le _ _
          _ ≤ _ := by
            simp only [norm_mul,norm_star]
            gcongr
            simpa only [norm_mul,norm_star] using norm_add_le
              (star (deriv F r)*W r) (star (F r)*deriv W r)
      change m*‖(star (deriv F r)*W r+star (F r)*deriv W r)*K r+
        star (F r)*W r*deriv K r‖≤_
      calc _ ≤ m*((‖deriv F r‖*‖W r‖+‖F r‖*‖deriv W r‖)*‖K r‖+
          ‖F r‖*‖W r‖*‖deriv K r‖) := mul_le_mul_of_nonneg_left hn hm
        _ = (‖deriv F r‖*‖W r‖+‖F r‖*‖deriv W r‖)*(m*‖K r‖)+
          ‖F r‖*‖W r‖*(m*‖deriv K r‖) := by ring
        _ ≤ (‖deriv F r‖*C+‖F r‖*C)*4+‖F r‖*C*8 := by gcongr
        _ = _ := by ring
  · have hz := height_amplitude_off j δ h pq a b hr
    have ht : tsupport (bagCubicReciprocalHeightAmplitude j δ.1 h.1 pq a b)⊆Icc (1 : ℝ) 2 :=
      closure_minimal (Function.support_subset_iff'.mpr (fun x hx =>
        height_amplitude_off j δ h pq a b hx)) isClosed_Icc
    have hdz : deriv (bagCubicReciprocalHeightAmplitude j δ.1 h.1 pq a b) r=0 :=
      deriv_of_notMem_tsupport (fun hh => hr (ht hh))
    rw [hz,hdz,norm_zero,mul_zero]
    constructor <;> positivity


/-- Every actual height-window jet has admitted, uniformly decaying reciprocal height action. -/
theorem bagCubicReciprocalHeight_uniform_decay (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1},
      ∀p q : {r : ℝ // r∈Icc (1 : ℝ) 2}, ∀a b D : ℝ,
      Integrable (fun r : ℝ => bourgainOscillation (-D/r)*bagCubicReciprocalHeightAmplitude j δ.1 h.1 (p.1,q.1) a b r) ∧
      ((1+|a|)*(1+|b|))*(1+|D|)*
        ‖∫r : ℝ, bourgainOscillation (-D/r)*bagCubicReciprocalHeightAmplitude j δ.1 h.1 (p.1,q.1) a b r‖≤C := by
  obtain ⟨A,hA,hAb⟩ := bagCubicNormalizedSlice_derivative_budgets 0
  obtain ⟨B,hB,hBb⟩ := bagCubicNormalizedSlice_derivative_budgets 1
  obtain ⟨C,hC,hCb⟩ := window_jet_bounds j
  refine ⟨10*(16*C*A+4*C*B),by positivity,fun δ h p q a b D => ?_⟩
  let F := bagCubicNormalizedSlice δ.1 h.1
  let f := bagCubicReciprocalHeightAmplitude j δ.1 h.1 (p.1,q.1) a b
  let m := (1+|a|)*(1+|b|)
  have hm : 0 ≤ m := by positivity
  have hmass : Integrable (fun r : ℝ => ‖F r‖) ∧ (∫r : ℝ, ‖F r‖)≤A := by
    simpa only [iteratedDeriv_zero,Nat.zero_sub,pow_zero,div_one] using hAb δ h
  have hvar : Integrable (fun r : ℝ => ‖deriv F r‖) ∧ (∫r : ℝ, ‖deriv F r‖)≤B := by
    simpa only [iteratedDeriv_one,Nat.sub_self,pow_zero,div_one] using hBb δ h
  have hf : ContDiff ℝ ∞ f := height_amplitude_smooth j δ h (p.1,q.1) a b
  have hs : ∀r : ℝ, r∉Icc (1 : ℝ) 2 → f r=0 :=
    fun r hr => height_amplitude_off j δ h (p.1,q.1) a b hr
  have hc : HasCompactSupport f := HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (Function.support_subset_iff'.mpr hs)
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  have hfdi : Integrable (deriv f) :=
    (hf.continuous_deriv (by simp)).integrable_of_hasCompactSupport hc.deriv
  have hpw (r : ℝ) := height_amplitude_bounds j δ h (p.1,q.1) a b C hC.le
    (hCb p.1 p.2 q.1 q.2) r
  have hmassf : m*(∫r : ℝ, ‖f r‖)≤4*C*A := by
    calc m*(∫r : ℝ, ‖f r‖) = ∫r : ℝ, m*‖f r‖ := (integral_const_mul _ _).symm
      _ ≤ ∫r : ℝ, 4*C*‖F r‖ :=
        integral_mono (hfi.norm.const_mul m) (hmass.1.const_mul (4*C)) (fun r => (hpw r).1)
      _ = 4*C*(∫r : ℝ, ‖F r‖) := integral_const_mul _ _
      _ ≤ 4*C*A := mul_le_mul_of_nonneg_left hmass.2 (by positivity)
  have hvarf : m*(∫r : ℝ, ‖deriv f r‖)≤12*C*A+4*C*B := by
    calc m*(∫r : ℝ, ‖deriv f r‖) = ∫r : ℝ, m*‖deriv f r‖ := (integral_const_mul _ _).symm
      _ ≤ ∫r : ℝ, 12*C*‖F r‖+4*C*‖deriv F r‖ :=
        integral_mono (hfdi.norm.const_mul m)
          ((hmass.1.const_mul (12*C)).add (hvar.1.const_mul (4*C))) (fun r => (hpw r).2)
      _ = 12*C*(∫r : ℝ, ‖F r‖)+4*C*(∫r : ℝ, ‖deriv F r‖) := by
        rw [integral_add (hmass.1.const_mul (12*C)) (hvar.1.const_mul (4*C))]
        simp only [integral_const_mul]
      _ ≤ 12*C*A+4*C*B := add_le_add
        (mul_le_mul_of_nonneg_left hmass.2 (by positivity))
        (mul_le_mul_of_nonneg_left hvar.2 (by positivity))
  refine ⟨reciprocal_integrable D hfi,?_⟩
  change m*(1+|D|)*‖∫r : ℝ, bourgainOscillation (-D/r)*f r‖≤_
  calc m*(1+|D|)*‖∫r : ℝ, bourgainOscillation (-D/r)*f r‖
      = m*((1+|D|)*‖∫r : ℝ, bourgainOscillation (-D/r)*f r‖) := by ring
    _ ≤ m*(10*((∫r : ℝ, ‖f r‖)+(∫r : ℝ, ‖deriv f r‖))) :=
      mul_le_mul_of_nonneg_left (reciprocal_variation_bound hf hs D) hm
    _ = 10*(m*(∫r : ℝ, ‖f r‖)+m*(∫r : ℝ, ‖deriv f r‖)) := by ring
    _ ≤ 10*(16*C*A+4*C*B) := by linarith


end RHTower.BAGTrace
