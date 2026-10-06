import GaloisForLFunctions.RHTower.ChiCubicReciprocalHeightDecay
import Mathlib.MeasureTheory.Integral.Prod
import GaloisForLFunctions.RHTower.ChiCubicNormalizedFourier

/-!
# Uniform coupled decay of the actual reciprocal cubic kernel

Two exact tangential resolvents generate three height-window jets. Compact
physical support admits their full Fubini exchange, and actual height decay
bounds the full kernel by a positive coupled-frequency integral. All original
Gaussian/logarithmic, conjugation, window and shrinking-cutoff factors remain.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff FourierTransform
open GaloisForLFunctions.RHTower
namespace RHTower.BAGTrace

private theorem linear_phase_deriv (t x : ℝ) :
    HasDerivAt (fun y : ℝ => bourgainOscillation (-t*y))
      (-(Complex.I*(t : ℂ))*bourgainOscillation (-t*x)) x := by
  have hd := (((hasDerivAt_id x).const_mul (-t)).ofReal_comp.const_mul Complex.I).cexp
  change HasDerivAt (fun y : ℝ => bourgainOscillation (-t*y)) _ x at hd
  convert hd using 1
  simp only [id_eq,bourgainOscillation,Complex.ofReal_mul,Complex.ofReal_neg,mul_one]
  ring

private theorem linear_phase_integrable (t : ℝ) {f : ℝ→ℂ} (hf : Integrable f) :
    Integrable (fun x : ℝ => bourgainOscillation (-t*x)*f x) := by
  have hc : Continuous (fun x : ℝ => bourgainOscillation (-t*x)) := by
    unfold bourgainOscillation
    fun_prop
  exact hf.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall
    (fun x => (norm_bourgainOscillation (-t*x)).le))

private theorem linear_resolvent {f : ℝ→ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (t : ℝ) :
    (1+Complex.I*(t : ℂ))*(∫x : ℝ, bourgainOscillation (-t*x)*f x) =
      ∫x : ℝ, bourgainOscillation (-t*x)*(f x+deriv f x) := by
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hc
  have hfdi : Integrable (deriv f) :=
    (hf.continuous_deriv (by simp)).integrable_of_hasCompactSupport hc.deriv
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hphase (x : ℝ) : deriv (fun y : ℝ => bourgainOscillation (-t*y)) x*f x =
      -(Complex.I*(t : ℂ))*(bourgainOscillation (-t*x)*f x) := by
    rw [(linear_phase_deriv t x).deriv]
    ring
  have hleft : Integrable (fun x : ℝ =>
      fderiv ℝ (fun y : ℝ => bourgainOscillation (-t*y)) x 1*f x) := by
    change Integrable (fun x : ℝ => deriv (fun y : ℝ => bourgainOscillation (-t*y)) x*f x)
    simp_rw [hphase]
    exact (linear_phase_integrable t hfi).const_mul _
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (v := (1 : ℝ)) hleft (linear_phase_integrable t hfdi) (linear_phase_integrable t hfi)
    (fun x _ => (linear_phase_deriv t x).differentiableAt) (fun x _ => hfd x)
  change (∫x : ℝ, bourgainOscillation (-t*x)*deriv f x) =
    -(∫x : ℝ, deriv (fun y : ℝ => bourgainOscillation (-t*y)) x*f x) at hibp
  simp_rw [hphase] at hibp
  rw [integral_const_mul] at hibp
  simp_rw [mul_add]
  rw [integral_add (linear_phase_integrable t hfi) (linear_phase_integrable t hfdi),hibp]
  ring

private theorem scaled_linear_resolvent {f : ℝ→ℂ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (b r : ℝ) (hr : r≠0) :
    ((r : ℂ)+Complex.I*(b : ℂ))*(∫p : ℝ, bourgainOscillation (-b*p/r)*f p) =
      (r : ℂ)*∫p : ℝ, bourgainOscillation (-b*p/r)*(f p+deriv f p) := by
  have hh := congrArg (fun z : ℂ => (r : ℂ)*z) (linear_resolvent hf hc (b/r))
  have he (p : ℝ) : -(b/r)*p=-b*p/r := by ring
  simp_rw [he] at hh
  have hcoef : (r : ℂ)*(1+Complex.I*((b/r : ℝ) : ℂ))=(r : ℂ)+Complex.I*(b : ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hr]
  rw [←mul_assoc,hcoef] at hh
  exact hh

private theorem window_derivatives_smooth (j : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv j (bagPhysicalHeightWindow : ℝ→ℝ)) := by
  induction j with
  | zero => simpa only [iteratedDeriv_zero] using bagPhysicalHeightWindow.contDiff
  | succ j ih =>
    rw [iteratedDeriv_succ]
    exact (contDiff_infty_iff_deriv.mp ih).2

private theorem window_tangent_smooth (j : ℕ) (q r : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ => bagCubicReciprocalWindowJet j (p,q) r) := by
  have hl : ContDiff ℝ ∞ (fun p : ℝ => p*q/r) :=
    (contDiff_id.mul contDiff_const).div_const r
  exact ((Complex.ofRealCLM.contDiff.comp (window_derivatives_smooth j)).comp
    hl).div_const _

private theorem window_tangent_deriv (j : ℕ) (p q r : ℝ) (hr : r≠0) :
    HasDerivAt (fun x : ℝ => bagCubicReciprocalWindowJet j (x,q) r)
      ((q : ℂ)*bagCubicReciprocalWindowJet (j+1) (p,q) r) p := by
  have hW : HasDerivAt (iteratedDeriv j (bagPhysicalHeightWindow : ℝ→ℝ))
      (iteratedDeriv (j+1) (bagPhysicalHeightWindow : ℝ→ℝ) (p*q/r)) (p*q/r) := by
    rw [iteratedDeriv_succ]
    exact ((window_derivatives_smooth j).differentiable (by simp) (p*q/r)).hasDerivAt
  have hd := ((hW.comp p (((hasDerivAt_id p).mul_const q).div_const r)).ofReal_comp).div_const
    ((r : ℂ)^j)
  change HasDerivAt (fun x : ℝ => bagCubicReciprocalWindowJet j (x,q) r) _ p at hd
  convert hd using 1
  simp only [bagCubicReciprocalWindowJet,Complex.ofReal_mul,Complex.ofReal_div,
    one_mul,pow_succ]
  field_simp [Complex.ofReal_ne_zero.mpr hr]

private theorem window_second_tangent_deriv (j : ℕ) (p q r : ℝ) (hr : r≠0) :
    HasDerivAt (fun y : ℝ => bagCubicReciprocalWindowJet j (p,y) r)
      ((p : ℂ)*bagCubicReciprocalWindowJet (j+1) (p,q) r) q := by
  convert window_tangent_deriv j q p r hr using 1
  · funext y
    simp only [bagCubicReciprocalWindowJet,mul_comm p y]
  · simp only [bagCubicReciprocalWindowJet,mul_comm p q]

private def plusSlice (δ h x : ℝ) : ℂ :=
  bagCubicNormalizedSlice δ h x+deriv (bagCubicNormalizedSlice δ h) x

private theorem slice_compact
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) :
    HasCompactSupport (bagCubicNormalizedSlice δ.1 h.1) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (Function.support_subset_iff'.mpr (bagCubicNormalizedSlice_properties δ h).2)

private theorem plus_slice_smooth
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) :
    ContDiff ℝ ∞ (plusSlice δ.1 h.1) := by
  have hf := (bagCubicNormalizedSlice_properties δ h).1
  exact hf.add (contDiff_infty_iff_deriv.mp hf).2

private theorem plus_slice_off
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    {x : ℝ} (hx : x∉Icc (1 : ℝ) 2) : plusSlice δ.1 h.1 x=0 := by
  have hs : tsupport (bagCubicNormalizedSlice δ.1 h.1)⊆Icc (1 : ℝ) 2 :=
    closure_minimal (Function.support_subset_iff'.mpr
      (bagCubicNormalizedSlice_properties δ h).2) isClosed_Icc
  have hd := deriv_of_notMem_tsupport (fun hh => hx (hs hh))
  simp only [plusSlice,(bagCubicNormalizedSlice_properties δ h).2 x hx,hd,add_zero]

private theorem first_tangent_identity
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (q r b : ℝ) (hr : r≠0) :
    ((r : ℂ)+Complex.I*(b : ℂ))*(∫p : ℝ, bourgainOscillation (-b*p/r)*
      (bagCubicNormalizedSlice δ.1 h.1 p*bagCubicReciprocalWindowJet 0 (p,q) r)) =
      (r : ℂ)*∫p : ℝ, bourgainOscillation (-b*p/r)*
        (plusSlice δ.1 h.1 p*bagCubicReciprocalWindowJet 0 (p,q) r+
          (q : ℂ)*bagCubicNormalizedSlice δ.1 h.1 p*bagCubicReciprocalWindowJet 1 (p,q) r) := by
  let F := bagCubicNormalizedSlice δ.1 h.1
  let g : ℝ→ℂ := fun p => F p*bagCubicReciprocalWindowJet 0 (p,q) r
  have hF : ContDiff ℝ ∞ F := (bagCubicNormalizedSlice_properties δ h).1
  have hg : ContDiff ℝ ∞ g := hF.mul (window_tangent_smooth 0 q r)
  have hc : HasCompactSupport g := (slice_compact δ h).mul_right
  calc _ = (r : ℂ)*∫p : ℝ, bourgainOscillation (-b*p/r)*(g p+deriv g p) :=
      scaled_linear_resolvent hg hc b r hr
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with p
      have hd := (((hF.differentiable (by simp)) p).hasDerivAt.mul
        (window_tangent_deriv 0 p q r hr)).deriv
      change deriv g p = _ at hd
      rw [hd]
      dsimp only [g,F,plusSlice]
      ring

private theorem window_second_tangent_smooth (j : ℕ) (p r : ℝ) :
    ContDiff ℝ ∞ (fun q : ℝ => bagCubicReciprocalWindowJet j (p,q) r) := by
  convert window_tangent_smooth j p r using 1
  funext q
  simp only [bagCubicReciprocalWindowJet,mul_comm p q]

private def tangentCoefficient0 (δ h p q : ℝ) : ℂ :=
  plusSlice δ h p*plusSlice δ h q

private def tangentCoefficient1 (δ h p q : ℝ) : ℂ :=
  (p : ℂ)*plusSlice δ h p*bagCubicNormalizedSlice δ h q+
    (q : ℂ)*bagCubicNormalizedSlice δ h p*plusSlice δ h q+
      bagCubicNormalizedSlice δ h p*bagCubicNormalizedSlice δ h q

private def tangentCoefficient2 (δ h p q : ℝ) : ℂ :=
  (p : ℂ)*(q : ℂ)*bagCubicNormalizedSlice δ h p*bagCubicNormalizedSlice δ h q

private theorem second_tangent_identity
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (p r a : ℝ) (hr : r≠0) :
    ((r : ℂ)+Complex.I*(a : ℂ))*(∫q : ℝ, bourgainOscillation (-a*q/r)*
      (bagCubicNormalizedSlice δ.1 h.1 q*
        (plusSlice δ.1 h.1 p*bagCubicReciprocalWindowJet 0 (p,q) r+
          (q : ℂ)*bagCubicNormalizedSlice δ.1 h.1 p*bagCubicReciprocalWindowJet 1 (p,q) r))) =
      (r : ℂ)*∫q : ℝ, bourgainOscillation (-a*q/r)*
        (tangentCoefficient0 δ.1 h.1 p q*bagCubicReciprocalWindowJet 0 (p,q) r+
          tangentCoefficient1 δ.1 h.1 p q*bagCubicReciprocalWindowJet 1 (p,q) r+
          tangentCoefficient2 δ.1 h.1 p q*bagCubicReciprocalWindowJet 2 (p,q) r) := by
  let F := bagCubicNormalizedSlice δ.1 h.1
  let g : ℝ→ℂ := fun q => F q*(plusSlice δ.1 h.1 p*bagCubicReciprocalWindowJet 0 (p,q) r+
    (q : ℂ)*F p*bagCubicReciprocalWindowJet 1 (p,q) r)
  have hF : ContDiff ℝ ∞ F := (bagCubicNormalizedSlice_properties δ h).1
  have hg : ContDiff ℝ ∞ g := hF.mul
    ((contDiff_const.mul (window_second_tangent_smooth 0 p r)).add
      ((Complex.ofRealCLM.contDiff.mul contDiff_const).mul (window_second_tangent_smooth 1 p r)))
  have hc : HasCompactSupport g := (slice_compact δ h).mul_right
  calc _ = (r : ℂ)*∫q : ℝ, bourgainOscillation (-a*q/r)*(g q+deriv g q) :=
      scaled_linear_resolvent hg hc a r hr
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with q
      have hq : HasDerivAt (fun y : ℝ => (y : ℂ)*F p) (F p) q := by
        simpa using ((hasDerivAt_id q).ofReal_comp.mul_const (F p))
      have hd := (((hF.differentiable (by simp)) q).hasDerivAt.mul
        (((window_second_tangent_deriv 0 p q r hr).const_mul (plusSlice δ.1 h.1 p)).add
          (hq.mul (window_second_tangent_deriv 1 p q r hr)))).deriv
      change deriv g q = _ at hd
      rw [hd]
      dsimp only [g,F,plusSlice,tangentCoefficient0,tangentCoefficient1,tangentCoefficient2]
      simp only [Pi.add_apply,Pi.mul_apply]
      ring


private theorem window_pair_smooth (j : ℕ) (r : ℝ) :
    ContDiff ℝ ∞ (fun pq : ℝ×ℝ => bagCubicReciprocalWindowJet j pq r) := by
  have hl : ContDiff ℝ ∞ (fun pq : ℝ×ℝ => pq.1*pq.2/r) :=
    (contDiff_fst.mul contDiff_snd).div_const r
  exact ((Complex.ofRealCLM.contDiff.comp (window_derivatives_smooth j)).comp hl).div_const _

private theorem oscillation_continuous : Continuous bourgainOscillation := by
  unfold bourgainOscillation
  fun_prop

private def firstStage (δ h r a b p q : ℝ) : ℂ :=
  bourgainOscillation (-a*q/r)*bourgainOscillation (-b*p/r)*bagCubicNormalizedSlice δ h q*
    (plusSlice δ h p*bagCubicReciprocalWindowJet 0 (p,q) r+
      (q : ℂ)*bagCubicNormalizedSlice δ h p*bagCubicReciprocalWindowJet 1 (p,q) r)

private theorem first_stage_swap
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (r a b : ℝ) :
    (∫q : ℝ,∫p : ℝ, firstStage δ.1 h.1 r a b p q)=
      ∫p : ℝ,∫q : ℝ, firstStage δ.1 h.1 r a b p q := by
  let T : ℝ×ℝ→ℂ := fun z => firstStage δ.1 h.1 r a b z.1 z.2
  have hF := (bagCubicNormalizedSlice_properties δ h).1.continuous
  have hU := (plus_slice_smooth δ h).continuous
  have hphaseQ : Continuous (fun z : ℝ×ℝ => bourgainOscillation (-a*z.2/r)) :=
    oscillation_continuous.comp ((continuous_const.mul continuous_snd).div_const r)
  have hphaseP : Continuous (fun z : ℝ×ℝ => bourgainOscillation (-b*z.1/r)) :=
    oscillation_continuous.comp ((continuous_const.mul continuous_fst).div_const r)
  have hc : Continuous T :=
    (((hphaseQ.mul hphaseP).mul (hF.comp continuous_snd))).mul
      (((hU.comp continuous_fst).mul (window_pair_smooth 0 r).continuous).add
        (((Complex.ofRealCLM.continuous.comp continuous_snd).mul (hF.comp continuous_fst)).mul
          (window_pair_smooth 1 r).continuous))
  have hs : HasCompactSupport T := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc)
    apply Function.support_subset_iff'.mpr
    intro z hz
    by_cases hp : z.1∈Icc (1 : ℝ) 2
    · have hq : z.2∉Icc (1 : ℝ) 2 := fun hq => hz ⟨hp,hq⟩
      simp only [T,firstStage,(bagCubicNormalizedSlice_properties δ h).2 z.2 hq,mul_zero,zero_mul]
    · simp only [T,firstStage,(bagCubicNormalizedSlice_properties δ h).2 z.1 hp,
        plus_slice_off δ h hp,zero_mul,mul_zero,zero_add]
  have hi : Integrable T (volume.prod volume) := hc.integrable_of_hasCompactSupport hs
  exact (integral_integral_swap (f := firstStage δ.1 h.1 r a b) hi).symm

private def originalStage (δ h r a b p q : ℝ) : ℂ :=
  bourgainOscillation (-a*q/r)*bourgainOscillation (-b*p/r)*bagCubicNormalizedSlice δ h q*
    (bagCubicNormalizedSlice δ h p*bagCubicReciprocalWindowJet 0 (p,q) r)

private def tangentStage (δ h r a b p q : ℝ) : ℂ :=
  bourgainOscillation (-b*p/r)*bourgainOscillation (-a*q/r)*
    (tangentCoefficient0 δ h p q*bagCubicReciprocalWindowJet 0 (p,q) r+
      tangentCoefficient1 δ h p q*bagCubicReciprocalWindowJet 1 (p,q) r+
      tangentCoefficient2 δ h p q*bagCubicReciprocalWindowJet 2 (p,q) r)

private theorem double_tangent_identity
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (r a b : ℝ) (hr : r≠0) :
    ((r : ℂ)+Complex.I*(a : ℂ))*((r : ℂ)+Complex.I*(b : ℂ))*
      (∫q : ℝ,∫p : ℝ, originalStage δ.1 h.1 r a b p q)=
        (r : ℂ)^2*∫p : ℝ,∫q : ℝ, tangentStage δ.1 h.1 r a b p q := by
  let A := (r : ℂ)+Complex.I*(a : ℂ)
  let B := (r : ℂ)+Complex.I*(b : ℂ)
  let F := bagCubicNormalizedSlice δ.1 h.1
  have h1 : B*(∫q : ℝ,∫p : ℝ, originalStage δ.1 h.1 r a b p q)=
      (r : ℂ)*∫q : ℝ,∫p : ℝ, firstStage δ.1 h.1 r a b p q := by
    rw [←integral_const_mul B,←integral_const_mul (r : ℂ)]
    apply integral_congr_ae
    filter_upwards [] with q
    have ho : (∫p : ℝ, originalStage δ.1 h.1 r a b p q)=
        (bourgainOscillation (-a*q/r)*F q)*
          ∫p : ℝ, bourgainOscillation (-b*p/r)*(F p*bagCubicReciprocalWindowJet 0 (p,q) r) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with p
      dsimp only [originalStage,F]
      ring
    have hs : (∫p : ℝ, firstStage δ.1 h.1 r a b p q)=
        (bourgainOscillation (-a*q/r)*F q)*∫p : ℝ, bourgainOscillation (-b*p/r)*
          (plusSlice δ.1 h.1 p*bagCubicReciprocalWindowJet 0 (p,q) r+
            (q : ℂ)*F p*bagCubicReciprocalWindowJet 1 (p,q) r) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with p
      dsimp only [firstStage,F]
      ring
    rw [ho,hs,mul_left_comm B]
    rw [first_tangent_identity δ h q r b hr]
    ring
  have h2 : A*(∫p : ℝ,∫q : ℝ, firstStage δ.1 h.1 r a b p q)=
      (r : ℂ)*∫p : ℝ,∫q : ℝ, tangentStage δ.1 h.1 r a b p q := by
    rw [←integral_const_mul A,←integral_const_mul (r : ℂ)]
    apply integral_congr_ae
    filter_upwards [] with p
    have ho : (∫q : ℝ, firstStage δ.1 h.1 r a b p q)=
        bourgainOscillation (-b*p/r)*∫q : ℝ, bourgainOscillation (-a*q/r)*
          (F q*(plusSlice δ.1 h.1 p*bagCubicReciprocalWindowJet 0 (p,q) r+
            (q : ℂ)*F p*bagCubicReciprocalWindowJet 1 (p,q) r)) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with q
      dsimp only [firstStage,F]
      ring
    have hs : (∫q : ℝ, tangentStage δ.1 h.1 r a b p q)=
        bourgainOscillation (-b*p/r)*∫q : ℝ, bourgainOscillation (-a*q/r)*
          (tangentCoefficient0 δ.1 h.1 p q*bagCubicReciprocalWindowJet 0 (p,q) r+
            tangentCoefficient1 δ.1 h.1 p q*bagCubicReciprocalWindowJet 1 (p,q) r+
            tangentCoefficient2 δ.1 h.1 p q*bagCubicReciprocalWindowJet 2 (p,q) r) := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with q
      dsimp only [tangentStage]
      ring
    rw [ho,hs,mul_left_comm A]
    rw [second_tangent_identity δ h p r a hr]
    ring
  change A*B*_=_
  rw [mul_assoc,h1,first_stage_swap δ h r a b,mul_left_comm A,h2]
  ring

private theorem denominator_ne (a r : ℝ) (hr : r≠0) :
    (r : ℂ)+Complex.I*(a : ℂ)≠0 := by
  intro he
  have hh := congrArg Complex.re he
  simp at hh
  exact hr hh

private def jetTriple (j : ℕ) (δ h a b c : ℝ) (C : ℝ×ℝ→ℂ) (z : ℝ×(ℝ×ℝ)) : ℂ :=
  C z.2*bourgainOscillation (-(z.2.1*b+z.2.2*a+c)/z.1)*
    bagCubicReciprocalHeightAmplitude j δ h z.2 a b z.1

private theorem jet_triple_integrable (j : ℕ)
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (a b c : ℝ) (C : ℝ×ℝ→ℂ) (hC : Continuous C)
    (hCs : ∀z, z∉Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2 → C z=0) :
    Integrable (jetTriple j δ.1 h.1 a b c C) := by
  let K := Icc (1 : ℝ) 2 ×ˢ (Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2)
  have hcc : ContinuousOn (jetTriple j δ.1 h.1 a b c C) K := by
    intro z hz
    have hr : z.1≠0 := (lt_of_lt_of_le zero_lt_one hz.1.1).ne'
    have harg : ContinuousAt (fun w : ℝ×(ℝ×ℝ) => w.2.1*w.2.2/w.1) z :=
      (continuous_snd.fst.continuousAt.mul continuous_snd.snd.continuousAt).div
        continuous_fst.continuousAt hr
    have hnum := (Complex.ofRealCLM.continuous.comp (window_derivatives_smooth j).continuous).continuousAt.comp harg
    have hpow : ContinuousAt (fun w : ℝ×(ℝ×ℝ) => (w.1 : ℂ)^j) z :=
      (Complex.ofRealCLM.continuous.comp continuous_fst).continuousAt.pow j
    have hW : ContinuousAt (fun w : ℝ×(ℝ×ℝ) => bagCubicReciprocalWindowJet j w.2 w.1) z :=
      hnum.div hpow (pow_ne_zero j (Complex.ofReal_ne_zero.mpr hr))
    have hinv (t : ℝ) : ContinuousAt (fun w : ℝ×(ℝ×ℝ) =>
        ((w.1 : ℂ)+Complex.I*(t : ℂ))⁻¹) z :=
      ((Complex.ofRealCLM.continuous.comp continuous_fst).continuousAt.add
        continuousAt_const).inv₀ (denominator_ne t z.1 hr)
    have hF : Continuous (fun w : ℝ×(ℝ×ℝ) => star (bagCubicNormalizedSlice δ.1 h.1 w.1)) :=
      Complex.conjCLE.continuous.comp ((bagCubicNormalizedSlice_properties δ h).1.continuous.comp continuous_fst)
    have hA : ContinuousAt (fun w : ℝ×(ℝ×ℝ) =>
        bagCubicReciprocalHeightAmplitude j δ.1 h.1 w.2 a b w.1) z :=
      (hF.continuousAt.mul hW).mul ((hinv a).mul (hinv b))
    have hl : Continuous (fun w : ℝ×(ℝ×ℝ) => -(w.2.1*b+w.2.2*a+c)) := by fun_prop
    have hE : ContinuousAt (fun w : ℝ×(ℝ×ℝ) =>
        bourgainOscillation (-(w.2.1*b+w.2.2*a+c)/w.1)) z :=
      oscillation_continuous.continuousAt.comp (hl.continuousAt.div continuous_fst.continuousAt hr)
    exact (((hC.comp continuous_snd).continuousAt.mul hE).mul hA).continuousWithinAt
  apply (hcc.integrableOn_compact (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))).integrable_of_forall_notMem_eq_zero
  intro z hz
  by_cases hr : z.1∈Icc (1 : ℝ) 2
  · have hpq : z.2∉Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2 := fun hh => hz ⟨hr,hh⟩
    simp only [jetTriple,hCs z.2 hpq,zero_mul]
  · simp only [jetTriple,bagCubicReciprocalHeightAmplitude,
      (bagCubicNormalizedSlice_properties δ h).2 z.1 hr,star_zero,zero_mul,mul_zero]

private theorem tangent_coefficients_continuous
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) :
    Continuous (fun pq : ℝ×ℝ => tangentCoefficient0 δ.1 h.1 pq.1 pq.2) ∧
    Continuous (fun pq : ℝ×ℝ => tangentCoefficient1 δ.1 h.1 pq.1 pq.2) ∧
    Continuous (fun pq : ℝ×ℝ => tangentCoefficient2 δ.1 h.1 pq.1 pq.2) := by
  have hF := (bagCubicNormalizedSlice_properties δ h).1.continuous
  have hU := (plus_slice_smooth δ h).continuous
  have hP : Continuous (fun pq : ℝ×ℝ => (pq.1 : ℂ)) := Complex.ofRealCLM.continuous.comp continuous_fst
  have hQ : Continuous (fun pq : ℝ×ℝ => (pq.2 : ℂ)) := Complex.ofRealCLM.continuous.comp continuous_snd
  refine ⟨(hU.comp continuous_fst).mul (hU.comp continuous_snd),?_,?_⟩
  · exact (((hP.mul (hU.comp continuous_fst)).mul (hF.comp continuous_snd)).add
      ((hQ.mul (hF.comp continuous_fst)).mul (hU.comp continuous_snd))).add
        ((hF.comp continuous_fst).mul (hF.comp continuous_snd))
  · exact ((hP.mul hQ).mul (hF.comp continuous_fst)).mul (hF.comp continuous_snd)

private theorem tangent_coefficients_off
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (pq : ℝ×ℝ) (hpq : pq∉Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2) :
    tangentCoefficient0 δ.1 h.1 pq.1 pq.2=0 ∧
    tangentCoefficient1 δ.1 h.1 pq.1 pq.2=0 ∧
    tangentCoefficient2 δ.1 h.1 pq.1 pq.2=0 := by
  by_cases hp : pq.1∈Icc (1 : ℝ) 2
  · have hq : pq.2∉Icc (1 : ℝ) 2 := fun hh => hpq ⟨hp,hh⟩
    simp only [tangentCoefficient0,tangentCoefficient1,tangentCoefficient2,
      (bagCubicNormalizedSlice_properties δ h).2 pq.2 hq,plus_slice_off δ h hq,mul_zero,add_zero,and_self]
  · simp only [tangentCoefficient0,tangentCoefficient1,tangentCoefficient2,
      (bagCubicNormalizedSlice_properties δ h).2 pq.1 hp,plus_slice_off δ h hp,
      mul_zero,zero_mul,add_zero,and_self]

private def resolvedStage (δ h a b c r p q : ℝ) : ℂ :=
  bourgainOscillation (-(p*b+q*a+c)/r)*
    (tangentCoefficient0 δ h p q*bagCubicReciprocalHeightAmplitude 0 δ h (p,q) a b r+
      tangentCoefficient1 δ h p q*bagCubicReciprocalHeightAmplitude 1 δ h (p,q) a b r+
      tangentCoefficient2 δ h p q*bagCubicReciprocalHeightAmplitude 2 δ h (p,q) a b r)

private theorem resolved_stage_integrable
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (a b c : ℝ) : Integrable (fun z : ℝ×(ℝ×ℝ) => resolvedStage δ.1 h.1 a b c z.1 z.2.1 z.2.2) := by
  have hc := tangent_coefficients_continuous δ h
  have hs := tangent_coefficients_off δ h
  have h0 := jet_triple_integrable 0 δ h a b c _ hc.1 (fun pq hpq => (hs pq hpq).1)
  have h1 := jet_triple_integrable 1 δ h a b c _ hc.2.1 (fun pq hpq => (hs pq hpq).2.1)
  have h2 := jet_triple_integrable 2 δ h a b c _ hc.2.2 (fun pq hpq => (hs pq hpq).2.2)
  refine ((h0.add h1).add h2).congr (Eventually.of_forall (fun z => ?_))
  simp only [Pi.add_apply,jetTriple,resolvedStage]
  ring

private theorem resolved_stage_swap
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (a b c : ℝ) :
    (∫r : ℝ,∫p : ℝ,∫q : ℝ, resolvedStage δ.1 h.1 a b c r p q)=
      ∫p : ℝ,∫q : ℝ,∫r : ℝ, resolvedStage δ.1 h.1 a b c r p q := by
  have hi := resolved_stage_integrable δ h a b c
  calc (∫r : ℝ,∫p : ℝ,∫q : ℝ, resolvedStage δ.1 h.1 a b c r p q)
      = ∫r : ℝ,∫pq : ℝ×ℝ, resolvedStage δ.1 h.1 a b c r pq.1 pq.2 := by
        apply integral_congr_ae
        filter_upwards [hi.prod_right_ae] with r hr
        exact (integral_prod _ hr).symm
    _ = ∫pq : ℝ×ℝ,∫r : ℝ, resolvedStage δ.1 h.1 a b c r pq.1 pq.2 := integral_integral_swap hi
    _ = _ := integral_prod _ hi.integral_prod_right

private theorem phase_add (x y : ℝ) :
    bourgainOscillation (x+y)=bourgainOscillation x*bourgainOscillation y := by
  unfold bourgainOscillation
  rw [←Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem original_resolved_fiber
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (a b c r : ℝ) :
    (∫q : ℝ,∫p : ℝ,
      bagCubicNormalizedSlice δ.1 h.1 p*bagCubicNormalizedSlice δ.1 h.1 q*
        star (bagCubicNormalizedSlice δ.1 h.1 r)/(r : ℂ)^2*
        (bagPhysicalHeightWindow (p*q/r) : ℂ)*bourgainOscillation (-(p*b+q*a+c)/r))=
      ∫p : ℝ,∫q : ℝ, resolvedStage δ.1 h.1 a b c r p q := by
  by_cases hr : r=0
  · have hzero : bagCubicNormalizedSlice δ.1 h.1 0=0 :=
      (bagCubicNormalizedSlice_properties δ h).2 0 (by simp)
    simp only [hr,Complex.ofReal_zero,pow_two,mul_zero,div_zero,zero_mul,integral_zero,resolvedStage,
      bagCubicReciprocalHeightAmplitude,hzero,star_zero,add_zero]
  let F := bagCubicNormalizedSlice δ.1 h.1
  let A := (r : ℂ)+Complex.I*(a : ℂ)
  let B := (r : ℂ)+Complex.I*(b : ℂ)
  let E := bourgainOscillation (-c/r)
  have hphase (p q : ℝ) : E*(bourgainOscillation (-a*q/r)*bourgainOscillation (-b*p/r))=
      bourgainOscillation (-(p*b+q*a+c)/r) := by
    dsimp only [E]
    rw [←phase_add,←phase_add]
    congr 1
    ring
  have ho : (∫q : ℝ,∫p : ℝ,
      F p*F q*star (F r)/(r : ℂ)^2*(bagPhysicalHeightWindow (p*q/r) : ℂ)*
        bourgainOscillation (-(p*b+q*a+c)/r))=
      (E*star (F r)/(r : ℂ)^2)*(∫q : ℝ,∫p : ℝ, originalStage δ.1 h.1 r a b p q) := by
    simp_rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with q
    apply integral_congr_ae
    filter_upwards [] with p
    rw [←hphase]
    simp only [originalStage,bagCubicReciprocalWindowJet,iteratedDeriv_zero,pow_zero,div_one]
    dsimp only [F]
    ring
  have ht : (∫p : ℝ,∫q : ℝ, resolvedStage δ.1 h.1 a b c r p q)=
      (E*star (F r)*(A⁻¹*B⁻¹))*(∫p : ℝ,∫q : ℝ, tangentStage δ.1 h.1 r a b p q) := by
    simp_rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with p
    apply integral_congr_ae
    filter_upwards [] with q
    change bourgainOscillation (-(p*b+q*a+c)/r)*
      (tangentCoefficient0 δ.1 h.1 p q*(star (F r)*bagCubicReciprocalWindowJet 0 (p,q) r*(A⁻¹*B⁻¹))+
        tangentCoefficient1 δ.1 h.1 p q*(star (F r)*bagCubicReciprocalWindowJet 1 (p,q) r*(A⁻¹*B⁻¹))+
        tangentCoefficient2 δ.1 h.1 p q*(star (F r)*bagCubicReciprocalWindowJet 2 (p,q) r*(A⁻¹*B⁻¹)))=_
    rw [←hphase]
    dsimp only [tangentStage]
    ring
  have hd := double_tangent_identity δ h r a b hr
  have hab : A*B≠0 := mul_ne_zero (denominator_ne a r hr) (denominator_ne b r hr)
  have hj : (∫q : ℝ,∫p : ℝ, originalStage δ.1 h.1 r a b p q)=
      (r : ℂ)^2*(∫p : ℝ,∫q : ℝ, tangentStage δ.1 h.1 r a b p q)/(A*B) := by
    apply (eq_div_iff hab).mpr
    rw [mul_comm]
    exact hd
  rw [ho,ht,hj]
  field_simp [Complex.ofReal_ne_zero.mpr hr,denominator_ne a r hr,denominator_ne b r hr]

private def variationWeight (δ h x : ℝ) : ℝ :=
  ‖bagCubicNormalizedSlice δ h x‖+‖deriv (bagCubicNormalizedSlice δ h) x‖

private theorem coefficient_bounds (δ h : ℝ) (p q : {r : ℝ // r∈Icc (1 : ℝ) 2}) :
    ‖tangentCoefficient0 δ h p.1 q.1‖≤variationWeight δ h p.1*variationWeight δ h q.1 ∧
    ‖tangentCoefficient1 δ h p.1 q.1‖≤5*(variationWeight δ h p.1*variationWeight δ h q.1) ∧
    ‖tangentCoefficient2 δ h p.1 q.1‖≤4*(variationWeight δ h p.1*variationWeight δ h q.1) := by
  have hF (x : ℝ) : ‖bagCubicNormalizedSlice δ h x‖≤variationWeight δ h x :=
    le_add_of_nonneg_right (norm_nonneg _)
  have hU (x : ℝ) : ‖plusSlice δ h x‖≤variationWeight δ h x := norm_add_le _ _
  have hw (x : ℝ) : 0≤variationWeight δ h x := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hwp := hw p.1
  have hwq := hw q.1
  have hp : ‖(p.1 : ℂ)‖≤2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith [p.2.1])]
    exact p.2.2
  have hq : ‖(q.1 : ℂ)‖≤2 := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith [q.2.1])]
    exact q.2.2
  refine ⟨?_,?_,?_⟩
  · dsimp only [tangentCoefficient0]
    rw [norm_mul]
    exact mul_le_mul (hU _) (hU _) (norm_nonneg _) (hw _)
  · calc ‖tangentCoefficient1 δ h p.1 q.1‖
        ≤ ‖(p.1 : ℂ)*plusSlice δ h p.1*bagCubicNormalizedSlice δ h q.1‖+
          ‖(q.1 : ℂ)*bagCubicNormalizedSlice δ h p.1*plusSlice δ h q.1‖+
          ‖bagCubicNormalizedSlice δ h p.1*bagCubicNormalizedSlice δ h q.1‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 2*variationWeight δ h p.1*variationWeight δ h q.1+
          2*variationWeight δ h p.1*variationWeight δ h q.1+
          variationWeight δ h p.1*variationWeight δ h q.1 := by
            simp only [norm_mul]
            gcongr
            all_goals first | positivity | exact hw _ | exact hp | exact hq | exact hF _ | exact hU _
      _ = _ := by ring
  · calc ‖tangentCoefficient2 δ h p.1 q.1‖
        = ‖(p.1 : ℂ)‖*‖(q.1 : ℂ)‖*‖bagCubicNormalizedSlice δ h p.1‖*‖bagCubicNormalizedSlice δ h q.1‖ := by
          simp only [tangentCoefficient2,norm_mul]
      _ ≤ 2*2*variationWeight δ h p.1*variationWeight δ h q.1 := by
        gcongr
        all_goals first | positivity | exact hw _ | exact hp | exact hq | exact hF _
      _ = _ := by ring

private theorem resolved_height_bound :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀a b c p q : ℝ,
      ‖∫r : ℝ, resolvedStage δ.1 h.1 a b c r p q‖≤
        C*(variationWeight δ.1 h.1 p*variationWeight δ.1 h.1 q)/
          ((1+|a|)*(1+|b|)*(1+|p*b+q*a+c|)) := by
  obtain ⟨K0,hK0,h0⟩ := bagCubicReciprocalHeight_uniform_decay 0
  obtain ⟨K1,hK1,h1⟩ := bagCubicReciprocalHeight_uniform_decay 1
  obtain ⟨K2,hK2,h2⟩ := bagCubicReciprocalHeight_uniform_decay 2
  refine ⟨K0+5*K1+4*K2,by positivity,fun δ h a b c p q => ?_⟩
  by_cases hpq : (p,q)∈Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2
  · let d := (1+|a|)*(1+|b|)*(1+|p*b+q*a+c|)
    have hd : 0<d := by dsimp only [d]; positivity
    let C0 := tangentCoefficient0 δ.1 h.1 p q
    let C1 := tangentCoefficient1 δ.1 h.1 p q
    let C2 := tangentCoefficient2 δ.1 h.1 p q
    let I (j : ℕ) := ∫r : ℝ, bourgainOscillation (-(p*b+q*a+c)/r)*
      bagCubicReciprocalHeightAmplitude j δ.1 h.1 (p,q) a b r
    have hi0 := h0 δ h ⟨p,hpq.1⟩ ⟨q,hpq.2⟩ a b (p*b+q*a+c)
    have hi1 := h1 δ h ⟨p,hpq.1⟩ ⟨q,hpq.2⟩ a b (p*b+q*a+c)
    have hi2 := h2 δ h ⟨p,hpq.1⟩ ⟨q,hpq.2⟩ a b (p*b+q*a+c)
    have hs : (∫r : ℝ, resolvedStage δ.1 h.1 a b c r p q)=C0*I 0+C1*I 1+C2*I 2 := by
      calc (∫r : ℝ, resolvedStage δ.1 h.1 a b c r p q)
          = ∫r : ℝ,
            C0*(bourgainOscillation (-(p*b+q*a+c)/r)*bagCubicReciprocalHeightAmplitude 0 δ.1 h.1 (p,q) a b r)+
            C1*(bourgainOscillation (-(p*b+q*a+c)/r)*bagCubicReciprocalHeightAmplitude 1 δ.1 h.1 (p,q) a b r)+
            C2*(bourgainOscillation (-(p*b+q*a+c)/r)*bagCubicReciprocalHeightAmplitude 2 δ.1 h.1 (p,q) a b r) := by
              apply integral_congr_ae
              filter_upwards [] with r
              dsimp only [resolvedStage,C0,C1,C2]
              ring
        _ = _ := by
          have h01 : Integrable (fun r : ℝ =>
              C0*(bourgainOscillation (-(p*b+q*a+c)/r)*bagCubicReciprocalHeightAmplitude 0 δ.1 h.1 (p,q) a b r)+
              C1*(bourgainOscillation (-(p*b+q*a+c)/r)*bagCubicReciprocalHeightAmplitude 1 δ.1 h.1 (p,q) a b r)) :=
            (hi0.1.const_mul C0).add (hi1.1.const_mul C1)
          rw [integral_add h01 (hi2.1.const_mul C2),
            integral_add (hi0.1.const_mul C0) (hi1.1.const_mul C1)]
          simp only [integral_const_mul,I]
    have hc := coefficient_bounds δ.1 h.1 ⟨p,hpq.1⟩ ⟨q,hpq.2⟩
    have hwp : 0≤variationWeight δ.1 h.1 p := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hwq : 0≤variationWeight δ.1 h.1 q := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have ht : ‖C0*I 0+C1*I 1+C2*I 2‖≤‖C0‖*‖I 0‖+‖C1‖*‖I 1‖+‖C2‖*‖I 2‖ := by
      simpa only [norm_mul] using (norm_add_le (C0*I 0+C1*I 1) (C2*I 2)).trans
        (add_le_add (norm_add_le (C0*I 0) (C1*I 1)) le_rfl)
    apply (le_div_iff₀ hd).mpr
    rw [mul_comm,hs]
    calc d*‖C0*I 0+C1*I 1+C2*I 2‖
        ≤ d*(‖C0‖*‖I 0‖+‖C1‖*‖I 1‖+‖C2‖*‖I 2‖) :=
          mul_le_mul_of_nonneg_left ht hd.le
      _ = ‖C0‖*(d*‖I 0‖)+‖C1‖*(d*‖I 1‖)+‖C2‖*(d*‖I 2‖) := by ring
      _ ≤ (variationWeight δ.1 h.1 p*variationWeight δ.1 h.1 q)*K0+
          5*(variationWeight δ.1 h.1 p*variationWeight δ.1 h.1 q)*K1+
          4*(variationWeight δ.1 h.1 p*variationWeight δ.1 h.1 q)*K2 := by
            gcongr
            all_goals first
              | positivity
              | exact hc.1
              | exact hc.2.1
              | exact hc.2.2
              | exact hi0.2
              | exact hi1.2
              | exact hi2.2
      _ = _ := by ring
  · have hz := tangent_coefficients_off δ h (p,q) hpq
    simp only [resolvedStage,hz.1,hz.2.1,hz.2.2,zero_mul,add_zero,mul_zero,integral_zero,norm_zero]
    dsimp only [variationWeight]
    positivity

private theorem variation_weight_properties
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1}) :
    Continuous (variationWeight δ.1 h.1) ∧
      (∀x : ℝ, x∉Icc (1 : ℝ) 2 → variationWeight δ.1 h.1 x=0) := by
  have hF := (bagCubicNormalizedSlice_properties δ h).1
  refine ⟨hF.continuous.norm.add (hF.continuous_deriv (by simp)).norm,?_⟩
  intro x hx
  have hf := (bagCubicNormalizedSlice_properties δ h).2 x hx
  have hu := plus_slice_off δ h hx
  simp only [plusSlice,hf,zero_add] at hu
  simp only [variationWeight,hf,hu,norm_zero,add_zero]

private def coupledMajorant (δ h a b c : ℝ) (pq : ℝ×ℝ) : ℝ :=
  (variationWeight δ h pq.1*variationWeight δ h pq.2)/
    ((1+|a|)*(1+|b|)*(1+|pq.1*b+pq.2*a+c|))

private theorem coupled_majorant_integrable
    (δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)}) (h : {r : ℝ // r∈Icc (0 : ℝ) 1})
    (a b c : ℝ) : Integrable (coupledMajorant δ.1 h.1 a b c) := by
  have hw := variation_weight_properties δ h
  have hn : Continuous (fun pq : ℝ×ℝ => variationWeight δ.1 h.1 pq.1*variationWeight δ.1 h.1 pq.2) :=
    (hw.1.comp continuous_fst).mul (hw.1.comp continuous_snd)
  have hd : Continuous (fun pq : ℝ×ℝ => (1+|a|)*(1+|b|)*(1+|pq.1*b+pq.2*a+c|)) := by fun_prop
  have hc : Continuous (coupledMajorant δ.1 h.1 a b c) :=
    hn.div hd (fun pq => ne_of_gt (by positivity))
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc.prod isCompact_Icc)
  apply Function.support_subset_iff'.mpr
  intro pq hpq
  by_cases hp : pq.1∈Icc (1 : ℝ) 2
  · have hq : pq.2∉Icc (1 : ℝ) 2 := fun hq => hpq ⟨hp,hq⟩
    simp only [coupledMajorant,hw.2 pq.2 hq,mul_zero,zero_div]
  · simp only [coupledMajorant,hw.2 pq.1 hp,zero_mul,zero_div]

/-- Full actual normalized reciprocal kernel, retaining its physical height factor. -/
def bagCubicReciprocalKernel (δ h a b c : ℝ) : ℂ :=
  ∫r : ℝ,∫q : ℝ,∫p : ℝ,
    bagCubicNormalizedSlice δ h p*bagCubicNormalizedSlice δ h q*
      star (bagCubicNormalizedSlice δ h r)/(r : ℂ)^2*
      (bagPhysicalHeightWindow (p*q/r) : ℂ)*bourgainOscillation (-(p*b+q*a+c)/r)

/-- The actual full kernel has a uniform coupled frequency majorant. -/
theorem bagCubicReciprocalKernel_coupled_decay :
    ∃ C : ℝ, 0<C ∧ ∀δ : {r : ℝ // r∈Ioo (0 : ℝ) (1/2)},
      ∀h : {r : ℝ // r∈Icc (0 : ℝ) 1}, ∀a b c : ℝ,
      Integrable (fun pq : ℝ×ℝ =>
        ((‖bagCubicNormalizedSlice δ.1 h.1 pq.1‖+‖deriv (bagCubicNormalizedSlice δ.1 h.1) pq.1‖)*
          (‖bagCubicNormalizedSlice δ.1 h.1 pq.2‖+‖deriv (bagCubicNormalizedSlice δ.1 h.1) pq.2‖))/
          ((1+|a|)*(1+|b|)*(1+|pq.1*b+pq.2*a+c|))) ∧
      ‖bagCubicReciprocalKernel δ.1 h.1 a b c‖≤C*∫pq : ℝ×ℝ,
        ((‖bagCubicNormalizedSlice δ.1 h.1 pq.1‖+‖deriv (bagCubicNormalizedSlice δ.1 h.1) pq.1‖)*
          (‖bagCubicNormalizedSlice δ.1 h.1 pq.2‖+‖deriv (bagCubicNormalizedSlice δ.1 h.1) pq.2‖))/
          ((1+|a|)*(1+|b|)*(1+|pq.1*b+pq.2*a+c|)) := by
  obtain ⟨C,hC,hCb⟩ := resolved_height_bound
  refine ⟨C,hC,fun δ h a b c => ?_⟩
  have hi := resolved_stage_integrable δ h a b c
  have hg := coupled_majorant_integrable δ h a b c
  refine ⟨hg,?_⟩
  have he : bagCubicReciprocalKernel δ.1 h.1 a b c=
      ∫pq : ℝ×ℝ,∫r : ℝ, resolvedStage δ.1 h.1 a b c r pq.1 pq.2 := by
    unfold bagCubicReciprocalKernel
    simp_rw [original_resolved_fiber δ h a b c]
    rw [resolved_stage_swap δ h a b c]
    exact (integral_prod _ hi.integral_prod_right).symm
  rw [he]
  calc ‖∫pq : ℝ×ℝ,∫r : ℝ, resolvedStage δ.1 h.1 a b c r pq.1 pq.2‖
      ≤ ∫pq : ℝ×ℝ, ‖∫r : ℝ, resolvedStage δ.1 h.1 a b c r pq.1 pq.2‖ := norm_integral_le_integral_norm _
    _ ≤ ∫pq : ℝ×ℝ, C*coupledMajorant δ.1 h.1 a b c pq :=
      integral_mono hi.integral_prod_right.norm (hg.const_mul C) (fun pq => by
        simpa only [coupledMajorant,mul_div_assoc] using hCb δ h a b c pq.1 pq.2)
    _ = _ := integral_const_mul _ _

/-- Exact attachment of the coupled kernel to the original controlled physical cone. -/
theorem bagCubicControlledCone_normalized_reciprocal_kernel (N : {r : ℝ // 1<r})
    (H : {r : ℝ // r∈Ioo (0 : ℝ) (N.1/2)}) (a b : ℝ) :
    (((Real.log N.1)^3/N.1 : ℝ) : ℂ)*
      (𝓕 (bagCubicConeSchwartz (bagCubicControlledPhysicalSchwartz N H)))
        (WithLp.toLp 2 ![a,b]) =
      (2*Real.pi : ℂ)*bagCubicReciprocalKernel (H.1/N.1) (1/Real.log N.1)
        (2*Real.pi*a) (2*Real.pi*b) (2*Real.pi*a*b/N.1) := by
  rw [bagCubicControlledCone_normalized_fourier]
  dsimp only [bagCubicReciprocalKernel]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with r
  apply integral_congr_ae
  filter_upwards [] with q
  apply integral_congr_ae
  filter_upwards [] with p
  congr 2
  ring

end RHTower.BAGTrace
