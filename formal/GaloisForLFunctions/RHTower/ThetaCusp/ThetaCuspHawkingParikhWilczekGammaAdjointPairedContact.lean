import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaAdjointLogMoment
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaReciprocalCutoffSource
import GaloisForLFunctions.HTGeometry.LogExpTailIntegral

/-!
# Complete signed source pairing of the retained adjoint contact

Translation retains the whole moving contact layer on a fixed positive ray.
The original two-parameter signed source density has a uniform exponential
majorant. Every contact and loss integral is admitted, and their complete
paired limit is the logarithmic contact. Finite-cutoff gain transposition and
the changing-source mismatch require separate proofs; no operator adjoint,
Xi occurrence or Ward balance is asserted here.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open MeasureTheory Set Filter Topology
noncomputable section

private theorem pwGammaContact_log_bound {a b : ℝ} (ha : 0<a) (hb : 0<b) :
    ‖∫ h in a..b, Real.exp (-h)/h‖ ≤ |Real.log (b/a)| := by
  have hi : ContinuousOn (fun h : ℝ => h) (uIcc a b) := continuousOn_id
  have hn : ∀ h ∈ uIcc a b, h≠0 := fun h hh => ne_of_gt ((lt_min ha hb).trans_le hh.1)
  have hg : IntervalIntegrable (fun h : ℝ => 1/h) volume a b :=
    (continuousOn_const.div hi hn).intervalIntegrable
  rw [← integral_one_div_of_pos ha hb]
  apply intervalIntegral.norm_integral_le_abs_of_norm_le _ hg
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with h hh
  have hh0 : 0<h := (lt_min ha hb).trans hh.1
  rw [Real.norm_of_nonneg (div_pos (Real.exp_pos _) hh0).le]
  exact div_le_div_of_nonneg_right
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hh0.le)) hh0.le

theorem pwGammaAdjointCutoffContact_log_bound {x d : ℝ} (hx : 0<x)
    (hd : 0<d) (hdx : d<x) :
    ‖pwGammaAdjointCutoffContact x d‖ ≤ |Real.log x|+|Real.log (x-d)| := by
  have hr : d/pwGammaAdjointCutoffLower x d = x*(x-d) := by
    unfold pwGammaAdjointCutoffLower
    field_simp
  have ht := pwGammaContact_log_bound (pwGammaAdjointCutoffLower_pos hx hd hdx) hd
  rw [hr, Real.log_mul hx.ne' (sub_pos.mpr hdx).ne'] at ht
  exact ht.trans (abs_add_le _ _)

theorem pwGammaAdjointCutoffContact_shifted_bound {u d : ℝ}
    (hu : 0<u) (hd : 0<d) (hd1 : d≤1) :
    ‖pwGammaAdjointCutoffContact (u+d) d‖ ≤ 2*|Real.log u|+u+1 := by
  have hl : |Real.log (u+d)| ≤ |Real.log u|+u+1 := by
    apply abs_le.mpr
    constructor
    · have hm := Real.strictMonoOn_log.monotoneOn hu (by positivity : 0<u+d)
        (by linarith : u≤u+d)
      linarith [neg_abs_le (Real.log u)]
    · have hm := Real.log_le_self (by positivity : 0≤u+d)
      linarith [abs_nonneg (Real.log u)]
  have ht := pwGammaAdjointCutoffContact_log_bound (by positivity : 0<u+d) hd
    (by linarith : d<u+d)
  rw [add_sub_cancel_right] at ht
  linarith

theorem pwGammaAdjointCutoffContact_shifted_tendsto {u : ℝ} (hu : 0<u) :
    Tendsto (fun d : ℝ => pwGammaAdjointCutoffContact (u+d) d)
      (𝓝[>] (0:ℝ)) (𝓝 (2*Real.log u)) := by
  have hd : Tendsto (fun d : ℝ => d) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hl : Tendsto (fun d : ℝ => pwGammaAdjointCutoffLower (u+d) d)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hh := hd.div ((tendsto_const_nhds.add hd).mul tendsto_const_nhds)
      (by positivity : (u+0)*u≠0)
    simpa only [pwGammaAdjointCutoffLower, add_sub_cancel_right, zero_div, Pi.div_def] using hh
  have he : Tendsto (fun d : ℝ => pwGammaAdjointCutoffContact (u+d) d-
      Real.log ((u+d)*u)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      (by simpa only [sub_zero, abs_zero] using (hd.sub hl).abs)
    filter_upwards [self_mem_nhdsWithin] with d hd0
    have hdpos : 0<d := hd0
    simpa only [add_sub_cancel_right] using pwGammaAdjointCutoffContact_error_bound
      (by positivity : 0<u+d) hd0 (by linarith : d<u+d)
  have hp : Tendsto (fun d : ℝ => (u+d)*u) (𝓝[>] (0:ℝ)) (𝓝 (u*u)) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hd).mul tendsto_const_nhds
  have hlog := (Real.continuousAt_log (mul_ne_zero hu.ne' hu.ne')).tendsto.comp hp
  rw [Real.log_mul hu.ne' hu.ne', ← two_mul] at hlog
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using he.add hlog

private theorem pwGammaContact_integral_measurable (a b : ℝ → ℝ)
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun u => ∫ h in a u..b u, Real.exp (-h)/h) := by
  have h1 : Measurable (fun p : ℝ×ℝ =>
      if a p.1 < p.2 ∧ p.2 ≤ b p.1 then Real.exp (-p.2)/p.2 else 0) := by
    apply Measurable.ite
    · exact (measurableSet_lt (ha.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hb.comp measurable_fst))
    · fun_prop
    · exact measurable_const
  have h2 : Measurable (fun p : ℝ×ℝ =>
      if b p.1 < p.2 ∧ p.2 ≤ a p.1 then Real.exp (-p.2)/p.2 else 0) := by
    apply Measurable.ite
    · exact (measurableSet_lt (hb.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (ha.comp measurable_fst))
    · fun_prop
    · exact measurable_const
  have hm := (h1.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable.sub
    (h2.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert hm using 1
  funext u
  simp only [intervalIntegral]
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
  simp only [Set.indicator, mem_Ioc, Pi.sub_apply]

theorem pwGammaAdjointCutoffContact_shifted_measurable (d : ℝ) :
    Measurable (fun u => pwGammaAdjointCutoffContact (u+d) d) := by
  apply pwGammaContact_integral_measurable
  · unfold pwGammaAdjointCutoffLower
    fun_prop
  · exact measurable_const

private theorem pwGammaContact_log_mul_bound {u : ℝ} (hu : 0<u) :
    u*|Real.log u| ≤ u^2+1 := by
  rw [show u*|Real.log u|=|u*Real.log u| by rw [abs_mul, abs_of_pos hu]]
  apply abs_le.mpr
  constructor
  · have ht := mul_le_mul_of_nonneg_left (Real.neg_inv_le_log hu.le) hu.le
    rw [mul_neg, mul_inv_cancel₀ hu.ne'] at ht
    nlinarith [sq_nonneg u]
  · nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_self hu.le) hu.le]

def pwGammaAdjointContactMajorant (C u : ℝ) : ℝ :=
  C*(Real.exp (-u)*(2*|Real.log u|+3*u^2+2*u+3))

private theorem pwGammaContact_poly_integrable (n : ℕ) :
    IntegrableOn (fun u : ℝ => Real.exp (-u)*u^n) (Ioi 0) := by
  have hi := Real.GammaIntegral_convergent (s := (n:ℝ)+1) (by positivity)
  simpa only [add_sub_cancel_right, Real.rpow_natCast] using hi

theorem pwGammaAdjointContactMajorant_integrable (C : ℝ) :
    IntegrableOn (pwGammaAdjointContactMajorant C) (Ioi 0) := by
  have hl : IntegrableOn (fun u : ℝ => Real.exp (-u)*|Real.log u|) (Ioi 0) := by
    apply Integrable.congr HTGeometry.integrableOn_log_mul_exp_neg_Ioi_zero.norm
    filter_upwards with u
    rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
    ring
  have hi := (((hl.const_mul 2).add ((pwGammaContact_poly_integrable 2).const_mul 3)).add
    ((pwGammaContact_poly_integrable 1).const_mul 2)).add
    ((integrableOn_exp_neg_Ioi 0).const_mul 3)
  apply Integrable.congr (hi.const_mul C)
  filter_upwards with u
  simp only [pwGammaAdjointContactMajorant, Pi.add_apply, pow_one]
  ring

theorem pwGammaAdjointContact_shifted_pair_bound {P : ℝ → ℂ} {C u d : ℝ}
    (hC : 0≤C) (hP : ∀x:ℝ, 0<x → ‖P x‖≤C*x*Real.exp (-x))
    (hu : 0<u) (hd : 0<d) (hd1 : d≤1) :
    ‖P (u+d)*(pwGammaAdjointCutoffContact (u+d) d:ℂ)‖ ≤
      pwGammaAdjointContactMajorant C u := by
  have hx : 0<u+d := by positivity
  have hb : ‖P (u+d)‖ ≤ C*(u+1)*Real.exp (-u) := by
    refine (hP _ hx).trans ?_
    apply mul_le_mul
    · gcongr
    · exact Real.exp_le_exp.mpr (by linarith)
    · positivity
    · positivity
  rw [norm_mul, Complex.norm_real]
  calc
    _ ≤ (C*(u+1)*Real.exp (-u))*(2*|Real.log u|+u+1) :=
      mul_le_mul hb (pwGammaAdjointCutoffContact_shifted_bound hu hd hd1)
        (norm_nonneg _) (by positivity)
    _ ≤ pwGammaAdjointContactMajorant C u := by
      have hl := pwGammaContact_log_mul_bound hu
      unfold pwGammaAdjointContactMajorant
      have hm := mul_le_mul_of_nonneg_left hl (by positivity : 0≤2*C*Real.exp (-u))
      nlinarith

private theorem pwGammaContact_translate (f : ℝ → ℂ) (d : ℝ) :
    (∫ u in Ioi (0:ℝ), f (u+d)) = ∫ x in Ioi d, f x := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_right_eq_self (fun x => (Ioi d).indicator f x) d]
  congr 1
  funext u
  by_cases h : u∈Ioi (0:ℝ)
  · have h' : u+d∈Ioi d := by simp only [mem_Ioi] at h ⊢; linarith
    rw [indicator_of_mem h, indicator_of_mem h']
  · have h' : u+d∉Ioi d := by simp only [mem_Ioi] at h ⊢; linarith
    rw [indicator_of_notMem h, indicator_of_notMem h']

theorem pwGammaAdjointContact_pair_tendsto {P : ℝ → ℂ} {C : ℝ}
    (hPc : ContinuousOn P (Ioi 0)) (hC : 0≤C)
    (hP : ∀x:ℝ, 0<x → ‖P x‖≤C*x*Real.exp (-x)) :
    Tendsto (fun d : ℝ => ∫ x in Ioi d, P x*(pwGammaAdjointCutoffContact x d:ℂ))
      (𝓝[>] (0:ℝ)) (𝓝 (∫ x in Ioi (0:ℝ), P x*(2*Real.log x:ℝ))) := by
  have hd : Tendsto (fun d : ℝ => d) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hm : ∀ᶠ d in 𝓝[>] (0:ℝ), AEStronglyMeasurable
      (fun u => P (u+d)*(pwGammaAdjointCutoffContact (u+d) d:ℂ))
      (volume.restrict (Ioi (0:ℝ))) := by
    filter_upwards [self_mem_nhdsWithin] with d hd0
    have hdpos : 0<d := hd0
    have hc : ContinuousOn (fun u => P (u+d)) (Ioi 0) :=
      hPc.comp (continuousOn_id.add continuousOn_const) (fun u hu => by change 0<u+d; linarith [show 0<u from hu])
    exact (hc.aestronglyMeasurable measurableSet_Ioi).mul
      ((Complex.measurable_ofReal.comp (pwGammaAdjointCutoffContact_shifted_measurable d)).aestronglyMeasurable)
  have hb : ∀ᶠ d in 𝓝[>] (0:ℝ), ∀ᵐ u ∂volume.restrict (Ioi (0:ℝ)),
      ‖P (u+d)*(pwGammaAdjointCutoffContact (u+d) d:ℂ)‖ ≤ pwGammaAdjointContactMajorant C u := by
    filter_upwards [self_mem_nhdsWithin, hd.eventually_lt_const zero_lt_one] with d hd0 hd1
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact pwGammaAdjointContact_shifted_pair_bound hC hP hu hd0 hd1.le
  have hlim : ∀ᵐ u ∂volume.restrict (Ioi (0:ℝ)), Tendsto
      (fun d : ℝ => P (u+d)*(pwGammaAdjointCutoffContact (u+d) d:ℂ))
      (𝓝[>] (0:ℝ)) (𝓝 (P u*(2*Real.log u:ℝ))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0<u := hu
    have hucont := (hPc u hu).continuousAt (Ioi_mem_nhds hu0)
    have hh : Tendsto (fun d : ℝ => u+d) (𝓝[>] (0:ℝ)) (𝓝 u) := by
      simpa only [add_zero] using tendsto_const_nhds.add hd
    exact (hucont.tendsto.comp hh).mul
      ((Complex.continuous_ofReal.tendsto _).comp (pwGammaAdjointCutoffContact_shifted_tendsto hu0))
  have ht := tendsto_integral_filter_of_dominated_convergence
    (pwGammaAdjointContactMajorant C) hm hb (pwGammaAdjointContactMajorant_integrable C) hlim
  apply ht.congr'
  exact Eventually.of_forall (fun d => pwGammaContact_translate
    (fun x => P x*(pwGammaAdjointCutoffContact x d:ℂ)) d)

def pwGammaAdjointEmptyIncomingLoss (P : ℝ → ℂ) (d : ℝ) : ℂ :=
  (∫ x in 0..d, P x)*(∫ h in Ioi d, Real.exp (-h)/h:ℝ)

private theorem pwGammaContact_tail_integrable {d : ℝ} (hd : 0<d) :
    IntegrableOn (fun h : ℝ => Real.exp (-h)/h) (Ioi d) := by
  apply ((integrableOn_exp_neg_Ioi d).div_const d).mono'
    (show Measurable (fun h : ℝ => Real.exp (-h)/h) by fun_prop).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  have hh0 : 0<h := hd.trans hh
  rw [Real.norm_of_nonneg (by positivity : 0≤Real.exp (-h)/h)]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hd hh.le

private theorem pwGammaContact_tail_bound {d : ℝ} (hd : 0<d) :
    ‖∫ h in Ioi d, Real.exp (-h)/h‖ ≤ Real.exp (-d)/d := by
  calc
    _ ≤ ∫ h in Ioi d, Real.exp (-h)/d := by
      apply norm_integral_le_of_norm_le ((integrableOn_exp_neg_Ioi d).div_const d)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
      have hh0 : 0<h := hd.trans hh
      rw [Real.norm_of_nonneg (by positivity : 0≤Real.exp (-h)/h)]
      exact div_le_div_of_nonneg_left (Real.exp_pos _).le hd hh.le
    _ = _ := by rw [integral_div, integral_exp_neg_Ioi]

theorem pwGammaAdjointEmptyIncomingLoss_bound {P : ℝ → ℂ} {C d : ℝ}
    (hC : 0≤C) (hP : ∀x:ℝ, 0<x → ‖P x‖≤C*x*Real.exp (-x)) (hd : 0<d) :
    ‖pwGammaAdjointEmptyIncomingLoss P d‖ ≤ C*d := by
  have hn : ‖∫ x in 0..d, P x‖ ≤ C*d^2 := by
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := P) (a := 0) (b := d) (C := C*d) (by
        intro x hx
        rw [uIoc_of_le hd.le] at hx
        have he := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx.1.le)
        calc
          _ ≤ C*x*Real.exp (-x) := hP x hx.1
          _ ≤ C*d := by nlinarith [mul_nonneg hC hx.1.le, mul_le_mul_of_nonneg_left hx.2 hC])
    simpa only [sub_zero, abs_of_pos hd, pow_two, mul_assoc] using hi
  unfold pwGammaAdjointEmptyIncomingLoss
  rw [norm_mul, Complex.norm_real]
  calc
    _ ≤ (C*d^2)*(Real.exp (-d)/d) :=
      mul_le_mul hn (pwGammaContact_tail_bound hd) (norm_nonneg _) (by positivity)
    _ = C*d*Real.exp (-d) := by field_simp
    _ ≤ C*d := mul_le_of_le_one_right (by positivity)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hd.le))

theorem pwGammaAdjointEmptyIncomingLoss_tendsto {P : ℝ → ℂ} {C : ℝ}
    (hC : 0≤C) (hP : ∀x:ℝ, 0<x → ‖P x‖≤C*x*Real.exp (-x)) :
    Tendsto (pwGammaAdjointEmptyIncomingLoss P) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hd : Tendsto (fun d : ℝ => d) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa only [mul_zero] using hd.const_mul C)
  filter_upwards [self_mem_nhdsWithin] with d hd0
  exact pwGammaAdjointEmptyIncomingLoss_bound hC hP hd0

/-- The actual complete signed arithmetic pair in the reversible density. -/
def pwGammaMobiusReversiblePairDensity (z v : ℂ) (x : ℝ) : ℂ :=
  (pwGammaReversibleDensity x:ℂ)*
    (starRingEnd ℂ) (pwGammaMobiusTilt z x/pwGammaRaySource x)*
    (pwGammaMobiusTilt v x/pwGammaRaySource x)

private theorem pwGammaContact_source_continuousOn :
    ContinuousOn pwGammaRaySource (Ioi 0) := by
  have hc : Continuous (fun x : ℝ => ((Real.sqrt x*Real.exp (-x):ℝ):ℂ)) := by fun_prop
  exact hc.continuousOn.congr (fun x hx => pwGammaRaySource_eq hx)

theorem pwGammaMobiusReversiblePairDensity_continuousOn (z v : ℂ) :
    ContinuousOn (pwGammaMobiusReversiblePairDensity z v) (Ioi 0) := by
  have hm (a : ℂ) : ContinuousOn (pwGammaMobiusTilt a) (Ioi 0) :=
    fun x hx => (pwGammaMobiusTilt_coordinate_hasDerivAt a hx).continuousAt.continuousWithinAt
  have hg (a : ℂ) : ContinuousOn (fun x => pwGammaMobiusTilt a x/pwGammaRaySource x) (Ioi 0) :=
    (hm a).div pwGammaContact_source_continuousOn (fun x _ => pwGammaRaySource_ne_zero x)
  have hw : ContinuousOn pwGammaReversibleDensity (Ioi 0) := by
    unfold pwGammaReversibleDensity
    fun_prop (disch := aesop)
  exact ((Complex.continuous_ofReal.comp_continuousOn hw).mul
    (Complex.continuous_conj.comp_continuousOn (hg z))).mul (hg v)

private theorem pwGammaContact_inverse_power_density_bound (k : ℕ) {x : ℝ} (hx : 0<x) :
    pwGammaReversibleDensity x/x^k ≤ ((k+2).factorial:ℝ)*x*Real.exp (-x) := by
  have hp := Real.pow_div_factorial_le_exp x⁻¹ (inv_pos.mpr hx).le (k+2)
  have hf : (0:ℝ)<(k+2).factorial := by positivity
  have hb : (x⁻¹)^(k+2)*Real.exp (-x⁻¹) ≤ ((k+2).factorial:ℝ) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    exact (div_le_iff₀ (Real.exp_pos _)).mpr
      (by simpa only [mul_comm] using (div_le_iff₀ hf).mp hp)
  calc
    _ = (x*Real.exp (-x))*((x⁻¹)^(k+2)*Real.exp (-x⁻¹)) := by
      unfold pwGammaReversibleDensity
      rw [sub_eq_add_neg, Real.exp_add, pow_add, inv_pow]
      field_simp
    _ ≤ (x*Real.exp (-x))*((k+2).factorial:ℝ) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

private theorem pwGammaContact_normalized_source_bound (z : ℂ) :
    ∃p:ℕ, ∃C:ℝ, 0≤C ∧ ∀x:ℝ, 0<x →
      ‖pwGammaMobiusTilt z x/pwGammaRaySource x‖≤1+C/x^p := by
  obtain ⟨p,C,hC,hb⟩ := pwGammaMobiusReciprocalTail_polynomial_bound z
  refine ⟨p,C,hC,fun x hx => ?_⟩
  have ht := hb (1/x) (by positivity)
  have he : pwGammaMobiusTilt z x/pwGammaRaySource x = pwGammaMobiusReciprocalTail z (1/x)+1 := by
    simp only [pwGammaMobiusReciprocalTail, one_div, inv_inv, sub_add_cancel]
  rw [he]
  calc
    _ ≤ ‖pwGammaMobiusReciprocalTail z (1/x)‖+‖(1:ℂ)‖ := norm_add_le _ _
    _ ≤ C*(1/x)^p+1 := add_le_add ht (by simp)
    _ = _ := by rw [div_pow, one_pow]; ring

theorem pwGammaMobiusReversiblePairDensity_bound (z v : ℂ) :
    ∃C:ℝ, 0≤C ∧ ∀x:ℝ, 0<x →
      ‖pwGammaMobiusReversiblePairDensity z v x‖≤C*x*Real.exp (-x) := by
  obtain ⟨p,A,hA,ha⟩ := pwGammaContact_normalized_source_bound z
  obtain ⟨q,B,hB,hb⟩ := pwGammaContact_normalized_source_bound v
  refine ⟨((2:ℕ).factorial:ℝ)+A*((p+2).factorial:ℝ)+B*((q+2).factorial:ℝ)+
    A*B*((p+q+2).factorial:ℝ), by positivity, fun x hx => ?_⟩
  have hw := (pwGammaReversibleDensity_pos hx).le
  unfold pwGammaMobiusReversiblePairDensity
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw, Complex.norm_conj]
  calc
    _ ≤ pwGammaReversibleDensity x*(1+A/x^p)*(1+B/x^q) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (ha x hx) hw) (hb x hx)
        (norm_nonneg _) (by positivity)
    _ = pwGammaReversibleDensity x/x^0+A*(pwGammaReversibleDensity x/x^p)+
        B*(pwGammaReversibleDensity x/x^q)+A*B*(pwGammaReversibleDensity x/x^(p+q)) := by
      rw [pow_zero, pow_add]
      field_simp
      ring
    _ ≤ ((2:ℕ).factorial:ℝ)*x*Real.exp (-x)+
        A*(((p+2).factorial:ℝ)*x*Real.exp (-x))+
        B*(((q+2).factorial:ℝ)*x*Real.exp (-x))+
        A*B*(((p+q+2).factorial:ℝ)*x*Real.exp (-x)) := by
      apply add_le_add
      · apply add_le_add
        · exact add_le_add (pwGammaContact_inverse_power_density_bound 0 hx)
            (mul_le_mul_of_nonneg_left (pwGammaContact_inverse_power_density_bound p hx) hA)
        · exact mul_le_mul_of_nonneg_left (pwGammaContact_inverse_power_density_bound q hx) hB
      · exact mul_le_mul_of_nonneg_left (pwGammaContact_inverse_power_density_bound (p+q) hx)
          (mul_nonneg hA hB)
    _ = _ := by ring

theorem pwGammaMobiusReversiblePairDensity_integrable (z v : ℂ) :
    IntegrableOn (pwGammaMobiusReversiblePairDensity z v) (Ioi 0) := by
  obtain ⟨C,hC,hb⟩ := pwGammaMobiusReversiblePairDensity_bound z v
  apply ((pwGammaContact_poly_integrable 1).const_mul C).mono'
    ((pwGammaMobiusReversiblePairDensity_continuousOn z v).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [pow_one, mul_assoc, mul_comm, mul_left_comm] using hb x hx

private theorem pwGammaContact_translate_integrable (f : ℝ → ℂ) (d : ℝ)
    (hi : IntegrableOn (fun u => f (u+d)) (Ioi 0)) : IntegrableOn f (Ioi d) := by
  apply (integrable_indicator_iff measurableSet_Ioi).mp
  have ht := (hi.integrable_indicator measurableSet_Ioi).comp_add_right (-d)
  apply ht.congr
  filter_upwards with x
  by_cases hx : d<x
  · have hx' : x+(-d)∈Ioi (0:ℝ) := by change 0<x+(-d); linarith
    rw [indicator_of_mem hx', indicator_of_mem (show x∈Ioi d from hx)]
    congr 1
    ring
  · have hx' : x+(-d)∉Ioi (0:ℝ) := by change ¬0<x+(-d); linarith
    rw [indicator_of_notMem hx', indicator_of_notMem (show x∉Ioi d from hx)]

private theorem pwGammaContact_pair_integrable {P : ℝ → ℂ} {C d : ℝ}
    (hPc : ContinuousOn P (Ioi 0)) (hC : 0≤C)
    (hP : ∀x:ℝ, 0<x → ‖P x‖≤C*x*Real.exp (-x)) (hd : 0<d) (hd1 : d≤1) :
    IntegrableOn (fun x => P x*(pwGammaAdjointCutoffContact x d:ℂ)) (Ioi d) := by
  apply pwGammaContact_translate_integrable
  have hc : ContinuousOn (fun u => P (u+d)) (Ioi 0) :=
    hPc.comp (continuousOn_id.add continuousOn_const)
      (fun u hu => by change 0<u+d; linarith [show 0<u from hu])
  apply (pwGammaAdjointContactMajorant_integrable C).mono'
    ((hc.aestronglyMeasurable measurableSet_Ioi).mul
      ((Complex.measurable_ofReal.comp (pwGammaAdjointCutoffContact_shifted_measurable d)).aestronglyMeasurable))
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact pwGammaAdjointContact_shifted_pair_bound hC hP hu hd hd1

private theorem pwGammaContact_log_pair_integrable {P : ℝ → ℂ} {C : ℝ}
    (hPc : ContinuousOn P (Ioi 0)) (hC : 0≤C)
    (hP : ∀x:ℝ, 0<x → ‖P x‖≤C*x*Real.exp (-x)) :
    IntegrableOn (fun x => P x*(2*Real.log x:ℝ)) (Ioi 0) := by
  have hc : ContinuousOn (fun x : ℝ => (2*Real.log x:ℝ)) (Ioi 0) := by fun_prop (disch := aesop)
  have hm := hPc.mul (Complex.continuous_ofReal.comp_continuousOn hc)
  apply (((pwGammaContact_poly_integrable 2).add (integrableOn_exp_neg_Ioi 0)).const_mul (2*C)).mono'
    (hm.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0<x := hx
  change ‖P x*((2*Real.log x:ℝ):ℂ)‖≤2*C*(Real.exp (-x)*x^2+Real.exp (-x))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0:ℝ)<2)]
  have hp := mul_le_mul_of_nonneg_right (hP x hx0) (by positivity : 0≤2*|Real.log x|)
  have hl := mul_le_mul_of_nonneg_left (pwGammaContact_log_mul_bound hx0)
    (by positivity : 0≤2*C*Real.exp (-x))
  nlinarith

/-- Every original integral in the retained complete-source contact passage is admitted. -/
theorem pwGammaMobiusReversiblePairDensity_contact_admission (z v : ℂ) {d : ℝ}
    (hd : 0<d) (hd1 : d≤1) :
    IntegrableOn (fun x => pwGammaMobiusReversiblePairDensity z v x*
      (pwGammaAdjointCutoffContact x d:ℂ)) (Ioi d) ∧
    IntervalIntegrable (pwGammaMobiusReversiblePairDensity z v) volume 0 d ∧
    IntegrableOn (fun h : ℝ => Real.exp (-h)/h) (Ioi d) ∧
    IntegrableOn (fun x => pwGammaMobiusReversiblePairDensity z v x*(2*Real.log x:ℝ)) (Ioi 0) := by
  obtain ⟨C,hC,hb⟩ := pwGammaMobiusReversiblePairDensity_bound z v
  have hc := pwGammaMobiusReversiblePairDensity_continuousOn z v
  refine ⟨pwGammaContact_pair_integrable hc hC hb hd hd1, ?_,
    pwGammaContact_tail_integrable hd, pwGammaContact_log_pair_integrable hc hC hb⟩
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hd.le]
  exact (pwGammaMobiusReversiblePairDensity_integrable z v).mono_set (fun x hx => hx.1)

theorem pwGammaMobiusReversiblePairDensity_original_contact_tendsto (z v : ℂ) :
    Tendsto (fun d : ℝ =>
      (∫ x in Ioi d, pwGammaMobiusReversiblePairDensity z v x*
        (pwGammaAdjointCutoffContact x d:ℂ))-
      pwGammaAdjointEmptyIncomingLoss (pwGammaMobiusReversiblePairDensity z v) d)
      (𝓝[>] (0:ℝ))
      (𝓝 (∫ x in Ioi (0:ℝ), pwGammaMobiusReversiblePairDensity z v x*(2*Real.log x:ℝ))) := by
  obtain ⟨C,hC,hb⟩ := pwGammaMobiusReversiblePairDensity_bound z v
  simpa only [sub_zero] using
    (pwGammaAdjointContact_pair_tendsto (pwGammaMobiusReversiblePairDensity_continuousOn z v) hC hb).sub
    (pwGammaAdjointEmptyIncomingLoss_tendsto hC hb)

end
end RHTower
