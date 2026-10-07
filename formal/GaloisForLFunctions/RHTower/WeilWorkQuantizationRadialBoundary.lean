import GaloisForLFunctions.RHTower.WeilWorkQuantizationEndpointPhase
import GaloisForLFunctions.HTGeometry.RightHalfPlanePrimitive
import Mathlib.Topology.Order.Monotone

/-!
# Radial boundary values of the canonical exponential

Normalize a primitive `P` of the actual Weil continuation by `P(2) = 0`.
Endpoint-inclusive Poisson inversion gives a finite radial limit of `Im P` at
every height. Positivity makes `exp (Re P)` monotone in the horizontal direction,
so `exp P` has a radial limit everywhere. The trace is measurable and respects
complex conjugation, including at zero boundary values.

No continuity on the critical edge or quantization of its measure is asserted.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ENNReal ComplexConjugate

noncomputable section
namespace RHTower.WeilSpectral

/-- The canonical Herglotz primitive, normalized to vanish at `2`. -/
def quantizationLogPrimitive {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) : ℂ → ℂ :=
  Classical.choose ((GaloisForLFunctions.HTGeometry.isExactOn_rightHalfPlane
    (differentiableOn_weilContinuation hW)).with_val_at 2 0)

theorem quantizationLogPrimitive_two {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    quantizationLogPrimitive hW 2 = 0 :=
  (Classical.choose_spec ((GaloisForLFunctions.HTGeometry.isExactOn_rightHalfPlane
    (differentiableOn_weilContinuation hW)).with_val_at 2 0)).1

theorem hasDerivAt_quantizationLogPrimitive {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    HasDerivAt (quantizationLogPrimitive hW) (weilContinuation hW s) s :=
  (Classical.choose_spec ((GaloisForLFunctions.HTGeometry.isExactOn_rightHalfPlane
    (differentiableOn_weilContinuation hW)).with_val_at 2 0)).2 s hs

theorem im_quantizationLogPrimitive_real {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {σ : ℝ} (hσ : 1 / 2 < σ) : (quantizationLogPrimitive hW σ).im = 0 := by
  have hd : ∀ x ∈ Ioi (1 / 2 : ℝ),
      HasDerivAt (fun x : ℝ => (quantizationLogPrimitive hW x).im) 0 x := by
    intro x hx
    have hc := congrArg Complex.im (weilContinuation_conj hW (s := (x : ℂ)) hx)
    have hi : (weilContinuation hW x).im = 0 := by
      simp only [Complex.conj_ofReal, Complex.conj_im] at hc
      linarith
    have hp := (hasDerivAt_quantizationLogPrimitive hW (s := (x : ℂ)) hx).comp_ofReal
    exact (Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hp).congr_deriv hi
  have heq := isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (1 / 2 : ℝ)).isPreconnected
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hd x hx).deriv) hσ (by norm_num : (2 : ℝ) ∈ Ioi (1 / 2 : ℝ))
  simpa [quantizationLogPrimitive_two] using heq

theorem hasDerivAt_im_quantizationLogPrimitive_vertical {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => (quantizationLogPrimitive hW ((σ : ℂ) + t * I)).im)
      (weilContinuation hW ((σ : ℂ) + t * I)).re t := by
  have hv : HasDerivAt (fun t : ℝ => (σ : ℂ) + t * I) I t := by
    simpa using (((hasDerivAt_id t).ofReal_comp).mul_const I).const_add (σ : ℂ)
  have hp := (hasDerivAt_quantizationLogPrimitive hW (s := (σ : ℂ) + t * I)
    (by simpa using hσ)).comp t hv
  refine (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hp).congr_deriv ?_
  simp

theorem integral_re_weilContinuation_eq_phase_sub {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1 / 2 < σ) (a b : ℝ) :
    ∫ t in a..b, (weilContinuation hW ((σ : ℂ) + t * I)).re =
      (quantizationLogPrimitive hW ((σ : ℂ) + b * I)).im -
        (quantizationLogPrimitive hW ((σ : ℂ) + a * I)).im := by
  have hc : Continuous fun t : ℝ => (weilContinuation hW ((σ : ℂ) + t * I)).re := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hd := (differentiableOn_weilContinuation hW).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simpa using hσ :
        (σ : ℂ) + t * I ∈ {s : ℂ | 1 / 2 < s.re}))
    exact Complex.continuous_re.continuousAt.comp
      (hd.continuousAt.comp (f := fun t : ℝ => (σ : ℂ) + t * I) (by fun_prop))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_im_quantizationLogPrimitive_vertical hW hσ t)
    (hc.intervalIntegrable a b)

/-- The imaginary part has a finite radial limit at every height, including atoms. -/
theorem exists_tendsto_im_quantizationLogPrimitive {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (t : ℝ) :
    ∃ θ : ℝ, Tendsto (fun η : ℝ =>
      (quantizationLogPrimitive hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).im)
      (𝓝[>] 0) (𝓝 θ) := by
  rcases lt_trichotomy 0 t with ht | ht | ht
  · refine ⟨_, (tendsto_re_weilContinuation_interval_endpoints hW ht).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
    rw [← intervalIntegral.integral_of_le ht.le,
      integral_re_weilContinuation_eq_phase_sub hW (by linarith)]
    simp only [Complex.ofReal_zero, zero_mul, add_zero,
      im_quantizationLogPrimitive_real hW (by linarith : 1 / 2 < 1 / 2 + η), sub_zero]
  · subst t
    refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
    simp only [Complex.ofReal_zero, zero_mul, add_zero,
      im_quantizationLogPrimitive_real hW (by linarith : 1 / 2 < 1 / 2 + η)]
  · refine ⟨_, (tendsto_re_weilContinuation_interval_endpoints hW ht).neg.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
    rw [← intervalIntegral.integral_of_le ht.le,
      integral_re_weilContinuation_eq_phase_sub hW (by linarith)]
    simp only [Complex.ofReal_zero, zero_mul, add_zero,
      im_quantizationLogPrimitive_real hW (by linarith : 1 / 2 < 1 / 2 + η), zero_sub, neg_neg]

/-- Positivity of the real logarithmic derivative makes the modulus monotone. -/
theorem monotoneOn_exp_re_quantizationLogPrimitive {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (t : ℝ) :
    MonotoneOn (fun η : ℝ => Real.exp
      (quantizationLogPrimitive hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re) (Ioi 0) := by
  have hd : ∀ η ∈ Ioi (0 : ℝ), HasDerivAt
      (fun η : ℝ => Real.exp (quantizationLogPrimitive hW
        (((1 / 2 + η : ℝ) : ℂ) + t * I)).re)
      (Real.exp (quantizationLogPrimitive hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re *
        (weilContinuation hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re) η := by
    intro η hη
    have hη' : 0 < η := hη
    have hv : HasDerivAt (fun η : ℝ => (((1 / 2 + η : ℝ) : ℂ) + t * I)) 1 η := by
      simpa using (((hasDerivAt_id η).const_add (1 / 2)).ofReal_comp).add_const ((t : ℂ) * I)
    have hp := (hasDerivAt_quantizationLogPrimitive hW
      (s := (((1 / 2 + η : ℝ) : ℂ) + t * I)) (by simp; linarith)).comp η hv
    refine (Complex.reCLM.hasFDerivAt.comp_hasDerivAt η hp).exp.congr_deriv ?_
    simp
  apply monotoneOn_of_deriv_nonneg (convex_Ioi (0 : ℝ))
  · exact fun η hη => (hd η hη).continuousAt.continuousWithinAt
  · intro η hη
    exact (hd η (by simpa only [interior_Ioi] using hη)).differentiableAt.differentiableWithinAt
  · intro η hη
    rw [(hd η (by simpa only [interior_Ioi] using hη)).deriv]
    exact mul_nonneg (Real.exp_pos _).le
      (re_weilContinuation_nonneg hW (by simp; simpa only [interior_Ioi, mem_Ioi] using hη))

/-- The canonical exponential has a radial trace everywhere. No continuity at the edge is assumed. -/
theorem exists_tendsto_exp_quantizationLogPrimitive {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) (t : ℝ) :
    ∃ g : ℂ, Tendsto (fun η : ℝ =>
      Complex.exp (quantizationLogPrimitive hW (((1 / 2 + η : ℝ) : ℂ) + t * I)))
      (𝓝[>] 0) (𝓝 g) := by
  obtain ⟨θ, hθ⟩ := exists_tendsto_im_quantizationLogPrimitive hW t
  let f : ℝ → ℝ := fun η => Real.exp
    (quantizationLogPrimitive hW (((1 / 2 + η : ℝ) : ℂ) + t * I)).re
  have hb : BddBelow (f '' Ioi 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨η, _, rfl⟩
    exact (Real.exp_pos _).le
  have hm := (monotoneOn_exp_re_quantizationLogPrimitive hW t).tendsto_nhdsGT hb
  have hp := Complex.continuous_exp.tendsto ((θ : ℂ) * I) |>.comp
    (((Complex.continuous_ofReal.tendsto θ).comp hθ).mul_const I)
  refine ⟨((sInf (f '' Ioi (0 : ℝ)) : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * I), ?_⟩
  have h := ((Complex.continuous_ofReal.tendsto _).comp hm).mul hp
  simpa only [Function.comp_def, Complex.ofReal_exp, ← Complex.exp_add,
    Complex.re_add_im, f] using h

/-- Values approached from the open half-plane, including possible zero limits. -/
def quantizationBoundaryTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) : ℂ :=
  Classical.choose (exists_tendsto_exp_quantizationLogPrimitive hW t)

theorem tendsto_quantizationBoundaryTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    Tendsto (fun η : ℝ =>
      Complex.exp (quantizationLogPrimitive hW (((1 / 2 + η : ℝ) : ℂ) + t * I)))
      (𝓝[>] 0) (𝓝 (quantizationBoundaryTrace hW t)) :=
  Classical.choose_spec (exists_tendsto_exp_quantizationLogPrimitive hW t)

theorem continuous_exp_quantizationLogPrimitive_vertical {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Continuous fun t : ℝ => Complex.exp (quantizationLogPrimitive hW ((σ : ℂ) + t * I)) := by
  apply Complex.continuous_exp.comp
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (hasDerivAt_quantizationLogPrimitive hW (s := (σ : ℂ) + t * I)
    (by simpa using hσ)).continuousAt.comp
      (f := fun t : ℝ => (σ : ℂ) + t * I) (by fun_prop)

/-- The canonical radial trace is measurable, without asserting continuity. -/
theorem measurable_quantizationBoundaryTrace {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Measurable (quantizationBoundaryTrace hW) := by
  have hε : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [mem_Ioi]; positivity⟩
  apply measurable_of_tendsto_metrizable
    (f := fun n : ℕ => fun t : ℝ => Complex.exp (quantizationLogPrimitive hW
      (((1 / 2 + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) + t * I)))
  · intro n
    exact (continuous_exp_quantizationLogPrimitive_vertical hW (by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)).measurable
  · exact tendsto_pi_nhds.mpr fun t => (tendsto_quantizationBoundaryTrace hW t).comp hε

theorem quantizationLogPrimitive_conj {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {s : ℂ} (hs : 1 / 2 < s.re) :
    quantizationLogPrimitive hW (conj s) = conj (quantizationLogPrimitive hW s) := by
  let q : ℂ → ℂ := fun z => quantizationLogPrimitive hW z -
    conj (quantizationLogPrimitive hW (conj z))
  have hd : ∀ z ∈ {z : ℂ | 1 / 2 < z.re}, HasDerivAt q 0 z := by
    intro z hz
    have hp := (hasDerivAt_quantizationLogPrimitive hW (s := conj z)
      (by simpa using hz)).conj_conj
    have hp' : HasDerivAt (fun w => conj (quantizationLogPrimitive hW (conj w)))
        (weilContinuation hW z) z := by
      simpa only [Function.comp_def, weilContinuation_conj hW hz, Complex.conj_conj] using hp
    exact ((hasDerivAt_quantizationLogPrimitive hW hz).sub hp').congr_deriv (sub_self _)
  have heq := (isOpen_lt continuous_const Complex.continuous_re).is_const_of_deriv_eq_zero
    (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected
    (fun z hz => (hd z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hd z hz).deriv) hs (by norm_num : (1 / 2 : ℝ) < (2 : ℂ).re)
  have h : quantizationLogPrimitive hW s = conj (quantizationLogPrimitive hW (conj s)) :=
    sub_eq_zero.mp (by simpa [q, Complex.conj_ofNat, quantizationLogPrimitive_two] using heq)
  simpa only [Complex.conj_conj] using (congrArg conj h).symm

/-- Reflection survives radial limits, including zeros of the boundary trace. -/
theorem quantizationBoundaryTrace_neg {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    quantizationBoundaryTrace hW (-t) = conj (quantizationBoundaryTrace hW t) := by
  have hc := Complex.continuous_conj.tendsto _ |>.comp (tendsto_quantizationBoundaryTrace hW t)
  apply tendsto_nhds_unique (tendsto_quantizationBoundaryTrace hW (-t))
  refine hc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with η (hη : 0 < η)
  simp only [Function.comp_apply]
  rw [← Complex.exp_conj, ← quantizationLogPrimitive_conj hW (by simp; linarith)]
  congr 2
  simp [Complex.conj_ofNat]

end RHTower.WeilSpectral
