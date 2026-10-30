import GaloisForLFunctions.CompletedArithmeticForms.BesselSpectralBand

/-!
# An argument-derivative reserve for the physical Schläfli source

Comparison with the decaying barrier `exp(-x)/x` bounds the negative argument
derivative of the actual imaginary-order Bessel function on its nonoscillatory
band. The bound pays the signed Bessel combination of a reflected theta atom.
-/

noncomputable section

open Complex Set Filter Topology

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry

/-- The literal Schläfli function vanishes at large argument for every fixed order. -/
theorem tendsto_modifiedBesselKOrder_arg_zero (ν : ℂ) :
    Tendsto (fun x : ℝ => modifiedBesselKOrder x ν) atTop (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ => Real.exp (1 - x) * besselOrderUnitMass ν)
      atTop (𝓝 0) := by
    simp_rw [Real.exp_sub]
    simpa only [div_eq_mul_inv, ← Real.exp_neg, zero_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (Real.exp 1)).mul_const
        (besselOrderUnitMass ν)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact norm_modifiedBesselKOrder_le_exp hx ν

/-- Wronskian against `exp(-x)/x`, expressed through the literal argument system. -/
def besselBarrierFlux (ν : ℂ) (x : ℝ) : ℂ :=
  (Real.exp (-x) : ℂ) *
    ((1 + (ν + 1) / x) * modifiedBesselKOrder x ν - modifiedBesselKOrder x (ν + 1))

theorem besselBarrierFlux_eq (ν : ℂ) (x : ℝ) :
    besselBarrierFlux ν x = (Real.exp (-x) : ℂ) *
      (besselArgDeriv ν x + (1 + 1 / (x : ℂ)) * modifiedBesselKOrder x ν) := by
  unfold besselBarrierFlux besselArgDeriv
  congr 1
  rw [add_div]
  ring

/-- Exact barrier flux derivative, with every order and inverse-argument term retained. -/
theorem hasDerivAt_besselBarrierFlux {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    HasDerivAt (besselBarrierFlux ν)
      (-(Real.exp (-x) : ℂ) * (1 / (x : ℂ) + (1 - ν ^ 2) / (x : ℂ) ^ 2) *
        modifiedBesselKOrder x ν) x := by
  have hf := hasDerivAt_modifiedBesselKOrder_arg hx ν
  have hg := hasDerivAt_modifiedBesselKOrder_arg_succ hx ν
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have hcoef := ((hasDerivAt_const x (ν + 1)).div hid hxC).const_add 1
  have hexp := ((hasDerivAt_id x).neg.exp).ofReal_comp
  have h : HasDerivAt (besselBarrierFlux ν) _ x := hexp.mul ((hcoef.mul hf).sub hg)
  refine h.congr_deriv ?_
  push_cast
  field_simp [hxC]
  ring

/-- No asymptotic premise is needed for the barrier flux at infinity. -/
theorem tendsto_besselBarrierFlux_zero (ν : ℂ) :
    Tendsto (besselBarrierFlux ν) atTop (𝓝 0) := by
  have hinv : Tendsto (fun x : ℝ => ((x : ℂ))⁻¹) atTop (𝓝 0) := by
    have h := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
    simpa only [Complex.ofReal_inv, Complex.ofReal_zero] using h
  have he : Tendsto (fun x : ℝ => (Real.exp (-x) : ℂ)) atTop (𝓝 0) := by
    simpa only [Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        Real.tendsto_exp_neg_atTop_nhds_zero
  have hc : Tendsto (fun x : ℝ => 1 + (ν + 1) / (x : ℂ)) atTop (𝓝 1) := by
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using
      tendsto_const_nhds.add (hinv.const_mul (ν + 1))
  have h := he.mul ((hc.mul (tendsto_modifiedBesselKOrder_arg_zero ν)).sub
    (tendsto_modifiedBesselKOrder_arg_zero (ν + 1)))
  simpa only [besselBarrierFlux, mul_zero, sub_zero] using h

/-- The imaginary-order barrier derivative is a negative real multiple of the source itself. -/
theorem hasDerivAt_besselBarrierFlux_real {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    HasDerivAt (fun y : ℝ => (besselBarrierFlux ((τ : ℂ) * I) y).re)
      (-Real.exp (-x) * (1 / x + (1 + τ ^ 2) / x ^ 2) *
        (modifiedBesselKOrder x ((τ : ℂ) * I)).re) x := by
  have hν : ((τ : ℂ) * I) ^ 2 = -((τ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_besselBarrierFlux hx ((τ : ℂ) * I))
  change HasDerivAt (fun y : ℝ => (besselBarrierFlux ((τ : ℂ) * I) y).re)
    (-(Real.exp (-x) : ℂ) * (1 / (x : ℂ) +
      (1 - ((τ : ℂ) * I) ^ 2) / (x : ℂ) ^ 2) * modifiedBesselKOrder x ((τ : ℂ) * I)).re x at h
  rw [hν] at h
  have he : -(Real.exp (-x) : ℂ) * (1 / (x : ℂ) +
      (1 - -((τ ^ 2 : ℝ) : ℂ)) / (x : ℂ) ^ 2) =
        ((-Real.exp (-x) * (1 / x + (1 + τ ^ 2) / x ^ 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he] at h
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using h

/-- Decay and the source sign force a nonnegative barrier flux throughout the band. -/
theorem besselBarrierFlux_re_nonneg_on_band {a τ : ℝ} (ha : 0 < a) (hτ : |τ| ≤ a) :
    0 ≤ (besselBarrierFlux ((τ : ℂ) * I) a).re := by
  let ν : ℂ := (τ : ℂ) * I
  have hm : MonotoneOn (fun x : ℝ => -(besselBarrierFlux ν x).re) (Ici a) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
      (f' := fun x => Real.exp (-x) * (1 / x + (1 + τ ^ 2) / x ^ 2) *
        (modifiedBesselKOrder x ν).re) ?_ ?_ ?_
    · intro x hx
      exact (hasDerivAt_besselBarrierFlux_real (ha.trans_le hx) τ).neg.continuousAt.continuousWithinAt
    · intro x hx
      have hx0 : 0 < x := ha.trans_le (interior_subset hx)
      convert (hasDerivAt_besselBarrierFlux_real hx0 τ).neg.hasDerivWithinAt using 1 <;> ring
    · intro x hx
      have hx0 : 0 < x := ha.trans_le (interior_subset hx)
      have hf := modifiedBesselKOrder_re_pos_on_band hx0 (hτ.trans (interior_subset hx))
      have hc : 0 ≤ 1 / x + (1 + τ ^ 2) / x ^ 2 := by positivity
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le hc) hf.le
  have hlim : Tendsto (fun x : ℝ => (besselBarrierFlux ν x).re) atTop (𝓝 0) := by
    simpa only [Complex.zero_re] using Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_besselBarrierFlux_zero ν)
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop a] with x hx
  have h := hm (show a ∈ Ici a from le_rfl) hx hx
  linarith only [h]

/-- The negative argument derivative costs at most `1 + 1/a` times the positive band density. -/
theorem besselArgDeriv_re_lower_on_band {a τ : ℝ} (ha : 0 < a) (hτ : |τ| ≤ a) :
    -(1 + 1 / a) * (modifiedBesselKOrder a ((τ : ℂ) * I)).re ≤
      (besselArgDeriv ((τ : ℂ) * I) a).re := by
  have h := besselBarrierFlux_re_nonneg_on_band ha hτ
  rw [besselBarrierFlux_eq] at h
  have he : (1 + 1 / (a : ℂ)) = ((1 + 1 / a : ℝ) : ℂ) := by push_cast; rfl
  rw [he] at h
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
    zero_mul, sub_zero] at h
  have h' := (mul_nonneg_iff_of_pos_left (Real.exp_pos (-a))).mp h
  linarith only [h']

/-- The complete signed radial Bessel combination retains an explicit positive density reserve. -/
theorem besselSignedRadialCombination_lower {a τ : ℝ} (ha : 0 < a) (hτ : |τ| ≤ a) :
    (a ^ 2 - 6 * a + 3) * (modifiedBesselKOrder a ((τ : ℂ) * I)).re ≤
      (a ^ 2 + 9) * (modifiedBesselKOrder a ((τ : ℂ) * I)).re +
        6 * a * (besselArgDeriv ((τ : ℂ) * I) a).re := by
  have h := mul_le_mul_of_nonneg_left (besselArgDeriv_re_lower_on_band ha hτ)
    (show 0 ≤ 6 * a by positivity)
  have he : 6 * a * (-(1 + 1 / a)) = -6 * a - 6 := by
    field_simp [ha.ne']
    ring
  rw [← mul_assoc, he] at h
  nlinarith only [h]

/-- Every physical radial scale at least six has a strictly positive full band. -/
theorem besselSignedRadialCombination_pos {a τ : ℝ} (ha : 6 ≤ a) (hτ : |τ| ≤ a) :
    0 < (a ^ 2 + 9) * (modifiedBesselKOrder a ((τ : ℂ) * I)).re +
      6 * a * (besselArgDeriv ((τ : ℂ) * I) a).re := by
  have ha0 : 0 < a := by linarith only [ha]
  have hp : 0 < a ^ 2 - 6 * a + 3 := by
    have h := mul_nonneg ha0.le (sub_nonneg.mpr ha)
    nlinarith only [h]
  exact (mul_pos hp (modifiedBesselKOrder_re_pos_on_band ha0 hτ)).trans_le
    (besselSignedRadialCombination_lower ha0 hτ)

#print axioms hasDerivAt_besselBarrierFlux
#print axioms tendsto_besselBarrierFlux_zero
#print axioms besselArgDeriv_re_lower_on_band
#print axioms besselSignedRadialCombination_pos

end GaloisForLFunctions.CompletedArithmeticForms
