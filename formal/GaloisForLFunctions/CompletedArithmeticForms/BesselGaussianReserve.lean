import GaloisForLFunctions.CompletedArithmeticForms.BesselGaussianMoments

/-!
# A Gaussian reserve on the complete imaginary-order Bessel band

The literal source dominates `exp(-τ²/a) K₀(a)` whenever `|τ| ≤ a`.
Its Wronskian against this Gaussian barrier has nonnegative derivative and
zero limit at infinity. The exact source normalization fixes the comparison
constant. The signed radial combination retains the same reserve.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry

/-- Real imaginary-order Schläfli density. -/
def besselBandSource (τ x : ℝ) : ℝ := (modifiedBesselKOrder x ((τ : ℂ) * I)).re

/-- Its literal argument derivative. -/
def besselBandSourceDeriv (τ x : ℝ) : ℝ := (besselArgDeriv ((τ : ℂ) * I) x).re

theorem hasDerivAt_besselBandSource {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    HasDerivAt (besselBandSource τ) (besselBandSourceDeriv τ x) x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_modifiedBesselKOrder_arg hx _)

theorem hasDerivAt_besselArgDeriv_system {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    HasDerivAt (besselArgDeriv ν)
      ((1 + ν ^ 2 / (x : ℂ) ^ 2) * modifiedBesselKOrder x ν - besselArgDeriv ν x / x) x := by
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have h := (((hasDerivAt_const x ν).div hid hxC).mul
    (hasDerivAt_modifiedBesselKOrder_arg hx ν)).sub
      (hasDerivAt_modifiedBesselKOrder_arg_succ hx ν)
  apply h.congr_deriv
  dsimp only [besselArgDeriv, Pi.div_apply, Pi.mul_apply, Pi.sub_apply]
  field_simp [hxC]
  ring

theorem hasDerivAt_besselBandSourceDeriv {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    HasDerivAt (besselBandSourceDeriv τ)
      ((1 - τ ^ 2 / x ^ 2) * besselBandSource τ x - besselBandSourceDeriv τ x / x) x := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x
    (hasDerivAt_besselArgDeriv_system hx ((τ : ℂ) * I))
  have he : 1 + ((τ : ℂ) * I) ^ 2 / (x : ℂ) ^ 2 =
      ((1 - τ ^ 2 / x ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, I_sq]
    ring
  change HasDerivAt (besselBandSourceDeriv τ)
    (((1 + ((τ : ℂ) * I) ^ 2 / (x : ℂ) ^ 2) *
      modifiedBesselKOrder x ((τ : ℂ) * I) - besselArgDeriv ((τ : ℂ) * I) x / x).re) x at h
  rw [he] at h
  simpa only [Complex.sub_re, Complex.re_ofReal_mul, Complex.div_ofReal_re,
    besselBandSource, besselBandSourceDeriv] using h

theorem besselBandSource_zero_deriv_le {x : ℝ} (hx : 0 < x) :
    besselBandSourceDeriv 0 x ≤ -besselBandSource 0 x := by
  have h : realModifiedBesselKOrder x 0 ≤ realModifiedBesselKOrder x 1 := by
    apply setIntegral_mono_on (integrableOn_realBesselOrderKernel hx 0)
      (integrableOn_realBesselOrderKernel hx 1) measurableSet_Ioi
    intro t _
    simp only [realBesselOrderKernel, zero_mul, one_mul, Real.cosh_zero, mul_one]
    exact le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_cosh t)
  have hzero := modifiedBesselKOrder_ofReal hx 0
  have hone := modifiedBesselKOrder_ofReal hx 1
  simp only [Complex.ofReal_zero] at hzero
  simp only [Complex.ofReal_one] at hone
  simpa only [besselBandSourceDeriv, besselArgDeriv, besselBandSource,
    Complex.ofReal_zero, zero_mul, zero_div, zero_add, zero_sub,
    hzero, hone,
    Complex.neg_re, Complex.ofReal_re] using neg_le_neg h

/-- The Gaussian comparison Wronskian, retaining the full source derivatives. -/
def besselGaussianFlux (τ x : ℝ) : ℝ :=
  Real.exp (-τ ^ 2 / x) *
    (x * besselBandSourceDeriv τ x * besselBandSource 0 x -
      besselBandSource τ x * (x * besselBandSourceDeriv 0 x) -
      τ ^ 2 / x * besselBandSource τ x * besselBandSource 0 x)

theorem hasDerivAt_besselGaussianFlux {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    HasDerivAt (besselGaussianFlux τ)
      (-besselBandSource τ x * (τ ^ 2 * Real.exp (-τ ^ 2 / x) / x *
        (2 * besselBandSourceDeriv 0 x +
          (1 - 1 / x + τ ^ 2 / x ^ 2) * besselBandSource 0 x))) x := by
  have hf := hasDerivAt_besselBandSource hx τ
  have hD := hasDerivAt_besselBandSourceDeriv hx τ
  have hg := hasDerivAt_besselBandSource hx 0
  have hG := hasDerivAt_besselBandSourceDeriv hx 0
  have hid := hasDerivAt_id x
  have he := ((hasDerivAt_const x (-τ ^ 2)).div hid hx.ne').exp
  have hc := (hasDerivAt_const x (τ ^ 2)).div hid hx.ne'
  have h := he.mul ((((hid.mul hD).mul hg).sub (hf.mul (hid.mul hG))).sub
    ((hc.mul hf).mul hg))
  apply h.congr_deriv
  dsimp only [id_eq, Pi.div_apply, Pi.mul_apply, Pi.sub_apply]
  field_simp [hx.ne']
  ring

private theorem tendsto_arg_mul_bessel_zero (ν : ℂ) :
    Tendsto (fun x : ℝ => (x : ℂ) * modifiedBesselKOrder x ν) atTop (𝓝 0) := by
  have hl : Tendsto (fun x : ℝ =>
      (Real.exp 1 * besselOrderUnitMass ν) * (x * Real.exp (-x))) atTop (𝓝 0) := by
    simpa only [mul_zero, pow_one] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul
        (Real.exp 1 * besselOrderUnitMass ν)
  apply squeeze_zero_norm' _ hl
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hx)]
  calc
    _ ≤ x * (Real.exp (1 - x) * besselOrderUnitMass ν) :=
      mul_le_mul_of_nonneg_left (norm_modifiedBesselKOrder_le_exp hx ν) (zero_le_one.trans hx)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

private theorem tendsto_arg_mul_besselDeriv_zero (ν : ℂ) :
    Tendsto (fun x : ℝ => (x : ℂ) * besselArgDeriv ν x) atTop (𝓝 0) := by
  have h := ((tendsto_modifiedBesselKOrder_arg_zero ν).const_mul ν).sub
    (tendsto_arg_mul_bessel_zero (ν + 1))
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [besselArgDeriv]
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp [hxC]

theorem tendsto_besselGaussianFlux_zero (τ : ℝ) :
    Tendsto (besselGaussianFlux τ) atTop (𝓝 0) := by
  have hf (t : ℝ) : Tendsto (besselBandSource t) atTop (𝓝 0) := by
    change Tendsto (fun x : ℝ => (modifiedBesselKOrder x ((t : ℂ) * I)).re) atTop (𝓝 0)
    simpa only [Function.comp_def, Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp
        (tendsto_modifiedBesselKOrder_arg_zero ((t : ℂ) * I))
  have hD (t : ℝ) : Tendsto (fun x => x * besselBandSourceDeriv t x) atTop (𝓝 0) := by
    dsimp only [besselBandSourceDeriv]
    simpa only [Function.comp_def, Complex.zero_re, Complex.re_ofReal_mul] using
      Complex.continuous_re.continuousAt.tendsto.comp
        (tendsto_arg_mul_besselDeriv_zero ((t : ℂ) * I))
  have hc : Tendsto (fun x : ℝ => τ ^ 2 / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).const_mul (τ ^ 2)
  have he : Tendsto (fun x : ℝ => Real.exp (-τ ^ 2 / x)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, neg_div, neg_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp hc.neg
  change Tendsto (fun x : ℝ => Real.exp (-τ ^ 2 / x) *
    (x * besselBandSourceDeriv τ x * besselBandSource 0 x -
      besselBandSource τ x * (x * besselBandSourceDeriv 0 x) -
      τ ^ 2 / x * besselBandSource τ x * besselBandSource 0 x)) atTop (𝓝 0)
  simpa only [mul_zero, sub_zero] using
    he.mul (((hD τ).mul (hf 0)).sub ((hf τ).mul (hD 0)) |>.sub
      ((hc.mul (hf τ)).mul (hf 0)))

theorem besselGaussianFlux_nonpos {a τ : ℝ} (ha : 0 < a) (hτ : |τ| ≤ a) :
    besselGaussianFlux τ a ≤ 0 := by
  have hm : MonotoneOn (besselGaussianFlux τ) (Ici a) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
      (f' := fun x => -besselBandSource τ x * (τ ^ 2 * Real.exp (-τ ^ 2 / x) / x *
        (2 * besselBandSourceDeriv 0 x +
          (1 - 1 / x + τ ^ 2 / x ^ 2) * besselBandSource 0 x))) ?_ ?_ ?_
    · intro x hx
      exact (hasDerivAt_besselGaussianFlux (ha.trans_le hx) τ).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_besselGaussianFlux (ha.trans_le (interior_subset hx)) τ).hasDerivWithinAt
    · intro x hx
      have hx0 : 0 < x := ha.trans_le (interior_subset hx)
      have htx := hτ.trans (interior_subset hx)
      have hf := modifiedBesselKOrder_re_pos_on_band hx0 htx
      have hg : 0 < besselBandSource 0 x :=
        modifiedBesselKOrder_re_pos_on_band hx0 (by simpa using hx0.le)
      have hsq : τ ^ 2 ≤ x ^ 2 := by
        simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg τ) htx 2
      have hc : 1 - 1 / x + τ ^ 2 / x ^ 2 ≤ 2 := by
        have hdiv := (div_le_one (sq_pos_of_pos hx0)).mpr hsq
        have hinv : 0 ≤ 1 / x := by positivity
        linarith only [hdiv, hinv]
      have hd := besselBandSource_zero_deriv_le hx0
      have hp := mul_le_mul_of_nonneg_right hc hg.le
      have hbr : 2 * besselBandSourceDeriv 0 x +
          (1 - 1 / x + τ ^ 2 / x ^ 2) * besselBandSource 0 x ≤ 0 := by
        linarith only [hd, hp]
      exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hf.le)
        (mul_nonpos_of_nonneg_of_nonpos (by positivity) hbr)
  apply ge_of_tendsto (tendsto_besselGaussianFlux_zero τ)
  filter_upwards [eventually_ge_atTop a] with x hx
  exact hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx

/-- The full nonoscillatory Schläfli band retains a Gaussian density reserve. -/
theorem modifiedBesselKOrder_gaussian_lower {a τ : ℝ} (ha : 0 < a) (hτ : |τ| ≤ a) :
    Real.exp (-τ ^ 2 / a) * (modifiedBesselKOrder a 0).re ≤
      (modifiedBesselKOrder a ((τ : ℂ) * I)).re := by
  let H : ℝ → ℝ := fun x => Real.exp (-τ ^ 2 / x) * besselBandSource 0 x
  let R : ℝ → ℝ := fun x => besselBandSource τ x / H x
  have hHpos (x : ℝ) (hx : 0 < x) : 0 < H x :=
    mul_pos (Real.exp_pos _) (modifiedBesselKOrder_re_pos_on_band hx (by simpa using hx.le))
  have hder (x : ℝ) (hx : 0 < x) : HasDerivAt R
      (besselGaussianFlux τ x / (x * H x ^ 2)) x := by
    have h := (hasDerivAt_besselBandSource hx τ).div
      ((((hasDerivAt_const x (-τ ^ 2)).div (hasDerivAt_id x) hx.ne').exp).mul
        (hasDerivAt_besselBandSource hx 0)) (hHpos x hx).ne'
    have hg : 0 < besselBandSource 0 x :=
      modifiedBesselKOrder_re_pos_on_band hx (by simpa using hx.le)
    apply h.congr_deriv
    dsimp only [besselGaussianFlux, H, id_eq, Pi.div_apply, Pi.mul_apply]
    field_simp [hx.ne', (Real.exp_pos (-τ ^ 2 / x)).ne', hg.ne']
    ring
  have hm : MonotoneOn (fun x => -R x) (Ici a) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici a)
      (f' := fun x => -(besselGaussianFlux τ x / (x * H x ^ 2))) ?_ ?_ ?_
    · intro x hx
      exact (hder x (ha.trans_le hx)).neg.continuousAt.continuousWithinAt
    · intro x hx
      exact (hder x (ha.trans_le (interior_subset hx))).neg.hasDerivWithinAt
    · intro x hx
      have hx0 := ha.trans_le (interior_subset hx)
      exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg
        (besselGaussianFlux_nonpos hx0 (hτ.trans (interior_subset hx))) (by positivity))
  have hexp : Tendsto (fun x : ℝ => Real.exp (-τ ^ 2 / x)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).const_mul (-τ ^ 2))
  have hlim : Tendsto R atTop (𝓝 1) := by
    have h := (tendsto_bessel_imaginary_ratio_one τ).div hexp one_ne_zero
    simp only [div_one] at h
    apply h.congr
    intro x
    dsimp only [R, H, besselBandSource, Pi.div_apply]
    simp only [Complex.ofReal_zero, zero_mul, div_div]
    congr 1
    ring
  have hR : 1 ≤ R a := by
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop a] with x hx
    have h := hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
    linarith only [h]
  have hpay := (le_div_iff₀ (hHpos a ha)).mp hR
  simpa only [one_mul, H, besselBandSource, Complex.ofReal_zero, zero_mul] using hpay

/-- The signed radial derivative combination keeps the Gaussian reserve on physical scales. -/
theorem besselSignedRadialCombination_gaussian_lower {a τ : ℝ}
    (ha : 6 ≤ a) (hτ : |τ| ≤ a) :
    (a ^ 2 - 6 * a + 3) * Real.exp (-τ ^ 2 / a) * (modifiedBesselKOrder a 0).re ≤
      (a ^ 2 + 9) * (modifiedBesselKOrder a ((τ : ℂ) * I)).re +
        6 * a * (besselArgDeriv ((τ : ℂ) * I) a).re := by
  have ha0 : 0 < a := by linarith only [ha]
  have hp : 0 ≤ a ^ 2 - 6 * a + 3 := by
    have h := mul_nonneg ha0.le (sub_nonneg.mpr ha)
    nlinarith only [h]
  have h := (mul_le_mul_of_nonneg_left (modifiedBesselKOrder_gaussian_lower ha0 hτ) hp).trans
    (besselSignedRadialCombination_lower ha0 hτ)
  simpa only [mul_assoc] using h

#print axioms hasDerivAt_besselGaussianFlux
#print axioms besselGaussianFlux_nonpos
#print axioms modifiedBesselKOrder_gaussian_lower
#print axioms besselSignedRadialCombination_gaussian_lower

end GaloisForLFunctions.CompletedArithmeticForms
