import GaloisForLFunctions.HTGeometry.BesselOrderPolyaRealZeros

/-!
# The nonoscillatory spectral band of the Schläfli source

The actual Bessel energy flux has nonnegative density when argument dominates
imaginary order. A zero would force a strictly positive flux on a ray, against
its literal exponential decay. Every order zero therefore lies strictly beyond
the argument scale. This is a source-derived spectral boundary for physical
cosh kernels.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.CompletedArithmeticForms

open HTGeometry

/-- The literal Schläfli energy flux vanishes at infinity for every fixed order. -/
theorem tendsto_besselEnergyFlux_zero (ν : ℂ) :
    Tendsto (besselEnergyFlux ν) atTop (𝓝 0) := by
  let M := besselOrderUnitMass ν
  let M' := besselOrderUnitMass (ν + 1)
  have hM : 0 ≤ M := besselOrderUnitMass_nonneg ν
  have hM' : 0 ≤ M' := besselOrderUnitMass_nonneg (ν + 1)
  have hbound (R : ℝ) (hR : 1 ≤ R) : ‖besselEnergyFlux ν R‖ ≤
      (‖ν‖ * M * M * Real.exp 2) * Real.exp (-R) +
        (M' * M * Real.exp 2) * (R * Real.exp (-R)) := by
    have hf := norm_modifiedBesselKOrder_le_exp hR ν
    have hg := norm_modifiedBesselKOrder_le_exp hR (ν + 1)
    have he : Real.exp (1 - R) * Real.exp (1 - R) ≤ Real.exp 2 * Real.exp (-R) := by
      rw [← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith only [hR])
    have hR0 : (0 : ℝ) ≤ R := by linarith only [hR]
    rw [besselEnergyFlux, norm_mul, Complex.norm_conj]
    calc
      _ ≤ (‖ν‖ * ‖modifiedBesselKOrder R ν‖ + R * ‖modifiedBesselKOrder R (ν + 1)‖) *
          ‖modifiedBesselKOrder R ν‖ := by
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0]
      _ ≤ (‖ν‖ * (Real.exp (1 - R) * M) + R * (Real.exp (1 - R) * M')) *
          (Real.exp (1 - R) * M) := by gcongr
      _ = (‖ν‖ * M * M + R * M' * M) * (Real.exp (1 - R) * Real.exp (1 - R)) := by ring
      _ ≤ (‖ν‖ * M * M + R * M' * M) * (Real.exp 2 * Real.exp (-R)) := by gcongr
      _ = _ := by ring
  have h1 : Tendsto (fun R : ℝ => Real.exp (-R)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun R : ℝ => R * Real.exp (-R)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hsum : Tendsto (fun R : ℝ =>
      (‖ν‖ * M * M * Real.exp 2) * Real.exp (-R) +
        (M' * M * Real.exp 2) * (R * Real.exp (-R))) atTop (𝓝 0) := by
    simpa using (h1.const_mul _).add (h2.const_mul _)
  refine squeeze_zero_norm' ?_ hsum
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR using hbound R hR

theorem continuousAt_besselArgDeriv {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    ContinuousAt (besselArgDeriv ν) x := by
  unfold besselArgDeriv
  exact ((continuousAt_const.div Complex.continuous_ofReal.continuousAt
    (by exact_mod_cast hx.ne')).mul
      (hasDerivAt_modifiedBesselKOrder_arg hx ν).continuousAt).sub
        (hasDerivAt_modifiedBesselKOrder_arg_succ hx ν).continuousAt

/-- The real energy density at imaginary order, retaining the argument derivative square. -/
def besselBandEnergyDensity (τ x : ℝ) : ℝ :=
  (x - τ ^ 2 / x) * ‖modifiedBesselKOrder x ((τ : ℂ) * I)‖ ^ 2 +
    x * ‖besselArgDeriv ((τ : ℂ) * I) x‖ ^ 2

theorem hasDerivAt_besselEnergyFlux_band {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    HasDerivAt (besselEnergyFlux ((τ : ℂ) * I)) (besselBandEnergyDensity τ x : ℂ) x := by
  have hν : ((τ : ℂ) * I) ^ 2 = -((τ ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  apply (hasDerivAt_besselEnergyFlux hx ((τ : ℂ) * I)).congr_deriv
  rw [hν]
  unfold besselBandEnergyDensity
  push_cast
  ring

theorem continuousAt_besselBandEnergyDensity {x : ℝ} (hx : 0 < x) (τ : ℝ) :
    ContinuousAt (besselBandEnergyDensity τ) x := by
  unfold besselBandEnergyDensity
  exact ((continuousAt_id.sub (continuousAt_const.div continuousAt_id hx.ne')).mul
    ((hasDerivAt_modifiedBesselKOrder_arg hx ((τ : ℂ) * I)).continuousAt.norm.pow 2)).add
      (continuousAt_id.mul ((continuousAt_besselArgDeriv hx ((τ : ℂ) * I)).norm.pow 2))

theorem besselBandEnergyDensity_nonneg {τ x : ℝ} (hx : 0 < x) (hτ : |τ| ≤ x) :
    0 ≤ besselBandEnergyDensity τ x := by
  have hs : τ ^ 2 ≤ x ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg τ) hτ 2
  have hc : 0 ≤ x - τ ^ 2 / x :=
    sub_nonneg.mpr ((div_le_iff₀ hx).mpr (by nlinarith only [hs]))
  exact add_nonneg (mul_nonneg hc (sq_nonneg _)) (mul_nonneg hx.le (sq_nonneg _))

theorem besselBandEnergyDensity_pos {τ x : ℝ} (hx : 0 < x) (hτ : |τ| < x)
    (hf : modifiedBesselKOrder x ((τ : ℂ) * I) ≠ 0) :
    0 < besselBandEnergyDensity τ x := by
  obtain ⟨hl, hu⟩ := abs_lt.mp hτ
  have hs : 0 < (x - τ) * (x + τ) := mul_pos (sub_pos.mpr hu) (by linarith only [hl])
  have hc : 0 < x - τ ^ 2 / x :=
    sub_pos.mpr ((div_lt_iff₀ hx).mpr (by nlinarith only [hs]))
  exact add_pos_of_pos_of_nonneg (mul_pos hc (pow_pos (norm_pos_iff.mpr hf) 2))
    (mul_nonneg hx.le (sq_nonneg _))

/-- No imaginary-order zero occurs at or below the literal argument scale. -/
theorem modifiedBesselKOrder_ne_zero_on_band {a τ : ℝ} (ha : 0 < a) (hτ : |τ| ≤ a) :
    modifiedBesselKOrder a ((τ : ℂ) * I) ≠ 0 := by
  intro hzero
  let ν : ℂ := (τ : ℂ) * I
  have hFTC (R : ℝ) (haR : a ≤ R) :
      besselEnergyFlux ν R = ((∫ x in a..R, besselBandEnergyDensity τ x : ℝ) : ℂ) := by
    have hpos (x : ℝ) (hx : x ∈ uIcc a R) : 0 < x := by
      rw [uIcc_of_le haR] at hx
      exact ha.trans_le hx.1
    have hi : IntervalIntegrable (fun x => (besselBandEnergyDensity τ x : ℂ)) volume a R :=
      ContinuousOn.intervalIntegrable fun x hx =>
        (Complex.continuous_ofReal.continuousAt.comp
          (continuousAt_besselBandEnergyDensity (hpos x hx) τ)).continuousWithinAt
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_besselEnergyFlux_band (hpos x hx) τ) hi
    have hz : besselEnergyFlux ν a = 0 := by
      change besselEnergyFlux ((τ : ℂ) * I) a = 0
      rw [besselEnergyFlux, hzero]
      simp
    change (∫ x in a..R, (besselBandEnergyDensity τ x : ℂ)) =
      besselEnergyFlux ν R - besselEnergyFlux ν a at he
    rw [hz, sub_zero, intervalIntegral.integral_ofReal] at he
    exact he.symm
  obtain ⟨X, hX1, hXpos⟩ := eventually_re_modifiedBesselKOrder_pos ν
  let x₀ := max X (a + 1)
  have hx₀a : a < x₀ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hx₀ : 0 < x₀ := ha.trans hx₀a
  have hf : modifiedBesselKOrder x₀ ν ≠ 0 := by
    intro hz
    have hp := hXpos x₀ (le_max_left _ _)
    rw [hz, Complex.zero_re] at hp
    exact lt_irrefl 0 hp
  let R₁ := x₀ + 1
  have hR₁ : a < R₁ := by dsimp only [R₁]; linarith only [hx₀a]
  have hI : 0 < ∫ x in a..R₁, besselBandEnergyDensity τ x := by
    refine intervalIntegral.integral_pos hR₁
      (fun x hx => (continuousAt_besselBandEnergyDensity (ha.trans_le hx.1) τ).continuousWithinAt)
      (fun x hx => besselBandEnergyDensity_nonneg (ha.trans hx.1) (hτ.trans hx.1.le))
      ⟨x₀, ⟨hx₀a.le, by dsimp only [R₁]; linarith⟩, ?_⟩
    exact besselBandEnergyDensity_pos hx₀ (hτ.trans_lt hx₀a) hf
  have hmono (R : ℝ) (hR : R₁ ≤ R) :
      (∫ x in a..R₁, besselBandEnergyDensity τ x) ≤
        ∫ x in a..R, besselBandEnergyDensity τ x := by
    refine intervalIntegral.integral_mono_interval le_rfl hR₁.le hR ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact besselBandEnergyDensity_nonneg (ha.trans hx.1) (hτ.trans hx.1.le)
    · exact ContinuousOn.intervalIntegrable fun x hx =>
        (continuousAt_besselBandEnergyDensity (by
          rw [uIcc_of_le (hR₁.le.trans hR)] at hx
          exact ha.trans_le hx.1) τ).continuousWithinAt
  obtain ⟨R, hR⟩ := (Metric.tendsto_atTop.mp (tendsto_besselEnergyFlux_zero ν)) _ hI
  have hsmall := hR (max R R₁) (le_max_left _ _)
  rw [dist_zero_right, hFTC (max R R₁) (hR₁.le.trans (le_max_right _ _)),
    Complex.norm_real, Real.norm_eq_abs] at hsmall
  have hlarge := hmono (max R R₁) (le_max_right _ _)
  have habs := le_abs_self (∫ x in a..max R R₁, besselBandEnergyDensity τ x)
  linarith only [hsmall, hlarge, habs]

/-- Every order zero is purely imaginary and has modulus strictly exceeding the source argument. -/
theorem modifiedBesselKOrder_zero_outside_band {a : ℝ} (ha : 0 < a) {ν : ℂ}
    (hz : modifiedBesselKOrder a ν = 0) : ν.re = 0 ∧ a < |ν.im| := by
  have hre := re_eq_zero_of_modifiedBesselKOrder_eq_zero ha hz
  refine ⟨hre, ?_⟩
  by_contra h
  have he : ν = (ν.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  rw [he] at hz
  exact modifiedBesselKOrder_ne_zero_on_band ha (le_of_not_gt h) hz

/-- Imaginary-order Schläfli values are real, directly from order reflection and conjugation. -/
theorem modifiedBesselKOrder_imaginaryOrder_im (a τ : ℝ) :
    (modifiedBesselKOrder a ((τ : ℂ) * I)).im = 0 := by
  have hc := modifiedBesselKOrder_conj a ((τ : ℂ) * I)
  have he : (starRingEnd ℂ) ((τ : ℂ) * I) = -((τ : ℂ) * I) := by simp
  rw [he, modifiedBesselKOrder_neg] at hc
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith only [hi]

/-- The entire nonoscillatory band has strictly positive Schläfli density. -/
theorem modifiedBesselKOrder_re_pos_on_band {a τ : ℝ} (ha : 0 < a) (hτ : |τ| ≤ a) :
    0 < (modifiedBesselKOrder a ((τ : ℂ) * I)).re := by
  by_contra hn
  have ha0 := le_of_not_gt hn
  obtain ⟨X, hX1, hXpos⟩ := eventually_re_modifiedBesselKOrder_pos ((τ : ℂ) * I)
  let R := max a X
  have haR : a ≤ R := le_max_left _ _
  have hR : 0 < (modifiedBesselKOrder R ((τ : ℂ) * I)).re :=
    hXpos R (le_max_right _ _)
  have hc : ContinuousOn (fun x : ℝ => (modifiedBesselKOrder x ((τ : ℂ) * I)).re)
      (Icc a R) := fun x hx =>
    (Complex.continuous_re.continuousAt.comp
      (hasDerivAt_modifiedBesselKOrder_arg (ha.trans_le hx.1) ((τ : ℂ) * I)).continuousAt).continuousWithinAt
  obtain ⟨y, hy, he⟩ := intermediate_value_Icc haR hc ⟨ha0, hR.le⟩
  have hz : modifiedBesselKOrder y ((τ : ℂ) * I) = 0 := by
    apply Complex.ext
    · exact he
    · exact modifiedBesselKOrder_imaginaryOrder_im y τ
  exact modifiedBesselKOrder_ne_zero_on_band (ha.trans_le hy.1) (hτ.trans hy.1) hz

#print axioms tendsto_besselEnergyFlux_zero
#print axioms modifiedBesselKOrder_ne_zero_on_band
#print axioms modifiedBesselKOrder_zero_outside_band
#print axioms modifiedBesselKOrder_re_pos_on_band

end GaloisForLFunctions.CompletedArithmeticForms
