import GaloisForLFunctions.«arithmetic-positivity-theory».CollaredCriticalArchimedeanLogCoercivity

/-!
# Positive definiteness of the complete collared critical form on high dyadic blocks

The complete collared critical energy is the Gamma–Lévy form of the collared critical source
`g_c = σ(e^{-x} - 1) g_b`:

`E_c(g_c) = Lévy(g_c) + Ω(0) ac_c(0) + 2 R_c E_c - 2 P_c`.

Its terms are the archimedean jump energy, the Gamma channel at the origin, the polar product of
the half-exponential moments `R_c = ∫ g_c e^{x/2}` and `E_c = ∫ g_c e^{-x/2}`, and the prime
channel.

* **Gamma channel.** Unit windows weighted by `j^{-2}` give the `ℓ²` ceiling
  `ac_c(0) = ∫ g_c² ≤ (π²/6) J ∑ b_n²`.
* **Polar channels.** `R_c = ∫_{v>1} ψ B_b` and `E_c`, the limit of `∫_1^X σ(v - 1) B_b(v)/v dv`,
  are integrated by parts against the bounded phase primitive. Both are at most a constant times
  `∑ |b_n|/(n+1)`, so their product is `O(∑ b_n² / M)`.
* **Prime channel.** By the `ℓ²`-uniform collared bound it is at most `C_c ∑ b_n²`.

With the collared logarithmic law `Lévy(g_c) ≥ s_c (log M - c_c) ∑ b_n²` this gives
`E_c(g_c) ≥ (s_c (log M - c_c) - K) ∑ b_n²` on every dyadic block. Hence there is an absolute scale
`M₀` beyond which the complete collared critical form is positive definite on every dyadic block,
whatever the number and positions of the atoms.
-/

open MeasureTheory Set Filter
open scoped Topology ENNReal
open _root_.Zeta23

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ### The Gamma channel: an `ℓ²` upper bound for the collared mass -/

theorem integrableOn_rpow_neg_two_mul_norm_sq_factorialPhaseCombination (S : Finset ℕ)
    (b : ℕ → ℂ) :
    IntegrableOn (fun v => v ^ (-2 : ℝ) * ‖factorialPhaseCombination S b v‖ ^ 2) (Ioi 1) := by
  have hw : IntegrableOn (fun v : ℝ => v ^ (-2 : ℝ)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  refine (hw.mul_const ((2 * ∑ n ∈ S, ‖b n‖) ^ 2)).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable (fun x hx => ?_) measurableSet_Ioi
    have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne')).mul
      ((continuous_factorialPhaseCombination S b).norm.pow 2).continuousAt).continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans zero_lt_one hv
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hv0.le _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (norm_factorialPhaseCombination_le S b v) 2) (Real.rpow_nonneg hv0.le _)

/-- **`ℓ²` upper bound with the critical weight.**
`∫_1^∞ v^{-2} ‖B_b(v)‖² dv ≤ (π²/6) J ∑ ‖b_n‖²`, summing unit windows weighted by `j^{-2}`. -/
theorem integral_Ioi_one_rpow_neg_two_mul_norm_sq_le (S : Finset ℕ) (b : ℕ → ℂ) :
    (∫ v in Ioi 1, v ^ (-2 : ℝ) * ‖factorialPhaseCombination S b v‖ ^ 2) ≤
      Real.pi ^ 2 / 6 * factorialUnitIntervalUpper * ∑ n ∈ S, ‖b n‖ ^ 2 := by
  set Sb := ∑ n ∈ S, ‖b n‖ ^ 2 with hSb
  have hSb0 : 0 ≤ Sb := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set g : ℝ → ℝ := fun v => v ^ (-2 : ℝ) * ‖factorialPhaseCombination S b v‖ ^ 2 with hg
  have hint : IntegrableOn g (Ioi 1) :=
    integrableOn_rpow_neg_two_mul_norm_sq_factorialPhaseCombination S b
  have hlim := intervalIntegral_tendsto_integral_Ioi (f := g) (μ := volume) 1 hint
    (b := fun M : ℕ => 1 + (M : ℝ)) (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  refine le_of_tendsto' hlim fun M => ?_
  have hpiece : ∀ j : ℕ, IntervalIntegrable g volume (1 + (j : ℝ)) (1 + ((j + 1 : ℕ) : ℝ)) ∧
      (∫ v in (1 + (j : ℝ))..(1 + ((j + 1 : ℕ) : ℝ)), g v) ≤
        (1 / ((j + 1 : ℕ) : ℝ) ^ 2) * (factorialUnitIntervalUpper * Sb) := by
    intro j
    set aj : ℝ := 1 + (j : ℝ) with haj
    have haj1 : 1 ≤ aj := by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    have haj0 : 0 < aj := by linarith
    have hend : (1 : ℝ) + ((j + 1 : ℕ) : ℝ) = aj + 1 := by rw [haj]; push_cast; ring
    rw [hend]
    have hgi : IntervalIntegrable g volume aj (aj + 1) := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
      exact hint.mono_set fun v hv => lt_of_le_of_lt haj1 hv.1
    obtain ⟨hBi, hBle⟩ := factorialPhaseCombination_dilated_window_upper S b le_rfl aj zero_le_one
    simp only [one_mul] at hBi hBle
    refine ⟨hgi, ?_⟩
    have hmono : (∫ v in aj..aj + 1, g v) ≤
        ∫ v in aj..aj + 1, aj ^ (-2 : ℝ) * ‖factorialPhaseCombination S b v‖ ^ 2 := by
      refine intervalIntegral.integral_mono_on (by linarith) hgi (hBi.const_mul _) fun v hv => ?_
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos haj0 hv.1 (by norm_num)) (sq_nonneg _)
    rw [intervalIntegral.integral_const_mul] at hmono
    have hpow : aj ^ (-2 : ℝ) = 1 / ((j + 1 : ℕ) : ℝ) ^ 2 := by
      rw [Real.rpow_neg haj0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, haj,
        one_div]
      push_cast
      ring_nf
    rw [hpow] at hmono
    refine hmono.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    unfold factorialUnitIntervalUpper
    have he : 49 / (4 * Real.pi ^ 4) * (1 + factorialWindowGapConstant) * Sb =
        49 * (1 + factorialWindowGapConstant) / (4 * Real.pi ^ 4) * Sb := by ring
    rw [← he]
    simpa using hBle
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := g)
    (a := fun k : ℕ => 1 + (k : ℝ)) (n := M) fun k _ => (hpiece k).1
  simp only [Nat.cast_zero, add_zero] at hsum
  rw [← hsum]
  have hz : Summable fun d : ℕ => 1 / (d : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  have hJ : 0 ≤ factorialUnitIntervalUpper * Sb := mul_nonneg factorialUnitIntervalUpper_pos.le hSb0
  calc (∑ k ∈ Finset.range M, ∫ v in (1 + (k : ℝ))..(1 + ((k + 1 : ℕ) : ℝ)), g v) ≤
        ∑ k ∈ Finset.range M, (1 / ((k + 1 : ℕ) : ℝ) ^ 2) * (factorialUnitIntervalUpper * Sb) :=
        Finset.sum_le_sum fun k _ => (hpiece k).2
    _ = (∑ k ∈ Finset.range M, 1 / ((k + 1 : ℕ) : ℝ) ^ 2) * (factorialUnitIntervalUpper * Sb) := by
        rw [Finset.sum_mul]
    _ ≤ (∑' d : ℕ, 1 / (d : ℝ) ^ 2) * (factorialUnitIntervalUpper * Sb) := by
        refine mul_le_mul_of_nonneg_right ?_ hJ
        have himg : ∑ k ∈ Finset.range M, 1 / ((k + 1 : ℕ) : ℝ) ^ 2 =
            ∑ d ∈ (Finset.range M).image (fun k : ℕ => k + 1), 1 / (d : ℝ) ^ 2 := by
          rw [Finset.sum_image fun x _ y _ h => Nat.add_right_cancel h]
        rw [himg]
        exact hz.sum_le_tsum _ fun d _ => by positivity
    _ = Real.pi ^ 2 / 6 * factorialUnitIntervalUpper * Sb := by
        rw [hasSum_zeta_two.tsum_eq]; ring

/-- Upper mass constant `U = (π²/6) J` of collared sources. -/
def criticalCollarMassUpper : ℝ := Real.pi ^ 2 / 6 * factorialUnitIntervalUpper

/-- **Collared mass ceiling.** `ac_c(0) = ∫ g_c² ≤ U ∑ b_n²`. -/
theorem sourceAutocorrelation_criticalCollaredSource_zero_le (S : Finset ℕ) (b : ℕ → ℝ) :
    sourceAutocorrelation (criticalCollaredSource S b) 0 ≤
      criticalCollarMassUpper * ∑ n ∈ S, b n ^ 2 := by
  set B := factorialPhaseCombination S (fun n => (b n : ℂ))
  have hsq : sourceAutocorrelation (criticalCollaredSource S b) 0 =
      ∫ y, criticalCollaredSource S b y ^ 2 := by
    unfold sourceAutocorrelation
    simp only [sub_zero, sq]
  have hup := integral_Ioi_one_rpow_neg_two_mul_norm_sq_le S (fun n => (b n : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hup
  rw [hsq, integral_criticalCollaredSource_sq_eq]
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun v => by positivity) ?_ ?_) hup
  · exact integrableOn_rpow_neg_two_mul_norm_sq_factorialPhaseCombination S (fun n => (b n : ℂ))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0 < v := lt_trans zero_lt_one hv
    have hσ : Real.smoothTransition (v - 1) ^ 2 ≤ 1 :=
      pow_le_one₀ (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)
    rw [Real.rpow_neg hv0.le, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [inv_mul_eq_div]
    gcongr
    calc Real.smoothTransition (v - 1) ^ 2 * ‖B v‖ ^ 2 ≤ 1 * ‖B v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hσ (sq_nonneg _)
      _ = _ := one_mul _

/-! ### The polar channels of a collared source -/

/-- Upper polar readout `∫_{v>1} ψ(v) B_b(v) dv` of a collared source. -/
def criticalCollaredPolarReadout (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  ∫ v in Ioi 1, criticalCollarWeight v * (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re

/-- The upper readout is the half-exponential moment: `∫ g_c(x) e^{x/2} dx = ∫_{v>1} ψ B_b`. -/
theorem integral_criticalCollaredSource_mul_exp_half (S : Finset ℕ) (b : ℕ → ℝ) :
    ∫ x, criticalCollaredSource S b x * Real.exp (x / 2) = criticalCollaredPolarReadout S b := by
  set F : ℝ → ℝ := fun v => (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re
  have hpt : ∀ x, criticalCollaredSource S b x * Real.exp (x / 2) = (Iic (0 : ℝ)).indicator
      (fun x => Real.exp x * (Real.smoothTransition (Real.exp (-x) - 1) * F (Real.exp (-x)))) x := by
    intro x
    by_cases hx : x ≤ 0
    · rw [indicator_of_mem (show x ∈ Iic 0 from hx)]
      simp only [criticalCollaredSource, criticalFactorialSource,
        indicator_of_mem (show x ∈ Iic 0 from hx), F]
      have : Real.exp (x / 2) * Real.exp (x / 2) = Real.exp x := by rw [← Real.exp_add]; ring_nf
      rw [← this]
      ring
    · rw [indicator_of_notMem (show x ∉ Iic 0 from hx)]
      simp [criticalCollaredSource, criticalFactorialSource,
        indicator_of_notMem (show x ∉ Iic 0 from hx)]
  rw [funext hpt, integral_indicator measurableSet_Iic,
    integral_Iic_zero_exp_mul_comp_exp_neg (fun v => Real.smoothTransition (v - 1) * F v)]
  unfold criticalCollaredPolarReadout
  refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
  simp only [criticalCollarWeight, F]
  ring

private theorem phase_re_bound (S : Finset ℕ) (b : ℕ → ℝ) (v : ℝ) :
    ‖(factorialPhaseCombination S (fun n => (b n : ℂ)) v).re‖ ≤ 2 * ∑ n ∈ S, |b n| := by
  have h := (Complex.abs_re_le_norm _).trans
    (norm_factorialPhaseCombination_le S (fun n => (b n : ℂ)) v)
  simpa [Complex.norm_real] using h

/-- **The collared readout is `ℓ²`-small.** Integrating by parts against the bounded primitive,
`|R_c| ≤ ‖ψ'‖₁ · 12 ∑ |b_n|/(n+1)`. -/
theorem abs_criticalCollaredPolarReadout_le (S : Finset ℕ) (b : ℕ → ℝ) :
    |criticalCollaredPolarReadout S b| ≤ (∫ v in Ioi 1, |deriv criticalCollarWeight v|) *
      (12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) := by
  set G := criticalFactorialPhasePrimitive S b
  set P := 12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hGb (v : ℝ) : |G v| ≤ P := criticalFactorialPhasePrimitive_bound S b v
  have hP : 0 ≤ P := (abs_nonneg _).trans (hGb 0)
  set F : ℝ → ℝ := fun v => (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re
  have hFc : Continuous F := Complex.continuous_re.comp (continuous_factorialPhaseCombination _ _)
  have hGc : ContinuousOn G (Ioi 0) := fun x hx =>
    (criticalFactorialPhasePrimitive_hasDerivAt S b hx).continuousAt.continuousWithinAt
  have hint1 : IntegrableOn (criticalCollarWeight * F) (Ioi 1) :=
    integrableOn_criticalCollarWeight.mul_bdd hFc.aestronglyMeasurable
      (Eventually.of_forall fun v => phase_re_bound S b v)
  have hint2 : IntegrableOn (deriv criticalCollarWeight * G) (Ioi 1) :=
    integrableOn_deriv_criticalCollarWeight.mul_bdd
      ((hGc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi)
      (Eventually.of_forall fun v => by simpa only [Real.norm_eq_abs] using hGb v)
  have hlim1 : Tendsto (criticalCollarWeight * G) (𝓝[>] 1) (𝓝 0) := by
    have h := ((hasDerivAt_criticalCollarWeight 1).continuousAt.mul
      (criticalFactorialPhasePrimitive_hasDerivAt S b one_pos).continuousAt).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
    have h0 : (criticalCollarWeight * G) 1 = 0 := by
      simp [criticalCollarWeight_eq_zero le_rfl]
    rwa [h0] at h
  have hlim2 : Tendsto (criticalCollarWeight * G) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun v => ?_)
      (by simpa using tendsto_criticalCollarWeight_atTop.norm.mul_const P)
    rw [Pi.mul_apply, norm_mul, Real.norm_eq_abs (G v)]
    exact mul_le_mul_of_nonneg_left (hGb v) (norm_nonneg _)
  have e := integral_Ioi_mul_deriv_eq_deriv_mul (u := criticalCollarWeight) (v := G)
    (u' := deriv criticalCollarWeight) (v' := F) (a' := 0) (b' := 0)
    (fun x _ => hasDerivAt_criticalCollarWeight x)
    (fun x hx => criticalFactorialPhasePrimitive_hasDerivAt S b (lt_trans one_pos hx))
    hint1 hint2 hlim1 hlim2
  unfold criticalCollaredPolarReadout
  change |∫ v in Ioi 1, criticalCollarWeight v * F v| ≤ _
  rw [e, sub_self, zero_sub, abs_neg, ← integral_mul_const]
  refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on hint2.abs
    (integrableOn_deriv_criticalCollarWeight.abs.mul_const P) measurableSet_Ioi fun v _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hGb v) (abs_nonneg _)

/-- Endpoint collar `ρ(v) = σ(v - 1)/v`. -/
def criticalCollarEndpointWeight (v : ℝ) : ℝ := Real.smoothTransition (v - 1) / v

theorem criticalCollarEndpointWeight_eq_zero {x : ℝ} (hx : x ≤ 1) : criticalCollarEndpointWeight x = 0 := by
  rw [criticalCollarEndpointWeight, Real.smoothTransition.zero_of_nonpos (by linarith), zero_div]

theorem criticalCollarEndpointWeight_eq_of_two_le {x : ℝ} (hx : 2 ≤ x) :
    criticalCollarEndpointWeight x = 1 * x ^ (-1 : ℤ) := by
  rw [criticalCollarEndpointWeight, Real.smoothTransition.one_of_one_le (by linarith), one_mul,
    zpow_neg_one, one_div]

theorem contDiff_criticalCollarEndpointWeight : ContDiff ℝ (⊤ : ℕ∞) criticalCollarEndpointWeight := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  rcases lt_or_ge x 1 with hx | hx
  · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact criticalCollarEndpointWeight_eq_zero (le_of_lt hy)
  · exact (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffAt.div
      contDiffAt_id (by positivity)

theorem hasDerivAt_criticalCollarEndpointWeight (x : ℝ) :
    HasDerivAt criticalCollarEndpointWeight (deriv criticalCollarEndpointWeight x) x :=
  ((contDiff_infty_iff_deriv.mp contDiff_criticalCollarEndpointWeight).1 x).hasDerivAt

theorem deriv_criticalCollarEndpointWeight_of_two_lt {x : ℝ} (hx : 2 < x) :
    deriv criticalCollarEndpointWeight x = -1 * x ^ (-2 : ℤ) := by
  have he : criticalCollarEndpointWeight =ᶠ[𝓝 x] fun y => y ^ (-1 : ℤ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [criticalCollarEndpointWeight_eq_of_two_le (le_of_lt hy), one_mul]
  rw [he.deriv_eq, (hasDerivAt_zpow (-1) x (Or.inl (by positivity))).deriv]
  norm_num

theorem integrableOn_deriv_criticalCollarEndpointWeight :
    IntegrableOn (deriv criticalCollarEndpointWeight) (Ioi 1) := by
  have hc := (contDiff_infty_iff_deriv.mp contDiff_criticalCollarEndpointWeight).2.continuous
  rw [← Ioc_union_Ioi_eq_Ioi one_le_two]
  refine (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self).union ?_
  refine IntegrableOn.congr_fun (((integrableOn_Ioi_rpow_of_lt (a := ((-2 : ℤ) : ℝ)) (by norm_num)
    two_pos).const_mul (-1))) (fun x hx => ?_) measurableSet_Ioi
  rw [deriv_criticalCollarEndpointWeight_of_two_lt hx, Real.rpow_intCast]

theorem tendsto_criticalCollarEndpointWeight_atTop :
    Tendsto criticalCollarEndpointWeight atTop (𝓝 0) := by
  refine (tendsto_zpow_atTop_zero (𝕜 := ℝ) (n := -1) (by norm_num)).congr' ?_
  filter_upwards [eventually_ge_atTop 2] with x hx
  rw [criticalCollarEndpointWeight_eq_of_two_le hx, one_mul]

/-- Lower polar endpoint of a collared source: the primitive regularization
`-∫_{v>1} ρ'(v) G_b(v) dv` of `∫_{v>1} σ(v - 1) B_b(v)/v dv`. -/
def criticalCollaredPolarEndpoint (S : Finset ℕ) (b : ℕ → ℝ) : ℝ :=
  -∫ v in Ioi 1, deriv criticalCollarEndpointWeight v * criticalFactorialPhasePrimitive S b v

private theorem integrableOn_deriv_endpoint_mul_primitive (S : Finset ℕ) (b : ℕ → ℝ) :
    IntegrableOn (fun v => deriv criticalCollarEndpointWeight v * criticalFactorialPhasePrimitive S b v)
      (Ioi 1) := by
  have hGc : ContinuousOn (criticalFactorialPhasePrimitive S b) (Ioi 0) := fun x hx =>
    (criticalFactorialPhasePrimitive_hasDerivAt S b hx).continuousAt.continuousWithinAt
  exact integrableOn_deriv_criticalCollarEndpointWeight.mul_bdd
    ((hGc.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi)
    (Eventually.of_forall fun v => by
      simpa only [Real.norm_eq_abs] using criticalFactorialPhasePrimitive_bound S b v)

/-- **The collared endpoint is the improper half-exponential moment.**
`∫_1^X σ(v - 1) B_b(v)/v dv → E_c` as `X → ∞`. -/
theorem tendsto_integral_criticalCollarEndpointWeight_mul (S : Finset ℕ) (b : ℕ → ℝ) :
    Tendsto (fun X => ∫ v in (1 : ℝ)..X, criticalCollarEndpointWeight v *
      (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re) atTop
      (𝓝 (criticalCollaredPolarEndpoint S b)) := by
  set G := criticalFactorialPhasePrimitive S b
  set P := 12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have hGb (v : ℝ) : |G v| ≤ P := criticalFactorialPhasePrimitive_bound S b v
  have hFc : Continuous fun v => (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re :=
    Complex.continuous_re.comp (continuous_factorialPhaseCombination _ _)
  have hc := (contDiff_infty_iff_deriv.mp contDiff_criticalCollarEndpointWeight).2.continuous
  have hIBP : ∀ X, 1 ≤ X → ∫ v in (1 : ℝ)..X, criticalCollarEndpointWeight v *
      (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re =
      criticalCollarEndpointWeight X * G X -
        ∫ v in (1 : ℝ)..X, deriv criticalCollarEndpointWeight v * G v := by
    intro X hX
    have e := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 1) (b := X)
      (u := criticalCollarEndpointWeight) (v := G) (u' := deriv criticalCollarEndpointWeight)
      (v' := fun v => (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re)
      (fun x _ => hasDerivAt_criticalCollarEndpointWeight x)
      (fun x hx => criticalFactorialPhasePrimitive_hasDerivAt S b (by
        rw [uIcc_of_le hX] at hx; linarith [hx.1]))
      (hc.intervalIntegrable 1 X) (hFc.intervalIntegrable 1 X)
    rw [e, criticalCollarEndpointWeight_eq_zero le_rfl, zero_mul, sub_zero]
  have hbd : Tendsto (fun X => criticalCollarEndpointWeight X * G X) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun v => ?_)
      (by simpa using tendsto_criticalCollarEndpointWeight_atTop.norm.mul_const P)
    rw [norm_mul, Real.norm_eq_abs (G v)]
    exact mul_le_mul_of_nonneg_left (hGb v) (norm_nonneg _)
  have htail := intervalIntegral_tendsto_integral_Ioi (μ := volume) 1
    (integrableOn_deriv_endpoint_mul_primitive S b) tendsto_id
  have hlim := hbd.sub htail
  rw [zero_sub] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [hIBP X hX]
  rfl

/-- **The collared endpoint is `ℓ²`-small.** `|E_c| ≤ ‖ρ'‖₁ · 12 ∑ |b_n|/(n+1)`. -/
theorem abs_criticalCollaredPolarEndpoint_le (S : Finset ℕ) (b : ℕ → ℝ) :
    |criticalCollaredPolarEndpoint S b| ≤ (∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v|) *
      (12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) := by
  set P := 12 * ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  unfold criticalCollaredPolarEndpoint
  rw [abs_neg, ← integral_mul_const]
  refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on
    (integrableOn_deriv_endpoint_mul_primitive S b).abs
    (integrableOn_deriv_criticalCollarEndpointWeight.abs.mul_const P) measurableSet_Ioi fun v _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (criticalFactorialPhasePrimitive_bound S b v) (abs_nonneg _)

/-- On scales `n + 1 ≥ M ≥ 2`: `(∑ |b_n|/(n+1))² ≤ (2/M) ∑ b_n²`. -/
theorem sq_sum_abs_div_succ_le (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : ∀ n ∈ S, M ≤ n + 1) :
    (∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 2 / M * ∑ n ∈ S, b n ^ 2 := by
  have hcs : (∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)) ^ 2 ≤
      (∑ n ∈ S, b n ^ 2) * ∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun n => |b n|) (fun n => 1 / ((n + 1 : ℕ) : ℝ))
    simpa only [mul_one_div, sq_abs] using h
  have hinv : (∑ n ∈ S, (1 / ((n + 1 : ℕ) : ℝ)) ^ 2) ≤ 2 / (M : ℝ) := by
    have h := sum_low_freq_sq_le_two_mul_sq_div (S.map ⟨fun n => n + 1, add_left_injective 1⟩) hM
      (by simpa using hS) 1
    simpa [Finset.sum_map] using h
  have hE : 0 ≤ ∑ n ∈ S, b n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc _ ≤ (∑ n ∈ S, b n ^ 2) * (2 / (M : ℝ)) := hcs.trans (mul_le_mul_of_nonneg_left hinv hE)
    _ = _ := by ring

/-! ### The complete collared critical form -/

/-- **Complete collared critical energy** in Gamma–Lévy form:
`Lévy(g_c) + Ω(0) ac_c(0) + 2 R_c E_c - 2 P_c`. -/
def criticalCollaredCompleteEnergy (S : Finset ℕ) (b : ℕ → ℝ) : EReal :=
  (sourceLevyEnergy (criticalCollaredSource S b) : EReal) +
    ((EF.gammaBracket 0 * sourceAutocorrelation (criticalCollaredSource S b) 0 +
      2 * (criticalCollaredPolarReadout S b * criticalCollaredPolarEndpoint S b) -
      2 * criticalCollaredPrimeEnergy S b : ℝ) : EReal)

/-- Channel constant `K = |Ω(0)| U + 288 ‖ψ'‖₁ ‖ρ'‖₁ + 2 C_c` of the collared form. -/
def criticalCollaredChannelConstant : ℝ :=
  |EF.gammaBracket 0| * criticalCollarMassUpper +
    288 * (∫ v in Ioi 1, |deriv criticalCollarWeight v|) *
      (∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v|) + 2 * criticalCollaredPrimeConstant

/-- The arithmetic channels of a collared source on a dyadic block are bounded below by `-K ∑ b_n²`. -/
theorem neg_le_criticalCollaredChannels (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : DyadicScaleBlock S M) :
    -(criticalCollaredChannelConstant * ∑ n ∈ S, b n ^ 2) ≤
      EF.gammaBracket 0 * sourceAutocorrelation (criticalCollaredSource S b) 0 +
        2 * (criticalCollaredPolarReadout S b * criticalCollaredPolarEndpoint S b) -
        2 * criticalCollaredPrimeEnergy S b := by
  set E := ∑ n ∈ S, b n ^ 2
  set ac := sourceAutocorrelation (criticalCollaredSource S b) 0
  set a := ∫ v in Ioi 1, |deriv criticalCollarWeight v|
  set c := ∫ v in Ioi 1, |deriv criticalCollarEndpointWeight v|
  set T := ∑ n ∈ S, |b n| / ((n + 1 : ℕ) : ℝ)
  have ha : 0 ≤ a := integral_nonneg fun _ => abs_nonneg _
  have hc : 0 ≤ c := integral_nonneg fun _ => abs_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg fun n _ => by positivity
  have hM0 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hac0 : 0 ≤ ac := by
    unfold ac sourceAutocorrelation
    exact integral_nonneg fun y => by simp only [sub_zero]; exact mul_self_nonneg _
  have hac := sourceAutocorrelation_criticalCollaredSource_zero_le S b
  have hΩ : -(|EF.gammaBracket 0| * (criticalCollarMassUpper * E)) ≤ EF.gammaBracket 0 * ac := by
    have h1 : -(|EF.gammaBracket 0| * ac) ≤ EF.gammaBracket 0 * ac := by
      have := neg_abs_le (EF.gammaBracket 0 * ac)
      rwa [abs_mul, abs_of_nonneg hac0] at this
    have h2 : |EF.gammaBracket 0| * ac ≤ |EF.gammaBracket 0| * (criticalCollarMassUpper * E) :=
      mul_le_mul_of_nonneg_left hac (abs_nonneg _)
    linarith
  have hT2 := sq_sum_abs_div_succ_le S b hM fun n hn => (hS n hn).1
  have hpol : |criticalCollaredPolarReadout S b * criticalCollaredPolarEndpoint S b| ≤ 144 * a * c * E := by
    rw [abs_mul]
    have h1 := abs_criticalCollaredPolarReadout_le S b
    have h2 := abs_criticalCollaredPolarEndpoint_le S b
    have h12 := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    have hTE : T ^ 2 ≤ E := hT2.trans (by
      have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have : 2 / (M : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hM0
      nlinarith)
    calc _ ≤ a * (12 * T) * (c * (12 * T)) := h12
      _ = 144 * a * c * T ^ 2 := by ring
      _ ≤ 144 * a * c * E := mul_le_mul_of_nonneg_left hTE (by positivity)
  have hP := abs_criticalCollaredPrimeEnergy_le (by omega) hS b
  have hP' := (abs_le.mp hP).2
  have hpol' := (abs_le.mp hpol).1
  unfold criticalCollaredChannelConstant
  nlinarith

/-- **Complete collared critical form on dyadic blocks.** For every family on a dyadic block
`[M, 2M]` (`M ≥ 2`) and every real coefficient vector,
`E_c(g_c) ≥ (s_c (log M - c_c) - K) ∑ b_n²`. -/
theorem criticalCollaredCompleteEnergy_ge (S : Finset ℕ) (b : ℕ → ℝ) {M : ℕ} (hM : 2 ≤ M)
    (hS : DyadicScaleBlock S M) :
    (((criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) -
        criticalCollaredChannelConstant) * ∑ n ∈ S, b n ^ 2 : ℝ) : EReal) ≤
      criticalCollaredCompleteEnergy S b := by
  set E := ∑ n ∈ S, b n ^ 2
  set X := criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) * E
  have hlev : (X : EReal) ≤ (sourceLevyEnergy (criticalCollaredSource S b) : EReal) := by
    have h1 := ofReal_le_criticalCollaredLevyEnergy S b hM fun n hn => (hS n hn).1
    have h2 := EReal.coe_ennreal_le_coe_ennreal_iff.mpr h1
    rw [EReal.coe_ennreal_ofReal] at h2
    exact le_trans (EReal.coe_le_coe_iff.mpr (le_max_left _ _)) h2
  have hch := neg_le_criticalCollaredChannels S b hM hS
  unfold criticalCollaredCompleteEnergy
  rw [show (criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) -
      criticalCollaredChannelConstant) * E = X + -(criticalCollaredChannelConstant * E) by ring,
    EReal.coe_add]
  exact add_le_add hlev (EReal.coe_le_coe_iff.mpr hch)

/-- **Positive definiteness of the complete collared critical form on high dyadic blocks.**
There is a scale `M₀` such that for every `M ≥ M₀`, every family on the dyadic block `[M, 2M]`
and every nonzero real coefficient vector, the complete collared critical energy is strictly
positive — with no restriction on the number or positions of the atoms. -/
theorem exists_criticalCollaredCompleteEnergy_pos :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ S : Finset ℕ, DyadicScaleBlock S M → ∀ b : ℕ → ℝ,
      (∃ n ∈ S, b n ≠ 0) → 0 < criticalCollaredCompleteEnergy S b := by
  have hs := criticalCollarArchLogSlope_pos
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop
    (criticalCollarArchLogOffset + criticalCollaredChannelConstant / criticalCollarArchLogSlope)).and
      (eventually_ge_atTop 2))
  refine ⟨M₀, fun M hM S hS b hb => ?_⟩
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  obtain ⟨j, hj, hbj⟩ := hb
  have hE : 0 < ∑ n ∈ S, b n ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj)
  have hgap : 0 < criticalCollarArchLogSlope * (Real.log M - criticalCollarArchLogOffset) -
      criticalCollaredChannelConstant := by
    have h1 : criticalCollaredChannelConstant / criticalCollarArchLogSlope <
        Real.log M - criticalCollarArchLogOffset := by linarith
    have h2 := (div_lt_iff₀ hs).mp h1
    linarith
  exact lt_of_lt_of_le (EReal.coe_pos.mpr (mul_pos hgap hE)) (criticalCollaredCompleteEnergy_ge S b hM2 hS)

end GaloisForLFunctions.ArithmeticPositivityTheory
