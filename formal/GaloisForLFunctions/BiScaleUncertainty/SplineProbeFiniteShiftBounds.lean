import GaloisForLFunctions.BiScaleUncertainty.CubicSplineUniversalProbe
import GaloisForLFunctions.BiScaleUncertainty.FiniteCutoffPacketEnergyAsymptotics

/-!
# Effective finite-shift error bounds for the explicit cubic spline probe

The boosted cubic spline `splineProbe u = eᵘ B(u)` (`B = U_1^{⋆4}`) is a `C²` source supported in
`[−4, 4]` whose Fourier transform has no zeros in the critical strip (`seesAllZeros_splineProbe`).
In `CubicSplineUniversalProbe` its RH and zero-width equivalences are proved with existential
shift thresholds `∃ T K, ∀ τ ≥ T, …`.

This module establishes explicit, quantitative finite-shift bounds for `splineProbe` valid at
every shift `τ > 4` right above its support radius:

1. **Pointwise and gauge-derivative bounds on `cubicSpline` and `splineProbe`**
   (`cubicSpline_le_half`, `abs_deriv_cubicSpline_le_quarter`, `abs_gaugeDerivative_splineProbe_le`,
   `integral_abs_gaugeDerivative_splineProbe_le`):
   `0 ≤ B(u) ≤ 1/2`, `|B'(u)| ≤ 1/4`, `|(U' − U/2)(u)| ≤ (1/2) e⁴`, and `‖U' − U/2‖₁ ≤ 4 e⁴`.
2. **Exact local Chebyshev gauge representation and finite-shift error bounds**
   (`stationaryPacket_splineProbe_eq_local_gauge`,
   `abs_stationaryPacket_splineProbe_le_local_chebyshev`,
   `abs_splinePrimeSum_sub_splinePolarMass_le_local_chebyshev`): for every `τ > 4`,
   `P_U(τ)` depends only on the normalized Chebyshev error `Ẽ(t)` in the local window
   `[τ − 4, τ + 4]`, giving
   `|P_U(τ)| ≤ 4 e^{2 − τ/2} + (1/2) e⁴ ∫_{τ−4}^{τ+4} |Ẽ(t)| dt` and
   `|splinePrimeSum τ − splinePolarMass τ| ≤ 4 e^{2 + τ/2} + (1/2) e^{4 + τ} ∫_{τ−4}^{τ+4} |Ẽ(t)| dt`.
3. **Explicit spectral bounds on `Û(r)`, `packetArchTail splineProbe τ`, and the zero series**
   (`norm_paperFT_splineProbe_ofReal_le`, `norm_packetArchTail_splineProbe_le`,
   `norm_paperFT_splineProbe_gammaOf_le`, `tsum_norm_packetCoeff_splineProbe_le_totalZeroEnergy`):
   on the real line `‖Û(r)‖ ≤ (cosh 1)⁴ / (1 + r²)²`, so `‖A_U(τ)‖ ≤ (1/2)(cosh 1)⁴(|c₀| + 3)` for
   all `τ ∈ ℝ`; at every zero `ρ`, `‖Û(γ_ρ)‖ ≤ (cosh(3/2))⁴ / ‖ρ‖⁴`, so the `L¹` zero-series norm is
   at most `(cosh(3/2))⁴ / 16` times the total zero energy `Σ_ρ m_ρ² / ‖ρ‖²`.
4. **Effective finite-shift bounds for all `τ > 4` and fixed-threshold equivalences**
   (`abs_stationaryPacket_splineProbe_le_of_xiZeroHalfPlaneBound`,
   `abs_stationaryPacket_splineProbe_le_of_riemannHypothesis`,
   `abs_splinePrimeSum_sub_splinePolarMass_le_of_riemannHypothesis`,
   `riemannHypothesis_iff_spline_prime_sum_le_of_gt_four`,
   `xiZeroHalfPlaneBound_iff_spline_prime_sum_le_of_gt_four`): eliminating the unknown threshold `T`
   in favour of the exact support boundary `τ > 4`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped BigOperators Convolution CompactlySupported
open RHTower.WeilDeletion (unif upow unif_nonneg upow_nonneg integrable_unif integrable_upow
  integral_unif integral_upow hasCompactSupport_upow paperFT_unif paperFT_upow
  norm_paperFT_unif_le norm_paperFT_upow_le support_upow_subset)

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## Pointwise, derivative, and gauge-derivative bounds for `cubicSpline` and `splineProbe` -/

theorem unif_one_le_half (x : ℝ) : unif 1 x ≤ 1 / 2 := by
  unfold unif
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hx]; norm_num
  · rw [Set.indicator_of_notMem hx]; norm_num

theorem upow_one_le_half : ∀ (n : ℕ) (x : ℝ), upow 1 n x ≤ 1 / 2
  | 0, x => unif_one_le_half x
  | n + 1, x => by
    show (unif 1 ⋆ upow 1 n) x ≤ 1 / 2
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    have hint : Integrable fun t : ℝ => (1 / 2 : ℝ) * upow 1 n (x - t) :=
      ((integrable_upow 1 n).comp_sub_left x).const_mul (1 / 2)
    have hle : (∫ t : ℝ, unif 1 t * upow 1 n (x - t)) ≤
        ∫ t : ℝ, (1 / 2 : ℝ) * upow 1 n (x - t) := by
      refine integral_mono_of_nonneg
        (Eventually.of_forall fun t => mul_nonneg (unif_nonneg one_pos t) (upow_nonneg one_pos n _))
        hint (Eventually.of_forall fun t => ?_)
      exact mul_le_mul_of_nonneg_right (unif_one_le_half t) (upow_nonneg one_pos n _)
    calc (∫ t : ℝ, unif 1 t * upow 1 n (x - t))
        ≤ ∫ t : ℝ, (1 / 2 : ℝ) * upow 1 n (x - t) := hle
      _ = (1 / 2 : ℝ) * ∫ t : ℝ, upow 1 n (x - t) := integral_const_mul _ _
      _ = 1 / 2 := by
          rw [integral_sub_left_eq_self (fun u => upow 1 n u) volume x,
            integral_upow one_pos n, mul_one]

theorem cubicSpline_nonneg (x : ℝ) : 0 ≤ cubicSpline x :=
  upow_nonneg one_pos 3 x

theorem cubicSpline_le_half (x : ℝ) : cubicSpline x ≤ 1 / 2 :=
  upow_one_le_half 3 x

theorem hasDerivAt_cubicSpline (x : ℝ) :
    HasDerivAt cubicSpline (1 / 2 * (upow 1 2 (x + 1) - upow 1 2 (x - 1))) x := by
  have hconv : cubicSpline = fun y : ℝ =>
      1 / 2 * ((∫ t in (0 : ℝ)..y + 1, upow 1 2 t) -
        ∫ t in (0 : ℝ)..y - 1, upow 1 2 t) := by
    ext y
    have h : cubicSpline y =
        1 / (2 * 1) * ((∫ t in (0 : ℝ)..y + 1, upow 1 2 t) -
          ∫ t in (0 : ℝ)..y - 1, upow 1 2 t) :=
      unif_convolution_eq one_pos (integrable_upow 1 2) y
    rw [h]
    ring
  have hc : Continuous (upow 1 2) := (contDiff_upow one_pos 1).continuous
  have hprim : ∀ u : ℝ, HasDerivAt (fun z : ℝ => ∫ t in (0 : ℝ)..z, upow 1 2 t) (upow 1 2 u) u :=
    fun u => (hc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hd1 : HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..y + 1, upow 1 2 t) (upow 1 2 (x + 1)) x := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (hprim (x + 1)).scomp x ((hasDerivAt_id x).add_const 1)
  have hd2 : HasDerivAt (fun y : ℝ => ∫ t in (0 : ℝ)..y - 1, upow 1 2 t) (upow 1 2 (x - 1)) x := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (hprim (x - 1)).scomp x ((hasDerivAt_id x).sub_const 1)
  rw [hconv]
  exact (hd1.sub hd2).const_mul (1 / 2 : ℝ)

theorem deriv_cubicSpline_eq (x : ℝ) :
    deriv cubicSpline x = 1 / 2 * (upow 1 2 (x + 1) - upow 1 2 (x - 1)) :=
  (hasDerivAt_cubicSpline x).deriv

theorem abs_deriv_cubicSpline_le_quarter (x : ℝ) :
    |deriv cubicSpline x| ≤ 1 / 4 := by
  rw [deriv_cubicSpline_eq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h1 := upow_nonneg one_pos 2 (x + 1)
  have h2 := upow_one_le_half 2 (x + 1)
  have h3 := upow_nonneg one_pos 2 (x - 1)
  have h4 := upow_one_le_half 2 (x - 1)
  have habs : |upow 1 2 (x + 1) - upow 1 2 (x - 1)| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  linarith

theorem deriv_cubicSpline_eq_zero {v : ℝ} (hv : 4 < |v|) :
    deriv cubicSpline v = 0 := by
  have hev : cubicSpline =ᶠ[𝓝 v] (fun _ => 0) :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨{x | 4 < |x|},
      (isOpen_lt continuous_const continuous_abs).mem_nhds hv, fun x hx => cubicSpline_eq_zero hx⟩
  rw [hev.deriv_eq, deriv_const]

theorem splineProbe_nonneg (x : ℝ) : 0 ≤ splineProbe x :=
  mul_nonneg (Real.exp_pos _).le (cubicSpline_nonneg x)

theorem splineProbe_le (x : ℝ) : splineProbe x ≤ 1 / 2 * Real.exp 4 := by
  by_cases hx : 4 < |x|
  · rw [splineProbe_eq_zero hx]
    positivity
  · push Not at hx
    unfold splineProbe tiltedSource
    rw [one_mul]
    have hexp : Real.exp x ≤ Real.exp 4 := Real.exp_le_exp.mpr ((le_abs_self x).trans hx)
    have hsp := cubicSpline_le_half x
    nlinarith [Real.exp_pos x, cubicSpline_nonneg x]

theorem gaugeDerivative_splineProbe_eq (x : ℝ) :
    gaugeDerivative splineProbe x =
      Real.exp x * (deriv cubicSpline x + 1 / 2 * cubicSpline x) := by
  have hd : HasDerivAt splineProbe
      (Real.exp x * cubicSpline x + Real.exp x * deriv cubicSpline x) x := by
    have hfun : splineProbe = fun u => Real.exp u * cubicSpline u := by
      funext u; simp [splineProbe, tiltedSource]
    rw [hfun]
    exact (Real.hasDerivAt_exp x).mul (hasDerivAt_cubicSpline x).differentiableAt.hasDerivAt
  unfold gaugeDerivative
  rw [hd.deriv]
  unfold splineProbe tiltedSource
  ring

theorem gaugeDerivative_splineProbe_eq_zero {v : ℝ} (hv : 4 < |v|) :
    gaugeDerivative splineProbe v = 0 :=
  gaugeDerivative_eq_zero_of_lt_abs (fun _ h => splineProbe_eq_zero h) hv

theorem abs_gaugeDerivative_splineProbe_le (x : ℝ) :
    |gaugeDerivative splineProbe x| ≤ 1 / 2 * Real.exp 4 := by
  by_cases hx : 4 < |x|
  · rw [gaugeDerivative_splineProbe_eq_zero hx, abs_zero]
    positivity
  · push Not at hx
    rw [gaugeDerivative_splineProbe_eq, abs_mul, abs_of_pos (Real.exp_pos x)]
    have hexp : Real.exp x ≤ Real.exp 4 := Real.exp_le_exp.mpr ((le_abs_self x).trans hx)
    have hd := abs_deriv_cubicSpline_le_quarter x
    have hc0 := cubicSpline_nonneg x
    have hc1 := cubicSpline_le_half x
    have hsum : |deriv cubicSpline x + 1 / 2 * cubicSpline x| ≤ 1 / 2 := by
      calc |deriv cubicSpline x + 1 / 2 * cubicSpline x|
          ≤ |deriv cubicSpline x| + |1 / 2 * cubicSpline x| := abs_add_le _ _
        _ = |deriv cubicSpline x| + 1 / 2 * cubicSpline x := by
            rw [abs_of_nonneg (mul_nonneg (by norm_num) hc0)]
        _ ≤ 1 / 4 + 1 / 2 * (1 / 2) := by linarith
        _ = 1 / 2 := by norm_num
    nlinarith [Real.exp_pos x, abs_nonneg (deriv cubicSpline x + 1 / 2 * cubicSpline x)]

theorem integral_abs_gaugeDerivative_splineProbe_le :
    (∫ u : ℝ, |gaugeDerivative splineProbe u|) ≤ 4 * Real.exp 4 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-4 : ℝ) 4) fun u hu => by
    simp only [mem_Icc, not_and_or, not_le] at hu
    have h4 : 4 < |u| := by
      rcases hu with hlt | hgt
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl hgt)
    rw [gaugeDerivative_splineProbe_eq_zero h4, abs_zero]]
  have hle : (∫ u in Icc (-4 : ℝ) 4, |gaugeDerivative splineProbe u|) ≤
      ∫ _u in Icc (-4 : ℝ) 4, (1 / 2 * Real.exp 4 : ℝ) := by
    refine setIntegral_mono_on
      ((continuous_gaugeDerivative (contDiff_splineProbe.of_le (by norm_num))).abs.integrableOn_Icc)
      (integrableOn_const (by norm_num)) measurableSet_Icc fun u _ =>
        abs_gaugeDerivative_splineProbe_le u
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul] at hle
  linarith

/-- The `C_c(ℝ, ℝ)`bundled explicit spline probe. -/
def splineProbeCc : C_c(ℝ, ℝ) :=
  ⟨⟨splineProbe, contDiff_splineProbe.continuous⟩, hasCompactSupport_splineProbe⟩

@[simp]
theorem splineProbeCc_apply (u : ℝ) : splineProbeCc u = splineProbe u := rfl

theorem autocorr_splineProbe_zero_le :
    autocorr splineProbe 0 ≤ 2 * Real.exp 8 := by
  change autocorr splineProbeCc 0 ≤ 2 * Real.exp 8
  rw [← integral_sq_eq_autocorr_zero splineProbeCc,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (-4 : ℝ) 4) fun u hu => by
      simp only [mem_Icc, not_and_or, not_le] at hu
      have h4 : 4 < |u| := by
        rcases hu with hlt | hgt
        · exact lt_abs.mpr (Or.inr (by linarith))
        · exact lt_abs.mpr (Or.inl hgt)
      simp [splineProbe_eq_zero h4]]
  have hle : (∫ u in Icc (-4 : ℝ) 4, splineProbeCc u ^ 2) ≤
      ∫ _u in Icc (-4 : ℝ) 4, ((1 / 2 * Real.exp 4) ^ 2 : ℝ) := by
    refine setIntegral_mono_on
      ((splineProbeCc.continuous.pow 2).integrableOn_Icc)
      (integrableOn_const (by norm_num)) measurableSet_Icc fun u _ => ?_
    exact pow_le_pow_left₀ (splineProbe_nonneg u) (splineProbe_le u) 2
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul] at hle
  have hexp : (1 / 2 * Real.exp 4) ^ 2 = 1 / 4 * Real.exp 8 := by
    rw [mul_pow, sq (Real.exp 4), ← Real.exp_add]
    norm_num
  linarith

/-! ## Exact local Chebyshev gauge representation and finite-shift error bounds -/

/-- **Local gauge representation of `stationaryPacket splineProbe τ`.** For every shift `τ > 4`,
the stationary packet of the explicit spline probe depends only on the values of `Ẽ(t)` in the
local window `[τ − 4, τ + 4]`:
`P_U(τ) = −∫_{τ−4}^{τ+4} e^{−t/2} U(t − τ) dt − ∫_{τ−4}^{τ+4} Ẽ(t) (U' − U/2)(t − τ) dt`. -/
theorem stationaryPacket_splineProbe_eq_local_gauge {τ : ℝ} (hτ : 4 < τ) :
    stationaryPacket splineProbe τ =
      -(∫ t in Icc (τ - 4) (τ + 4), Real.exp (-t / 2) * splineProbe (-τ + t)) -
        ∫ t in Icc (τ - 4) (τ + 4),
          normalizedLogError t * gaugeDerivative splineProbe (-τ + t) := by
  obtain ⟨N, hN1, -⟩ := exists_cutoff_between (a := τ + 4) (by linarith)
  have hF1 : ContDiff ℝ 1 (splineProbeCc : ℝ → ℝ) := contDiff_splineProbe.of_le (by norm_num)
  have hgauge : stationaryPacket splineProbe τ =
      forwardResidual splineProbe N (-τ) - chebyshevGaugeConvolution splineProbe N (-τ) :=
    stationaryPacket_eq_gauge splineProbeCc hF1 (by norm_num : (0 : ℝ) ≤ 4)
      (fun _ hv => splineProbe_eq_zero hv) hN1
  rw [hgauge]
  have hsub : Icc (τ - 4) (τ + 4) ⊆ Icc 0 (cutoff N) :=
    Icc_subset_Icc (by linarith) hN1.le
  have hres : forwardResidual splineProbe N (-τ) =
      -∫ t in Icc (τ - 4) (τ + 4), Real.exp (-t / 2) * splineProbe (-τ + t) := by
    unfold forwardResidual
    rw [splineProbe_eq_zero (lt_abs.mpr (Or.inr (by linarith))), zero_sub]
    congr 1
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub fun t ht => ?_
    have h4 : 4 < |-τ + t| := by
      have ht2 := ht.2
      simp only [mem_Icc, not_and_or, not_le] at ht2
      rcases ht2 with hlt | hgt
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl (by linarith))
    rw [splineProbe_eq_zero h4, mul_zero]
  have hconv : chebyshevGaugeConvolution splineProbe N (-τ) =
      ∫ t in Icc (τ - 4) (τ + 4),
        normalizedLogError t * gaugeDerivative splineProbe (-τ + t) := by
    unfold chebyshevGaugeConvolution
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc hsub fun t ht => ?_
    have h4 : 4 < |-τ + t| := by
      have ht2 := ht.2
      simp only [mem_Icc, not_and_or, not_le] at ht2
      rcases ht2 with hlt | hgt
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl (by linarith))
    rw [gaugeDerivative_splineProbe_eq_zero h4, mul_zero]
  rw [hres, hconv]

/-- **Unconditional finite-shift Chebyshev error bound for `stationaryPacket splineProbe τ`.**
For every `τ > 4`,
`|stationaryPacket splineProbe τ| ≤ 4 e^{2 − τ/2} + (1/2) e⁴ ∫_{τ−4}^{τ+4} |Ẽ(t)| dt`. -/
theorem abs_stationaryPacket_splineProbe_le_local_chebyshev {τ : ℝ} (hτ : 4 < τ) :
    |stationaryPacket splineProbe τ| ≤
      4 * Real.exp (2 - τ / 2) +
        1 / 2 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |normalizedLogError t| := by
  rw [stationaryPacket_splineProbe_eq_local_gauge hτ]
  set I₁ := ∫ t in Icc (τ - 4) (τ + 4), Real.exp (-t / 2) * splineProbe (-τ + t)
  set I₂ := ∫ t in Icc (τ - 4) (τ + 4),
    normalizedLogError t * gaugeDerivative splineProbe (-τ + t)
  have hI₁0 : 0 ≤ I₁ := setIntegral_nonneg measurableSet_Icc fun t _ =>
    mul_nonneg (Real.exp_pos _).le (splineProbe_nonneg _)
  have hI₁_le : I₁ ≤ 4 * Real.exp (2 - τ / 2) := by
    have hle : I₁ ≤ ∫ _t in Icc (τ - 4) (τ + 4), (1 / 2 * Real.exp (2 - τ / 2) : ℝ) := by
      refine setIntegral_mono_on
        (((Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul
          (contDiff_splineProbe.continuous.comp (continuous_const.add continuous_id))).integrableOn_Icc)
        (integrableOn_const (by norm_num)) measurableSet_Icc fun t ht => ?_
      unfold splineProbe tiltedSource
      rw [one_mul, ← mul_assoc, ← Real.exp_add]
      have hexp : Real.exp (-t / 2 + (-τ + t)) ≤ Real.exp (2 - τ / 2) :=
        Real.exp_le_exp.mpr (by linarith [ht.2])
      have hsp := cubicSpline_le_half (-τ + t)
      nlinarith [Real.exp_pos (-t / 2 + (-τ + t)), cubicSpline_nonneg (-τ + t)]
    rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at hle
    linarith
  have hI₂_le : |I₂| ≤
      1 / 2 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |normalizedLogError t| := by
    have hint_abs : IntegrableOn (fun t => |normalizedLogError t|) (Icc (τ - 4) (τ + 4)) :=
      ((integrableOn_normalizedLogError_Icc (τ + 4)).mono_set
        (Icc_subset_Icc (by linarith) le_rfl)).norm
    calc |I₂| ≤ ∫ t in Icc (τ - 4) (τ + 4),
          |normalizedLogError t * gaugeDerivative splineProbe (-τ + t)| := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun t => normalizedLogError t * gaugeDerivative splineProbe (-τ + t))
      _ ≤ ∫ t in Icc (τ - 4) (τ + 4),
          (1 / 2 * Real.exp 4) * |normalizedLogError t| := by
          refine setIntegral_mono_on ?_ (hint_abs.const_mul _) measurableSet_Icc fun t _ => ?_
          · refine (hint_abs.const_mul (1 / 2 * Real.exp 4)).mono'
              ((measurable_normalizedLogError.mul
                ((continuous_gaugeDerivative (contDiff_splineProbe.of_le (by norm_num))).comp
                  (continuous_const.add continuous_id)).measurable).abs.aestronglyMeasurable) ?_
            rw [ae_restrict_iff' measurableSet_Icc]
            refine Eventually.of_forall fun t _ => ?_
            rw [Real.norm_eq_abs, abs_abs, abs_mul, mul_comm (1 / 2 * Real.exp 4)]
            exact mul_le_mul_of_nonneg_left (abs_gaugeDerivative_splineProbe_le _) (abs_nonneg _)
          · rw [abs_mul, mul_comm (1 / 2 * Real.exp 4)]
            exact mul_le_mul_of_nonneg_left (abs_gaugeDerivative_splineProbe_le _) (abs_nonneg _)
      _ = 1 / 2 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |normalizedLogError t| :=
          integral_const_mul _ _
  calc |-I₁ - I₂| ≤ |-I₁| + |I₂| := abs_sub _ _
    _ = I₁ + |I₂| := by rw [abs_neg, abs_of_nonneg hI₁0]
    _ ≤ 4 * Real.exp (2 - τ / 2) +
        1 / 2 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |normalizedLogError t| :=
      add_le_add hI₁_le hI₂_le

/-- **Unconditional finite-shift Chebyshev error bound for the spline prime sum.**
For every `τ > 4`,
`|splinePrimeSum τ − splinePolarMass τ| ≤ 4 e^{2 + τ/2} + (1/2) e^{4 + τ} ∫_{τ−4}^{τ+4} |Ẽ(t)| dt`. -/
theorem abs_splinePrimeSum_sub_splinePolarMass_le_local_chebyshev {τ : ℝ} (hτ : 4 < τ) :
    |splinePrimeSum τ - splinePolarMass τ| ≤
      4 * Real.exp (2 + τ / 2) +
        1 / 2 * Real.exp (4 + τ) * ∫ t in Icc (τ - 4) (τ + 4), |normalizedLogError t| := by
  rw [← exp_mul_stationaryPacket_splineProbe τ, abs_mul, abs_of_pos (Real.exp_pos τ)]
  have h := mul_le_mul_of_nonneg_left
    (abs_stationaryPacket_splineProbe_le_local_chebyshev hτ) (Real.exp_pos τ).le
  have he1 : Real.exp τ * (4 * Real.exp (2 - τ / 2)) = 4 * Real.exp (2 + τ / 2) := by
    rw [mul_left_comm, ← Real.exp_add, show τ + (2 - τ / 2) = 2 + τ / 2 by ring]
  have he2 : Real.exp τ * (1 / 2 * Real.exp 4) = 1 / 2 * Real.exp (4 + τ) := by
    rw [mul_left_comm, ← Real.exp_add, add_comm τ 4]
  rw [mul_add, ← mul_assoc (Real.exp τ) (1 / 2 * Real.exp 4), he1, he2] at h
  exact h

/-- **Quantitative windowed `L²` packet bound for `splineProbe`.** For every `L ≥ 4`,
`∫_4^L P_U(τ)² dτ ≤ 32 e⁸ ∫_0^{L+7} Ẽ(t)² dt + 40 e⁸`. -/
theorem integral_sq_stationaryPacket_splineProbe_le {L : ℝ} (hL : 4 ≤ L) :
    (∫ τ in (4 : ℝ)..L, stationaryPacket splineProbe τ ^ 2) ≤
      32 * Real.exp 8 * (∫ t in Icc 0 (L + 7), normalizedLogError t ^ 2) +
        40 * Real.exp 8 := by
  have h : (∫ τ in (4 : ℝ)..L, stationaryPacket splineProbe τ ^ 2) ≤
      (1 + 1) * ((∫ u, |gaugeDerivative splineProbe u|) ^ 2 *
          ∫ t in Icc 0 (L + 4 + 3), normalizedLogError t ^ 2) +
        (1 + 1 / 1) * (10 * autocorr splineProbe 0) :=
    integral_sq_packet_le_of_compact splineProbeCc contDiff_splineProbe
      (w := 4) (by norm_num) (fun _ hv => splineProbe_eq_zero hv) (η := 1) one_pos hL
  have hG : (∫ u, |gaugeDerivative splineProbe u|) ^ 2 ≤ 16 * Real.exp 8 := by
    have h1 := integral_abs_gaugeDerivative_splineProbe_le
    have h0 : 0 ≤ ∫ u, |gaugeDerivative splineProbe u| := integral_nonneg fun _ => abs_nonneg _
    have hsq := pow_le_pow_left₀ h0 h1 2
    have hexp : (4 * Real.exp 4) ^ 2 = 16 * Real.exp 8 := by
      rw [mul_pow, sq (Real.exp 4), ← Real.exp_add]; norm_num
    linarith
  have hA := autocorr_splineProbe_zero_le
  have hI0 : 0 ≤ ∫ t in Icc 0 (L + 7), normalizedLogError t ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  rw [show L + 4 + 3 = L + 7 by ring] at h
  have hGI := mul_le_mul_of_nonneg_right hG hI0
  linarith

/-! ## Explicit spectral bounds on `Û(r)`, `packetArchTail splineProbe`, and the zero series -/

/-- On the real axis, `‖Û(r)‖ ≤ (cosh 1)⁴ / (1 + r²)²` for every `r ∈ ℝ`. -/
theorem norm_paperFT_splineProbe_ofReal_le (r : ℝ) :
    ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r‖ ≤
      Real.cosh 1 ^ 4 / (1 + r ^ 2) ^ 2 := by
  unfold splineProbe
  rw [paperFT_tiltedSource, cubicSpline]
  have hne : (r : ℂ) - I * 1 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have h := norm_paperFT_upow_le one_pos 3 hne
  have him : ((r : ℂ) - I * 1).im = -1 := by simp
  have hcosh : Real.cosh (1 * ((r : ℂ) - I * 1).im) = Real.cosh 1 := by
    rw [him, one_mul, Real.cosh_neg]
  have hnorm_sq : (1 * ‖(r : ℂ) - I * 1‖) ^ 4 = (1 + r ^ 2) ^ 2 := by
    rw [one_mul, show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, ofReal_re, I_re, I_im, mul_one, sub_zero, sub_im, ofReal_im, zero_sub]
    ring
  rw [hcosh, div_pow, hnorm_sq] at h
  exact h

/-- Explicit archimedean tail bound for `splineProbe`:
`splineArchBound = (1/2) (cosh 1)⁴ (|digammaVerticalGrowthConst (1/4) + log π| + 3)`. -/
def splineArchBound : ℝ :=
  1 / 2 * Real.cosh 1 ^ 4 *
    (|_root_.RHTower.digammaVerticalGrowthConst (1 / 4) + Real.log Real.pi| + 3)

theorem splineArchBound_nonneg : 0 ≤ splineArchBound := by
  unfold splineArchBound
  positivity

/-- For every shift `τ ∈ ℝ`, `‖packetArchTail splineProbe τ‖ ≤ splineArchBound`. -/
theorem norm_packetArchTail_splineProbe_le (τ : ℝ) :
    ‖packetArchTail splineProbe τ‖ ≤ splineArchBound := by
  set c₀ := _root_.RHTower.digammaVerticalGrowthConst (1 / 4) + Real.log Real.pi
  have hpt : ∀ r : ℝ, ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r *
      (Zeta23.EF.gammaBracket r : ℂ)‖ ≤
      Real.cosh 1 ^ 4 * (|c₀| + 3) * (1 + r ^ 2)⁻¹ := by
    intro r
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hU := norm_paperFT_splineProbe_ofReal_le r
    have hγ := _root_.RHTower.WeilSpectral.abs_gammaBracket_le_sqrt r
    have hsqrt : Real.sqrt (1 + |r|) ≤ 1 + |r| := by
      refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
      nlinarith [abs_nonneg r]
    have habs : 1 + |r| ≤ 3 / 2 * (1 + r ^ 2) := by
      nlinarith [sq_abs r, sq_nonneg (|r| - 1)]
    have hγ' : |Zeta23.EF.gammaBracket r| ≤ (|c₀| + 3) * (1 + r ^ 2) := by
      have hc₀ : c₀ ≤ |c₀| * (1 + r ^ 2) :=
        (le_abs_self c₀).trans (le_mul_of_one_le_right (abs_nonneg c₀) (by nlinarith [sq_nonneg r]))
      linarith
    have hpos : 0 < 1 + r ^ 2 := by positivity
    calc ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r‖ * |Zeta23.EF.gammaBracket r|
        ≤ (Real.cosh 1 ^ 4 / (1 + r ^ 2) ^ 2) * ((|c₀| + 3) * (1 + r ^ 2)) :=
          mul_le_mul hU hγ' (abs_nonneg _) (by positivity)
      _ = Real.cosh 1 ^ 4 * (|c₀| + 3) * (1 + r ^ 2)⁻¹ := by
          field_simp
  have hint1 : Integrable fun r : ℝ =>
      ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r * (Zeta23.EF.gammaBracket r : ℂ)‖ :=
    (integrable_paperFT_mul_gammaBracket contDiff_splineProbe fun _ hv => splineProbe_eq_zero hv).norm
  have hint2 : Integrable fun r : ℝ =>
      Real.cosh 1 ^ 4 * (|c₀| + 3) * (1 + r ^ 2)⁻¹ :=
    integrable_inv_one_add_sq.const_mul _
  have hint_le : (∫ r : ℝ, ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r *
      (Zeta23.EF.gammaBracket r : ℂ)‖) ≤
      Real.cosh 1 ^ 4 * (|c₀| + 3) * Real.pi := by
    calc (∫ r : ℝ, ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r *
          (Zeta23.EF.gammaBracket r : ℂ)‖)
        ≤ ∫ r : ℝ, Real.cosh 1 ^ 4 * (|c₀| + 3) * (1 + r ^ 2)⁻¹ :=
          integral_mono hint1 hint2 hpt
      _ = Real.cosh 1 ^ 4 * (|c₀| + 3) * Real.pi := by
          rw [integral_const_mul, integral_univ_inv_one_add_sq]
  calc ‖packetArchTail splineProbe τ‖
      ≤ 1 / (2 * Real.pi) * ∫ r : ℝ, ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) r *
          (Zeta23.EF.gammaBracket r : ℂ)‖ := norm_packetArchTail_le splineProbe τ
    _ ≤ 1 / (2 * Real.pi) * (Real.cosh 1 ^ 4 * (|c₀| + 3) * Real.pi) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = splineArchBound := by
        dsimp only [splineArchBound, c₀]
        have hπ : Real.pi ≠ 0 := Real.pi_pos.ne'
        field_simp

/-- Every nontrivial zero `ρ ∈ 𝒵` has `4 < |(ρ : ℂ).im|` and `4 < ‖(ρ : ℂ)‖`. -/
theorem four_lt_norm_carrier (ρ : 𝒵) : 4 < ‖(ρ : ℂ)‖ := by
  have h := _root_.RHTower.four_lt_abs_zeroOrdinate
    (firstCopy (xiDivisorSupportEquivCarrier.symm ρ))
  have heq : _root_.RHTower.zeroOrdinate (firstCopy (xiDivisorSupportEquivCarrier.symm ρ)) =
      (ρ : ℂ).im := rfl
  rw [heq] at h
  exact h.trans_le (Complex.abs_im_le_norm (ρ : ℂ))

/-- At every nontrivial zero `ρ ∈ 𝒵`, `‖Û(γ_ρ)‖ ≤ (cosh(3/2))⁴ / ‖(ρ : ℂ)‖⁴`. -/
theorem norm_paperFT_splineProbe_gammaOf_le (ρ : 𝒵) :
    ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) (Zeta23.gammaOf ρ)‖ ≤
      Real.cosh (3 / 2) ^ 4 / ‖(ρ : ℂ)‖ ^ 4 := by
  unfold splineProbe
  rw [paperFT_tiltedSource, cubicSpline]
  have hre0 : 0 < (ρ : ℂ).re := ρ.2.2.1
  have hre1 : (ρ : ℂ).re < 1 := ρ.2.2.2
  have hId : I * (Zeta23.gammaOf ρ - I * 1) = (ρ : ℂ) + 1 / 2 := by
    rw [mul_sub, I_mul_gammaOf, zeroShift]
    have : I * (I * 1) = -1 := by rw [mul_one, Complex.I_mul_I]
    rw [this]; ring
  have hnorm_eq : ‖Zeta23.gammaOf ρ - I * 1‖ = ‖(ρ : ℂ) + 1 / 2‖ := by
    have := congrArg norm hId
    rwa [norm_mul, Complex.norm_I, one_mul] at this
  have hnorm_le : ‖(ρ : ℂ)‖ ≤ ‖(ρ : ℂ) + 1 / 2‖ := by
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
      Complex.normSq_apply, Complex.normSq_apply]
    simp only [add_re, div_ofNat_re, one_re, add_im, div_ofNat_im, one_im, zero_div, add_zero]
    nlinarith
  have hρ4 := four_lt_norm_carrier ρ
  have hne : Zeta23.gammaOf ρ - I * 1 ≠ 0 := by
    intro h0
    have : ‖Zeta23.gammaOf ρ - I * 1‖ = 0 := by rw [h0, norm_zero]
    linarith [hnorm_eq, hnorm_le, hρ4]
  have h := norm_paperFT_upow_le one_pos 3 hne
  have him : (Zeta23.gammaOf ρ - I * 1).im = -((ρ : ℂ).re + 1 / 2) := by
    have hre_id := congrArg Complex.re hId
    simp only [mul_re, I_re, zero_mul, I_im, one_mul, zero_sub, add_re, div_ofNat_re,
      one_re] at hre_id
    linarith
  have hcosh : Real.cosh (Zeta23.gammaOf ρ - I * 1).im ≤ Real.cosh (3 / 2) := by
    rw [him, Real.cosh_neg, Real.cosh_le_cosh]
    rw [abs_of_pos (by linarith), abs_of_pos (by norm_num)]
    linarith
  rw [one_mul, one_mul, hnorm_eq, show (3 + 1 : ℕ) = 4 by rfl] at h
  refine h.trans ?_
  rw [div_pow]
  refine div_le_div₀ (by positivity) (pow_le_pow_left₀ (Real.cosh_pos _).le hcosh 4)
    (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hnorm_le 4)

/-- At every nontrivial zero `ρ ∈ 𝒵`,
`‖packetCoeff splineProbe ρ‖ ≤ ((cosh(3/2))⁴ / 16) * m_ρ² / ‖ρ‖²`. -/
theorem norm_packetCoeff_splineProbe_le_zeroEnergy (ρ : 𝒵) :
    ‖packetCoeff splineProbe ρ‖ ≤
      (Real.cosh (3 / 2) ^ 4 / 16) *
        ((Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2) := by
  unfold packetCoeff
  rw [norm_mul, Complex.norm_natCast]
  have hm1 : (1 : ℝ) ≤ (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) := by
    exact_mod_cast Zeta23.zetaZeroConfig.one_le_mult ρ ρ.2
  have hm_sq : (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) ≤
      (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) ^ 2 := by nlinarith
  have hρ4 := four_lt_norm_carrier ρ
  have hρ16 : 16 ≤ ‖(ρ : ℂ)‖ ^ 2 := by nlinarith
  have hU := norm_paperFT_splineProbe_gammaOf_le ρ
  calc (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) *
        ‖Zeta23.paperFT (fun u => (splineProbe u : ℂ)) (Zeta23.gammaOf ρ)‖
      ≤ (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) ^ 2 *
          (Real.cosh (3 / 2) ^ 4 / ‖(ρ : ℂ)‖ ^ 4) :=
        mul_le_mul hm_sq hU (norm_nonneg _) (by positivity)
    _ = Real.cosh (3 / 2) ^ 4 * (1 / ‖(ρ : ℂ)‖ ^ 2) *
          ((Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2) := by
        field_simp
    _ ≤ (Real.cosh (3 / 2) ^ 4 / 16) *
          ((Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [div_eq_mul_one_div (Real.cosh (3 / 2) ^ 4)]
        exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by norm_num) hρ16) (by positivity)

/-- Under RH, the `L¹` zero-series norm of `splineProbe` is at most
`((cosh(3/2))⁴ / 16) * totalZeroEnergy`. -/
theorem tsum_norm_packetCoeff_splineProbe_le_totalZeroEnergy (hRH : RiemannHypothesis) :
    (∑' ρ : 𝒵, ‖packetCoeff splineProbe ρ‖) ≤
      (Real.cosh (3 / 2) ^ 4 / 16) * totalZeroEnergy := by
  have h1 := summable_norm_packetCoeff contDiff_splineProbe hasCompactSupport_splineProbe
  have h2 := (summable_zetaZeroEnergy_of_riemannHypothesis hRH).mul_left (Real.cosh (3 / 2) ^ 4 / 16)
  unfold totalZeroEnergy
  rw [← tsum_mul_left]
  exact h1.tsum_le_tsum norm_packetCoeff_splineProbe_le_zeroEnergy h2

/-! ## Effective finite-shift bounds for all `τ > 4` and fixed-threshold equivalences -/

/-- **Effective finite-shift bound under a zero-width bound `β`.** If every zero has
`Re ρ ≤ 1/2 + β` (`β ≥ 0`), then for EVERY shift `τ > 4`,
`|stationaryPacket splineProbe τ| ≤ splineArchBound + (Σ_ρ ‖packetCoeff splineProbe ρ‖) e^{βτ}`. -/
theorem abs_stationaryPacket_splineProbe_le_of_xiZeroHalfPlaneBound {β : ℝ} (hβ : 0 ≤ β)
    (hXi : _root_.RHTower.XiZeroHalfPlaneBound β) {τ : ℝ} (hτ : 4 < τ) :
    |stationaryPacket splineProbe τ| ≤
      splineArchBound + (∑' ρ : 𝒵, ‖packetCoeff splineProbe ρ‖) * Real.exp (β * τ) := by
  have hc := summable_norm_packetCoeff contDiff_splineProbe hasCompactSupport_splineProbe
  have hmem := (xiZeroHalfPlaneBound_iff_forall_mem hβ).mp hXi
  have hτ0 : 0 ≤ τ := by linarith
  have hterm : ∀ ρ : 𝒵, ‖packetCoeff splineProbe ρ * cexp (zeroShift ρ * τ)‖ ≤
      ‖packetCoeff splineProbe ρ‖ * Real.exp (β * τ) := fun ρ => by
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have : (zeroShift ρ * τ).re = ((ρ : ℂ).re - 1 / 2) * τ := by simp [zeroShift]
    rw [this]
    exact mul_le_mul_of_nonneg_right (by linarith [hmem ρ]) hτ0
  have hdom : Summable fun ρ : 𝒵 => ‖packetCoeff splineProbe ρ‖ * Real.exp (β * τ) :=
    hc.mul_right _
  have hG : ‖zeroSeries (packetCoeff splineProbe) τ‖ ≤
      (∑' ρ : 𝒵, ‖packetCoeff splineProbe ρ‖) * Real.exp (β * τ) := by
    rw [zeroSeries, ← tsum_mul_right]
    exact (norm_tsum_le_tsum_norm (hdom.of_nonneg_of_le (fun _ => norm_nonneg _) hterm)).trans
      (Summable.tsum_le_tsum hterm (hdom.of_nonneg_of_le (fun _ => norm_nonneg _) hterm) hdom)
  rw [← Real.norm_eq_abs, ← Complex.norm_real,
    stationaryPacket_eq contDiff_splineProbe hasCompactSupport_splineProbe
      (by norm_num : (0 : ℝ) ≤ 4) (fun _ hv => splineProbe_eq_zero hv) hτ]
  calc ‖packetArchTail splineProbe τ - zeroSeries (packetCoeff splineProbe) τ‖
      ≤ ‖packetArchTail splineProbe τ‖ + ‖zeroSeries (packetCoeff splineProbe) τ‖ :=
        norm_sub_le _ _
    _ ≤ splineArchBound + (∑' ρ : 𝒵, ‖packetCoeff splineProbe ρ‖) * Real.exp (β * τ) :=
        add_le_add (norm_packetArchTail_splineProbe_le τ) hG

/-- **Effective finite-shift bound on `stationaryPacket splineProbe τ` under RH.**
For every shift `τ > 4`,
`|stationaryPacket splineProbe τ| ≤ splineArchBound + ((cosh(3/2))⁴ / 16) * totalZeroEnergy`. -/
theorem abs_stationaryPacket_splineProbe_le_of_riemannHypothesis (hRH : RiemannHypothesis)
    {τ : ℝ} (hτ : 4 < τ) :
    |stationaryPacket splineProbe τ| ≤
      splineArchBound + (Real.cosh (3 / 2) ^ 4 / 16) * totalZeroEnergy := by
  have hXi := _root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mp hRH
  have h := abs_stationaryPacket_splineProbe_le_of_xiZeroHalfPlaneBound le_rfl hXi hτ
  rw [zero_mul, Real.exp_zero, mul_one] at h
  exact h.trans (add_le_add le_rfl (tsum_norm_packetCoeff_splineProbe_le_totalZeroEnergy hRH))

/-- **Effective finite-shift bound on the spline prime sum under RH.**
For every shift `τ > 4`,
`|splinePrimeSum τ − splinePolarMass τ| ≤ (splineArchBound + ((cosh(3/2))⁴ / 16) * totalZeroEnergy) e^τ`. -/
theorem abs_splinePrimeSum_sub_splinePolarMass_le_of_riemannHypothesis (hRH : RiemannHypothesis)
    {τ : ℝ} (hτ : 4 < τ) :
    |splinePrimeSum τ - splinePolarMass τ| ≤
      (splineArchBound + (Real.cosh (3 / 2) ^ 4 / 16) * totalZeroEnergy) * Real.exp τ := by
  rw [← exp_mul_stationaryPacket_splineProbe τ, abs_mul, abs_of_pos (Real.exp_pos τ), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (abs_stationaryPacket_splineProbe_le_of_riemannHypothesis hRH hτ) (Real.exp_pos τ).le

/-- **Fixed-threshold RH equivalence for the spline prime sum.** RH holds if and only if there is
a constant `K` such that for all `τ > 4` (right above the support radius `4` of `B`),
`splinePrimeSum τ ≤ splinePolarMass τ + K e^τ`. -/
theorem riemannHypothesis_iff_spline_prime_sum_le_of_gt_four :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ τ : ℝ, 4 < τ →
      splinePrimeSum τ ≤ splinePolarMass τ + K * Real.exp τ := by
  constructor
  · intro hRH
    refine ⟨splineArchBound + (Real.cosh (3 / 2) ^ 4 / 16) * totalZeroEnergy, fun τ hτ => ?_⟩
    have h := (le_abs_self _).trans
      (abs_splinePrimeSum_sub_splinePolarMass_le_of_riemannHypothesis hRH hτ)
    linarith
  · rintro ⟨K, hK⟩
    exact riemannHypothesis_iff_spline_prime_sum_le.mpr
      ⟨5, K, fun τ hτ => hK τ (by linarith)⟩

/-- **Fixed-threshold zero-width equivalence for the spline prime sum.** For `β ≥ 0`, every zero
has `Re ρ ≤ 1/2 + β` if and only if there is a constant `K` such that for all `τ > 4`,
`splinePrimeSum τ ≤ splinePolarMass τ + K e^{(1 + β)τ}`. -/
theorem xiZeroHalfPlaneBound_iff_spline_prime_sum_le_of_gt_four {β : ℝ} (hβ : 0 ≤ β) :
    _root_.RHTower.XiZeroHalfPlaneBound β ↔ ∃ K : ℝ, ∀ τ : ℝ, 4 < τ →
      splinePrimeSum τ ≤ splinePolarMass τ + K * Real.exp ((1 + β) * τ) := by
  constructor
  · intro hXi
    refine ⟨splineArchBound + ∑' ρ : 𝒵, ‖packetCoeff splineProbe ρ‖, fun τ hτ => ?_⟩
    have h := (le_abs_self _).trans
      (abs_stationaryPacket_splineProbe_le_of_xiZeroHalfPlaneBound hβ hXi hτ)
    have hτ0 : 0 ≤ τ := by linarith
    have he : 1 ≤ Real.exp (β * τ) := Real.one_le_exp (mul_nonneg hβ hτ0)
    have hA : 0 ≤ splineArchBound := splineArchBound_nonneg
    have hP : stationaryPacket splineProbe τ ≤
        (splineArchBound + ∑' ρ : 𝒵, ‖packetCoeff splineProbe ρ‖) * Real.exp (β * τ) := by
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hP (Real.exp_pos τ).le
    rw [exp_mul_stationaryPacket_splineProbe τ] at hm
    have hexp : Real.exp τ *
        ((splineArchBound + ∑' ρ : 𝒵, ‖packetCoeff splineProbe ρ‖) * Real.exp (β * τ)) =
        (splineArchBound + ∑' ρ : 𝒵, ‖packetCoeff splineProbe ρ‖) * Real.exp ((1 + β) * τ) := by
      rw [mul_left_comm, ← Real.exp_add, show τ + β * τ = (1 + β) * τ by ring]
    linarith
  · rintro ⟨K, hK⟩
    exact (xiZeroHalfPlaneBound_iff_spline_prime_sum_le hβ).mpr
      ⟨5, K, fun τ hτ => hK τ (by linarith)⟩

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
