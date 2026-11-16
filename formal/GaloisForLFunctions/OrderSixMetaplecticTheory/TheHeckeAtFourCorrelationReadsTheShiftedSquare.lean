import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeAtFourCorrelationHasTheSquareMultiplier
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheSquareOfTheSourceThetaUnfolds

/-!
# The Hecke-at-four correlation reads the shifted square

For the projected theta function `θ_s` (Fourier series `Σ_h b(v, h) e(ξ_h z)`, `b(v, 0) = c v^{2/3}`), the
Hecke-at-four correlation `F(w) = θ_s(Aw) θ_s(A⁻¹w)` at `(2u, v)` is `θ_s(4u, 2v) θ_s(u, v/2)`. A cross-Parseval
identity on the period parallelogram (`integral_cuspCharacterSeries_four_mul`) gives its constant term
(`integral_sourceFourCorrelation`):

`∫_P F(2u, v) du = |P| Σ_h b(2v, h) b(v/2, −4h)`,

with `b(2v, 0) b(v/2, 0) = c² v^{4/3}` (`sourceAmplitude_four_zero`) and, for `h ≠ 0`,
`b(2v, h) b(v/2, −4h) = T_s(h) T_s(−4h) v² K_{1/3}(8π|ξ_h| v)²` (`sourceAmplitude_four_shift`): the correlation grows
like `θ_s²` and reads the shifted square `Σ_h T_s(h) T_s(−4h)` at the doubled frequency `2ξ_h`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover

theorem cuspFrequency_mul_four (h : O) : cuspFrequency (4 * h) = 4 * cuspFrequency h := by
  unfold cuspFrequency
  rw [map_mul, map_ofNat]
  ring

theorem four_ne_zero_O : (4 : O) ≠ 0 := by
  intro h
  have h' := congrArg ringComplex h
  rw [map_ofNat, map_zero] at h'
  norm_num at h'

/-- `A·(z, v) = (2z, 2v)`. -/
theorem fourDilation_upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) :
    fourDilation • upperPoint z v hv = upperPoint (2 * z) (2 * v) (by positivity) := by
  rw [fourDilation, complexDiagonal_action]
  apply upperPoint_congr
  · rw [sqrtTwo_sq]
  · rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- `A⁻¹·(z, v) = (z/2, v/2)`. -/
theorem fourContraction_upperPoint (z : ℂ) (v : ℝ) (hv : 0 < v) :
    fourContraction • upperPoint z v hv = upperPoint (z / 2) (v / 2) (by positivity) := by
  rw [fourContraction, complexDiagonal_action]
  apply upperPoint_congr
  · rw [inv_pow, sqrtTwo_sq]
    ring
  · rw [map_inv₀, Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring

/-- **Cross-Parseval on `P`.** `∫_P S_a(4u) S_b(u) du = |P| Σ_h a_h b_{−4h}`. -/
theorem integral_cuspCharacterSeries_four_mul (a b : O → ℂ) (ha : Summable (fun h => ‖a h‖))
    (hb : Summable (fun h => ‖b h‖)) :
    ∫ u in periodDomain, cuspCharacterSeries a (4 * u) * cuspCharacterSeries b u =
      periodArea * ∑' h : O, a h * b (-(4 * h)) := by
  letI : Countable O := Coordinates.coordinateEquiv.injective.countable
  have hSc : Continuous (cuspCharacterSeries b) := cuspCharacterSeries_continuous b hb
  have hfin : volume periodDomain ≠ ⊤ := by
    rw [periodDomain_volume]
    exact ENNReal.ofReal_ne_top
  have hi : ∀ h : O, Integrable (fun u : ℂ => a h *
      (cuspCharacterSeries b u * tracePhase (cuspFrequency (4 * h) * u))) (volume.restrict periodDomain) :=
    fun h => integrableOn_periodDomain_of_continuous _
      (continuous_const.mul (hSc.mul (tracePhase_continuous (4 * h))))
  have hpt : ∀ (h : O) (u : ℂ), ‖a h * (cuspCharacterSeries b u * tracePhase (cuspFrequency (4 * h) * u))‖ ≤
      ‖a h‖ * ∑' k : O, ‖b k‖ := by
    intro h u
    rw [norm_mul, norm_mul, tracePhase_norm, mul_one]
    exact mul_le_mul_of_nonneg_left (norm_cuspCharacterSeries_le b hb u) (norm_nonneg _)
  have hint_le : ∀ h : O, ∫ u in periodDomain,
      ‖a h * (cuspCharacterSeries b u * tracePhase (cuspFrequency (4 * h) * u))‖ ≤
        ‖a h‖ * (∑' k : O, ‖b k‖) * (volume periodDomain).toReal := by
    intro h
    have hc : IntegrableOn (fun _ : ℂ => ‖a h‖ * ∑' k : O, ‖b k‖) periodDomain :=
      integrableOn_const (μ := volume) hfin
    calc _ ≤ ∫ _ in periodDomain, ‖a h‖ * ∑' k : O, ‖b k‖ :=
          setIntegral_mono_on (hi h).norm hc periodDomain_measurable (fun u _ => hpt h u)
      _ = _ := by rw [setIntegral_const, smul_eq_mul, Measure.real, mul_comm]
  have hsum : Summable (fun h : O => ∫ u in periodDomain,
      ‖a h * (cuspCharacterSeries b u * tracePhase (cuspFrequency (4 * h) * u))‖) :=
    Summable.of_nonneg_of_le (fun h => integral_nonneg fun u => norm_nonneg _) hint_le
      ((ha.mul_right _).mul_right _)
  have hprod : ∀ u : ℂ, cuspCharacterSeries a (4 * u) * cuspCharacterSeries b u =
      ∑' h : O, a h * (cuspCharacterSeries b u * tracePhase (cuspFrequency (4 * h) * u)) := by
    intro u
    rw [cuspCharacterSeries, ← tsum_mul_right]
    refine tsum_congr fun h => ?_
    rw [cuspFrequency_mul_four, show 4 * cuspFrequency h * u = cuspFrequency h * (4 * u) by ring]
    ring
  simp_rw [hprod]
  rw [← integral_tsum_of_summable_integral_norm hi hsum]
  calc ∑' h : O, ∫ u in periodDomain, a h *
        (cuspCharacterSeries b u * tracePhase (cuspFrequency (4 * h) * u))
      = ∑' h : O, periodArea * (a h * b (-(4 * h))) :=
        tsum_congr fun h => by
          have hk := cuspCharacterSeries_fourier b hb (-(4 * h))
          rw [cuspFrequency_neg, neg_neg] at hk
          rw [integral_const_mul, hk]
          ring
    _ = _ := tsum_mul_left

/-- The Hecke-at-four correlation of the projected theta function. -/
abbrev sourceFourCorrelation : HyperbolicSpace → ℂ := heckeFourCorrelation sourceTheta

/-- `F(2u, v) = S_{b(2v)}(4u) S_{b(v/2)}(u)`. -/
theorem sourceFourCorrelation_upperPoint (u : ℂ) (v : ℝ) (hv : 0 < v) :
    sourceFourCorrelation (upperPoint (2 * u) v hv) =
      cuspCharacterSeries (rationalSourceModeAmplitude (2 * v)) (4 * u) *
        cuspCharacterSeries (rationalSourceModeAmplitude (v / 2)) u := by
  simp only [sourceFourCorrelation, heckeFourCorrelation]
  rw [fourDilation_upperPoint, fourContraction_upperPoint]
  rw [show (2 : ℂ) * (2 * u) = 4 * u by ring, show (2 : ℂ) * u / 2 = u by ring]
  rw [sourceTheta, cubicSourceResidualFunction_fourier_expansion, cubicSourceResidualFunction_fourier_expansion]

/-- **The constant term of the Hecke-at-four correlation.** -/
theorem integral_sourceFourCorrelation (v : ℝ) (hv : 0 < v) :
    ∫ u in periodDomain, sourceFourCorrelation (upperPoint (2 * u) v hv) =
      periodArea * ∑' h : O, rationalSourceModeAmplitude (2 * v) h *
        rationalSourceModeAmplitude (v / 2) (-(4 * h)) := by
  simp_rw [sourceFourCorrelation_upperPoint]
  exact integral_cuspCharacterSeries_four_mul _ _ (rationalSourceModeAmplitude_summable _ (by positivity))
    (rationalSourceModeAmplitude_summable _ (by positivity))

/-- `(2v)^{2/3} (v/2)^{2/3} = v^{4/3}`. -/
theorem cpow_two_mul_mul_cpow_half (v : ℝ) (hv : 0 < v) :
    ((2 * v : ℝ) : ℂ) ^ (2 / 3 : ℂ) * ((v / 2 : ℝ) : ℂ) ^ (2 / 3 : ℂ) = (v : ℂ) ^ (4 / 3 : ℂ) := by
  have hv0 : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  rw [← Complex.mul_cpow_ofReal_nonneg (by positivity) (by positivity),
    show ((2 * v : ℝ) : ℂ) * ((v / 2 : ℝ) : ℂ) = (v : ℂ) * (v : ℂ) by push_cast; ring,
    Complex.mul_cpow_ofReal_nonneg hv.le hv.le, ← Complex.cpow_add _ _ hv0]
  norm_num

/-- The growing term: `b(2v, 0) b(v/2, 0) = c² v^{4/3}`. -/
theorem sourceAmplitude_four_zero (v : ℝ) (hv : 0 < v) :
    rationalSourceModeAmplitude (2 * v) 0 * rationalSourceModeAmplitude (v / 2) (-(4 * 0)) =
      thetaConstant ^ 2 * (v : ℂ) ^ (4 / 3 : ℂ) := by
  rw [mul_zero, neg_zero, rationalSourceModeAmplitude_zero, rationalSourceModeAmplitude_zero,
    ← cpow_two_mul_mul_cpow_half v hv]
  push_cast
  ring

/-- For `h ≠ 0`: `b(2v, h) b(v/2, −4h) = T_s(h) T_s(−4h) v² K_{1/3}(8π|ξ_h| v)²`. -/
theorem sourceAmplitude_four_shift (v : ℝ) (hv : 0 < v) (h : O) (hh : h ≠ 0) :
    rationalSourceModeAmplitude (2 * v) h * rationalSourceModeAmplitude (v / 2) (-(4 * h)) =
      rationalSourceResidualFourierCoefficient h * rationalSourceResidualFourierCoefficient (-(4 * h)) *
        (v : ℂ) ^ 2 * schlafliBesselK (1 / 3) (8 * Real.pi * ‖cuspFrequency h‖ * v) ^ 2 := by
  rw [rationalSourceModeAmplitude_bessel (2 * v) (by positivity) h hh,
    rationalSourceModeAmplitude_bessel (v / 2) (by positivity) (-(4 * h))
      (neg_ne_zero.mpr (mul_ne_zero four_ne_zero_O hh)),
    cuspFrequency_neg, norm_neg, cuspFrequency_mul_four, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
  have e1 : 4 * Real.pi * ‖cuspFrequency h‖ * (2 * v) = 8 * Real.pi * ‖cuspFrequency h‖ * v := by ring
  have e2 : 4 * Real.pi * (4 * ‖cuspFrequency h‖) * (v / 2) = 8 * Real.pi * ‖cuspFrequency h‖ * v := by ring
  rw [e1, e2]
  push_cast
  ring

end GaloisForLFunctions.OrderSixMetaplecticTheory
