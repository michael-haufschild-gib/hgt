import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapConductorFloor
import GaloisForLFunctions.BiScaleUncertainty.EffectiveTranslatedPairingAndMultiplicityDefect

/-!
# A polynomial lower floor for every completed conductor

The boosted spline Fourier bound survives translation and dilation to the unit profile.
Integrating its squared lower bound over a band of length `c` beyond overlap `c` retains
an explicit positive multiple of `c⁻⁷`. The coprime-tail formula transfers this same floor
to every completed conductor, uniformly as overlap grows.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri
  BiScaleUncertainty.ChebyshevGauge RenormalizedArithmeticPotentialTheory.CompletedShell

/-- The fixed positive coefficient in the polynomial Fourier-tail floor. -/
def tiltedSplineTailConstant : ℝ :=
  Real.sinh 1 ^ 8 / (64 * (1 + (3 * Real.pi / 4) ^ 2) ^ 4)

theorem tiltedSplineTailConstant_pos : 0 < tiltedSplineTailConstant := by
  have hs : 0 < Real.sinh 1 := Real.sinh_pos_iff.mpr zero_lt_one
  unfold tiltedSplineTailConstant
  positivity

private theorem norm_paperFT_tiltedUnitSpline (r : ℝ) :
    ‖paperFT (cx tiltedUnitSpline) (r : ℂ)‖ =
      (1 / 8 : ℝ) * ‖paperFT (cx splineProbe) ((r / 8 : ℝ) : ℂ)‖ := by
  have heq : cx tiltedUnitSpline =
      ArithmeticCastelnuovoSeveri.translate (1 / 2) (cx (atomDilate splineProbe (1 / 8))) := rfl
  rw [heq, paperFT_translate, paperFT_atomDilate (by norm_num : (0 : ℝ) < 1 / 8),
    norm_mul, norm_mul, Complex.norm_exp]
  have hz : ((1 / 8 : ℝ) : ℂ) * (r : ℂ) = ((r / 8 : ℝ) : ℂ) := by push_cast; ring
  rw [hz]
  norm_num [Complex.mul_re, Complex.mul_im]

private theorem tiltedUnitSpline_spectrum_floor_on_tail_band {c : ℝ} (hc : 1 ≤ c)
    {t : ℝ} (ht : t ∈ Icc (c + 1) (2 * c + 1)) :
    tiltedSplineTailConstant / c ^ 8 ≤ shellSpectrum tiltedUnitSpline t := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have ht0 : 0 ≤ t := by linarith only [ht.1, hc]
  have ht3 : t ≤ 3 * c := by linarith only [ht.2, hc]
  let D := 1 + (3 * Real.pi / 4) ^ 2
  have hD : 0 < D := by dsimp only [D]; positivity
  have hsq : (Real.pi * t / 4) ^ 2 ≤ (3 * Real.pi / 4) ^ 2 * c ^ 2 := by
    have h := mul_self_le_mul_self (by positivity : 0 ≤ Real.pi * t / 4)
      (show Real.pi * t / 4 ≤ (3 * Real.pi / 4) * c by nlinarith only [Real.pi_pos, ht3])
    nlinarith only [h]
  have hden : 1 + (Real.pi * t / 4) ^ 2 ≤ D * c ^ 2 := by
    dsimp only [D]
    nlinarith only [hsq, hc, sq_nonneg (c - 1)]
  have hden2 := pow_le_pow_left₀
    (by positivity : 0 ≤ 1 + (Real.pi * t / 4) ^ 2) hden 2
  have hbase := le_norm_paperFT_splineProbe_ofReal ((2 * Real.pi * t) / 8)
  have harg : 2 * Real.pi * t / 8 = Real.pi * t / 4 := by ring
  rw [harg] at hbase
  have hnorm : Real.sinh 1 ^ 4 / (8 * D ^ 2 * c ^ 4) ≤
      ‖paperFT (cx tiltedUnitSpline) ((2 * Real.pi * t : ℝ) : ℂ)‖ := by
    rw [norm_paperFT_tiltedUnitSpline]
    have hsmall := div_le_div_of_nonneg_left (by positivity : 0 ≤ Real.sinh 1 ^ 4)
      (by positivity : 0 < (1 + (Real.pi * t / 4) ^ 2) ^ 2) hden2
    have h := mul_le_mul_of_nonneg_left (hsmall.trans hbase)
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [harg]
    calc
      _ = (1 / 8 : ℝ) * (Real.sinh 1 ^ 4 / (D * c ^ 2) ^ 2) := by ring
      _ ≤ _ := h
  have hsqnorm := mul_self_le_mul_self
    (by positivity : 0 ≤ Real.sinh 1 ^ 4 / (8 * D ^ 2 * c ^ 4)) hnorm
  change _ ≤ ‖paperFT (cx tiltedUnitSpline) ((2 * Real.pi * t : ℝ) : ℂ)‖ ^ 2
  calc
    _ = (Real.sinh 1 ^ 4 / (8 * D ^ 2 * c ^ 4)) ^ 2 := by
      dsimp only [tiltedSplineTailConstant, D]
      field_simp
      ring
    _ ≤ _ := by simpa only [pow_two] using hsqnorm

/-- The explicit tilted spline retains a Fourier tail of order at least `c⁻⁷`. -/
theorem tiltedSplineTailConstant_div_pow_le_shellTail {c : ℝ} (hc : 1 ≤ c) :
    tiltedSplineTailConstant / c ^ 7 ≤
      ∫ t in Ioi c, shellSpectrum tiltedUnitSpline t := by
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hsub : Icc (c + 1) (2 * c + 1) ⊆ Ioi c := fun t ht => by
    simp only [mem_Ioi]
    linarith only [ht.1]
  have hint := integrableOn_shellSpectrum_Ioi contDiff_tiltedUnitSpline
    hasCompactSupport_tiltedUnitSpline c
  calc
    _ = ∫ t in Icc (c + 1) (2 * c + 1), tiltedSplineTailConstant / c ^ 8 := by
      rw [setIntegral_const, smul_eq_mul, Measure.real, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith only [hc])]
      field_simp
      ring
    _ ≤ ∫ t in Icc (c + 1) (2 * c + 1), shellSpectrum tiltedUnitSpline t :=
      setIntegral_mono_on (integrableOn_const (by simp)) (hint.mono_set hsub)
        measurableSet_Icc fun t ht => tiltedUnitSpline_spectrum_floor_on_tail_band hc ht
    _ ≤ _ := setIntegral_mono_set hint (ae_of_all _ fun t => shellSpectrum_nonneg t)
      (Eventually.of_forall hsub)

/-- Every completed conductor has the same polynomial lower floor as overlap grows. -/
theorem tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor {c : ℝ} (hc : 1 ≤ c)
    {m : ℕ} (hm : 0 < m) :
    (2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)) / c ^ 7 ≤
      completedConductorEnergy tiltedUnitSpline c m := by
  have h := (mul_le_mul_of_nonneg_left (tiltedSplineTailConstant_div_pow_le_shellTail hc)
    (div_nonneg zero_le_two integral_tiltedUnitSpline_sq_pos.le)).trans
      (completedConductorEnergy_ge_shellTail contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
        integral_tiltedUnitSpline_sq_pos (zero_lt_one.trans_le hc) hm)
  calc
    _ = (2 / (∫ u, tiltedUnitSpline u ^ 2)) * (tiltedSplineTailConstant / c ^ 7) := by ring
    _ ≤ _ := h

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tiltedSplineTailConstant_div_pow_le_shellTail
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor
