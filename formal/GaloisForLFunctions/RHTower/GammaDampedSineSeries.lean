import GaloisForLFunctions.RHTower.GammaDampedScaledSpectralLimit
import GaloisForLFunctions.RHTower.EulerFisherCurvature
import GaloisForLFunctions.HTGeometry.OddSpectralSynthesis

/-!
# The damped spectral symbol as a sine series

On the vertical line `z = α - i x`, `α = (σ+1)/2`, the damped spectral symbol

```text
D(σ, x) = -F'(α - ix) - m_σ F(α - ix)
```

is the Dirichlet series with coefficients `μ(d)² η_d (log d - m_σ)`, so its imaginary part is exactly
the odd sine series

```text
Im D(σ, x) = ∑_d μ(d)² η_d (log d - m_σ) d^(-α) sin(x log d) ,
```

with absolutely summable coefficients.  This is the arithmetic side of the odd spectral synthesis.
-/

open Filter Topology LSeries

namespace RHTower

noncomputable section

/-! ### The vertical line and the sine coefficients -/

/-- The point `α - i x` on the Euler abscissa `α = (σ+1)/2`. -/
def gammaDampedCriticalLinePoint (σ x : ℝ) : ℂ := (((σ + 1) / 2 : ℝ) : ℂ) - (x : ℂ) * Complex.I

theorem gammaDampedCriticalLinePoint_re (σ x : ℝ) : (gammaDampedCriticalLinePoint σ x).re = (σ + 1) / 2 := by
  simp [gammaDampedCriticalLinePoint]

theorem criticalScaledPoint_eq (ε y : ℝ) :
    criticalScaledPoint ε y = gammaDampedCriticalLinePoint (1 + ε) (ε * y) := by
  rw [criticalScaledPoint, criticalDirection, gammaDampedCriticalLinePoint]
  push_cast
  ring

/-- The odd sine-series coefficients `μ(d)² η_d (log d - m_σ) d^(-α)`. -/
def gammaDampedSineCoeff (σ : ℝ) (d : ℕ) : ℝ :=
  if Squarefree d then
    gammaDampingFactor d * (Real.log d - squarefreeMobiusLogMoment 1 σ) *
      (d : ℝ) ^ (-((σ + 1) / 2))
  else 0

theorem abs_gammaDampedSineCoeff_le (σ : ℝ) (d : ℕ) :
    |gammaDampedSineCoeff σ d|
      ≤ |Real.log d| ^ 1 * (d : ℝ) ^ (-((σ + 1) / 2)) +
        |squarefreeMobiusLogMoment 1 σ| * (|Real.log d| ^ 0 * (d : ℝ) ^ (-((σ + 1) / 2))) := by
  have hpow : (0 : ℝ) ≤ (d : ℝ) ^ (-((σ + 1) / 2)) := Real.rpow_nonneg (Nat.cast_nonneg d) _
  rw [gammaDampedSineCoeff]
  split_ifs
  · rw [abs_mul, abs_mul, abs_of_pos (gammaDampingFactor_pos d), abs_of_nonneg hpow]
    have hle : gammaDampingFactor d ≤ 1 := gammaDampingFactor_le_one d
    have habs : |Real.log d - squarefreeMobiusLogMoment 1 σ|
        ≤ |Real.log d| + |squarefreeMobiusLogMoment 1 σ| := abs_sub _ _
    have hpos : (0 : ℝ) ≤ |Real.log d - squarefreeMobiusLogMoment 1 σ| := abs_nonneg _
    have hd : (0 : ℝ) < gammaDampingFactor d := gammaDampingFactor_pos d
    have hstep : gammaDampingFactor d * |Real.log d - squarefreeMobiusLogMoment 1 σ|
        ≤ |Real.log d| + |squarefreeMobiusLogMoment 1 σ| := by
      calc gammaDampingFactor d * |Real.log d - squarefreeMobiusLogMoment 1 σ|
          ≤ 1 * |Real.log d - squarefreeMobiusLogMoment 1 σ| :=
            mul_le_mul_of_nonneg_right hle hpos
        _ = |Real.log d - squarefreeMobiusLogMoment 1 σ| := one_mul _
        _ ≤ |Real.log d| + |squarefreeMobiusLogMoment 1 σ| := habs
    simp only [pow_one, pow_zero, one_mul]
    calc gammaDampingFactor d * |Real.log d - squarefreeMobiusLogMoment 1 σ| *
          (d : ℝ) ^ (-((σ + 1) / 2))
        ≤ (|Real.log d| + |squarefreeMobiusLogMoment 1 σ|) * (d : ℝ) ^ (-((σ + 1) / 2)) :=
          mul_le_mul_of_nonneg_right hstep hpow
      _ = |Real.log d| * (d : ℝ) ^ (-((σ + 1) / 2)) +
          |squarefreeMobiusLogMoment 1 σ| * (d : ℝ) ^ (-((σ + 1) / 2)) := by ring
  · simp only [abs_zero]
    have h1 : (0 : ℝ) ≤ |Real.log d| ^ 1 * (d : ℝ) ^ (-((σ + 1) / 2)) := by positivity
    have h2 : (0 : ℝ) ≤ |squarefreeMobiusLogMoment 1 σ| *
        (|Real.log d| ^ 0 * (d : ℝ) ^ (-((σ + 1) / 2))) := by positivity
    linarith

theorem summable_abs_gammaDampedSineCoeff {σ : ℝ} (hσ : 1 < σ) :
    Summable fun d => |gammaDampedSineCoeff σ d| := by
  have hα : 1 < (σ + 1) / 2 := by linarith
  have h1 := summable_abs_log_natCast_pow_mul_rpow_neg 1 ((σ + 1) / 2) hα
  have h0 := summable_abs_log_natCast_pow_mul_rpow_neg 0 ((σ + 1) / 2) hα
  refine Summable.of_nonneg_of_le (fun d => abs_nonneg _) (abs_gammaDampedSineCoeff_le σ)
    (h1.add (h0.mul_left _))

/-! ### The symbol on the vertical line -/

/-- The damped spectral symbol on the vertical line `α - i x`. -/
def gammaDampedSymbol (σ x : ℝ) : ℂ :=
  -deriv (LSeries gammaDampedCoeff) (gammaDampedCriticalLinePoint σ x) -
    ((squarefreeMobiusLogMoment 1 σ : ℝ) : ℂ) * LSeries gammaDampedCoeff (gammaDampedCriticalLinePoint σ x)

theorem gammaDampedSpectralSymbol_eq (ε y : ℝ) :
    gammaDampedSpectralSymbol ε y = gammaDampedSymbol (1 + ε) (ε * y) := by
  rw [gammaDampedSpectralSymbol, gammaDampedSymbol, criticalScaledPoint_eq]

theorem norm_gammaDampedCoeff_le (d : ℕ) : ‖gammaDampedCoeff d‖ ≤ 1 := by
  rw [gammaDampedCoeff]
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gammaDampingFactor_pos d)]
    exact gammaDampingFactor_le_one d
  · simp

theorem abscissaOfAbsConv_gammaDampedCoeff_le : abscissaOfAbsConv gammaDampedCoeff ≤ 1 :=
  abscissaOfAbsConv_le_of_le_const ⟨1, fun n _ => norm_gammaDampedCoeff_le n⟩

theorem abscissa_lt_gammaDampedCriticalLinePoint {σ : ℝ} (hσ : 1 < σ) (x : ℝ) :
    abscissaOfAbsConv gammaDampedCoeff < ((gammaDampedCriticalLinePoint σ x).re : EReal) := by
  refine lt_of_le_of_lt abscissaOfAbsConv_gammaDampedCoeff_le ?_
  rw [gammaDampedCriticalLinePoint_re, show ((1 : EReal)) = ((1 : ℝ) : EReal) from rfl]
  exact_mod_cast (by linarith : (1 : ℝ) < (σ + 1) / 2)

theorem complex_log_natCast (n : ℕ) : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]

/-- **The symbol is the Dirichlet series of `μ(d)² η_d (log d - m_σ)`.** -/
theorem gammaDampedSymbol_eq_lSeries {σ : ℝ} (hσ : 1 < σ) (x : ℝ) :
    gammaDampedSymbol σ x
      = LSeries (fun d => (((Real.log d - squarefreeMobiusLogMoment 1 σ : ℝ)) : ℂ) *
          gammaDampedCoeff d) (gammaDampedCriticalLinePoint σ x) := by
  have habs := abscissa_lt_gammaDampedCriticalLinePoint hσ x
  have hsum : LSeriesSummable gammaDampedCoeff (gammaDampedCriticalLinePoint σ x) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re habs
  have hlog : LSeriesSummable (logMul gammaDampedCoeff) (gammaDampedCriticalLinePoint σ x) :=
    LSeriesSummable_logMul_of_lt_re habs
  have hsmul : LSeriesSummable
      (((squarefreeMobiusLogMoment 1 σ : ℝ) : ℂ) • gammaDampedCoeff) (gammaDampedCriticalLinePoint σ x) := by
    refine (hsum.mul_left ((squarefreeMobiusLogMoment 1 σ : ℝ) : ℂ)).congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [term_of_ne_zero hn, term_of_ne_zero hn]
      simp [mul_div_assoc]
  rw [gammaDampedSymbol, LSeries_deriv habs, neg_neg, ← LSeries_smul, ← LSeries_sub hlog hsmul]
  refine LSeries_congr (fun {n} _ => ?_) _
  simp only [Pi.sub_apply, logMul, Pi.smul_apply, smul_eq_mul]
  rw [complex_log_natCast]
  push_cast
  ring

/-! ### The imaginary part is the sine series -/

/-- **The odd part of the symbol is the sine series.** -/
theorem im_gammaDampedSymbol {σ : ℝ} (hσ : 1 < σ) (x : ℝ) :
    (gammaDampedSymbol σ x).im
      = HTGeometry.sinSeries (gammaDampedSineCoeff σ) (fun d => Real.log d) x := by
  have habs := abscissa_lt_gammaDampedCriticalLinePoint hσ x
  set g : ℕ → ℂ := fun d => (((Real.log d - squarefreeMobiusLogMoment 1 σ : ℝ)) : ℂ) *
    gammaDampedCoeff d with hg
  have hsum : LSeriesSummable g (gammaDampedCriticalLinePoint σ x) := by
    rw [hg]
    have hsum0 : LSeriesSummable gammaDampedCoeff (gammaDampedCriticalLinePoint σ x) :=
      LSeriesSummable_of_abscissaOfAbsConv_lt_re habs
    have hlog : LSeriesSummable (logMul gammaDampedCoeff) (gammaDampedCriticalLinePoint σ x) :=
      LSeriesSummable_logMul_of_lt_re habs
    have hsmul : LSeriesSummable
        (((squarefreeMobiusLogMoment 1 σ : ℝ) : ℂ) • gammaDampedCoeff) (gammaDampedCriticalLinePoint σ x) := by
      refine (hsum0.mul_left ((squarefreeMobiusLogMoment 1 σ : ℝ) : ℂ)).congr fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp [LSeries.term_zero]
      · rw [term_of_ne_zero hn, term_of_ne_zero hn]
        simp [mul_div_assoc]
    refine (hlog.sub hsmul).congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [term_of_ne_zero hn, term_of_ne_zero hn]
      congr 1
      simp only [Pi.sub_apply, logMul, Pi.smul_apply, smul_eq_mul]
      rw [complex_log_natCast]
      push_cast
      ring
  rw [gammaDampedSymbol_eq_lSeries hσ x, ← hg, LSeries]
  rw [show ((∑' d, term g (gammaDampedCriticalLinePoint σ x) d).im)
      = Complex.imCLM (∑' d, term g (gammaDampedCriticalLinePoint σ x) d) from rfl,
    Complex.imCLM.map_tsum hsum, HTGeometry.sinSeries]
  refine tsum_congr fun d => ?_
  rcases eq_or_ne d 0 with rfl | hd
  · simp [LSeries.term_zero, gammaDampedSineCoeff, not_squarefree_zero]
  · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
    have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
    have hdne : ((d : ℂ)) ≠ 0 := by
      simp only [ne_eq, Nat.cast_eq_zero]
      exact hd
    have hcpow : ((d : ℂ)) ^ (-(gammaDampedCriticalLinePoint σ x)) =
        Complex.exp (((Real.log d : ℝ) : ℂ) * (-(gammaDampedCriticalLinePoint σ x))) := by
      rw [Complex.cpow_def_of_ne_zero hdne, complex_log_natCast]
    have hterm : term g (gammaDampedCriticalLinePoint σ x) d
        = g d * Complex.exp (((Real.log d : ℝ) : ℂ) * (-(gammaDampedCriticalLinePoint σ x))) := by
      rw [term_of_ne_zero hd, ← hcpow, Complex.cpow_neg, div_eq_mul_inv]
    have hre : (((Real.log d : ℝ) : ℂ) * (-(gammaDampedCriticalLinePoint σ x))).re
        = -((σ + 1) / 2 * Real.log d) := by
      simp only [gammaDampedCriticalLinePoint, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero, zero_sub, neg_neg]
      ring
    have him : (((Real.log d : ℝ) : ℂ) * (-(gammaDampedCriticalLinePoint σ x))).im
        = Real.log d * x := by
      simp only [gammaDampedCriticalLinePoint, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, mul_one, sub_zero, zero_sub, neg_neg]
      ring
    have hgB : g d = (((Real.log d - squarefreeMobiusLogMoment 1 σ) *
        (if Squarefree d then gammaDampingFactor d else 0) : ℝ) : ℂ) := by
      simp only [hg, gammaDampedCoeff]
      split_ifs <;> push_cast <;> ring
    have hexp : Real.exp (-((σ + 1) / 2 * Real.log d)) = (d : ℝ) ^ (-((σ + 1) / 2)) := by
      rw [Real.rpow_def_of_pos hdpos]
      congr 1
      ring
    rw [hterm, hgB, Complex.imCLM_apply, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.exp_im, hre, him, hexp, gammaDampedSineCoeff]
    split_ifs <;> ring

/-! ### The spectral norm identity -/

/-- **`(21)`: the odd synthesis norm is the spectral energy of `Im D`.**  Any synthesis whose Gram
matrix is the odd Gamma cyclic kernel `φ(log d - log e) - φ(log d + log e)` has squared norm twice the
`ν_Γ`-energy of the imaginary part of the damped spectral symbol. -/
theorem norm_sq_gammaDampedOddSynthesis {K : Type*} [NormedAddCommGroup K]
    [InnerProductSpace ℝ K] [CompleteSpace K] (v : ℕ → K) {σ : ℝ} (hσ : 1 < σ)
    (hgram : ∀ d e : ℕ, (inner ℝ (v d) (v e) : ℝ)
      = Real.cosh (Real.log d - Real.log e) ^ (-(1 / 2) : ℝ)
        - Real.cosh (Real.log d + Real.log e) ^ (-(1 / 2) : ℝ))
    (hsum : Summable fun d => gammaDampedSineCoeff σ d • v d) :
    ‖∑' d, gammaDampedSineCoeff σ d • v d‖ ^ 2
      = 2 * ∫ y, (gammaDampedSymbol σ y).im ^ 2 ∂HTGeometry.gammaCyclicMeasure := by
  have hgram' : ∀ d e : ℕ, (inner ℝ (v d) (v e) : ℝ)
      = 2 * ∫ y, Real.sin (Real.log d * y) * Real.sin (Real.log e * y)
          ∂HTGeometry.gammaCyclicMeasure := by
    intro d e
    rw [hgram d e, HTGeometry.gammaCyclicOddKernel_measure_eq]
  have hmain := HTGeometry.norm_sq_oddSynthesis (c := gammaDampedSineCoeff σ)
    (h := fun d => Real.log d) (v := v) (summable_abs_gammaDampedSineCoeff hσ) hgram' hsum
  rw [hmain]
  congr 1
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with y
  rw [im_gammaDampedSymbol hσ y]

end

end RHTower
