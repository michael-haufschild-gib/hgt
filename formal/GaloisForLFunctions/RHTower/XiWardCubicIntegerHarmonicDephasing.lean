import GaloisForLFunctions.RHTower.XiWardCubicHeightBohrFiber
import GaloisForLFunctions.HTGeometry.HarmonicLogFourierMode
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPrimeTranslationAnomaly
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaPrimeCriticalRiggedCarrier

/-!
# Source-native integer-harmonic ordinate dephasing

Normalized integer shifts on two line-conjugate evaluation fibres retain a unit-modulus phase
depending only on the spectral ordinate.  Their logarithmic harmonic correlation converges to the
equal-ordinate projector.  This realizes the finite cubic dephasing trace before divisor
evaluation; it does not assert the still-open arithmetic trace budget.
-/

open scoped BigOperators
open Complex Filter Topology Finset

namespace RHTower

noncomputable section

open GaloisForLFunctions
open HedenmalmPrimeTranslation
open HedenmalmThetaSource

/-- Spectral eigenvalue of the fixed normalized tensor dilation
`n (T_n tensor T_n)` on line-conjugate evaluation fibres. -/
def normalizedLineConjIntegerPhaseGain (n : ℕ) (z : ℂ) : ℂ :=
  (n : ℂ) * ((n : ℂ) ^ (-(dirichletExponent z))) *
    ((n : ℂ) ^ (-(dirichletExponent (star z))))

theorem normalizedLineConjIntegerPhaseGain_eq_exp
    {n : ℕ} (hn : 0 < n) (z : ℂ) :
    normalizedLineConjIntegerPhaseGain n z =
      Complex.exp ((-2 * z.re : ℂ) * I * (Real.log n : ℂ)) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    rw [← Complex.ofReal_natCast]
    exact (Complex.ofReal_log hnR.le).symm
  have hnexp : (n : ℂ) = Complex.exp (Real.log n : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hnR]
    push_cast
    rfl
  rw [normalizedLineConjIntegerPhaseGain,
    Complex.cpow_def_of_ne_zero hnC, Complex.cpow_def_of_ne_zero hnC,
    hlog, hnexp, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;>
    simp [dirichletExponent, Complex.mul_re, Complex.mul_im] <;> ring

/-- On an actual Xi divisor mode, the fixed source gain is exactly the physical ordinate
character. -/
theorem normalizedLineConjIntegerPhaseGain_xiSpectralPoint_eq_exp
    {n : ℕ} (hn : 0 < n) (q : XiZeroCopy) :
    normalizedLineConjIntegerPhaseGain n (xiSpectralPoint q) =
      Complex.exp ((-2 * (q.1 : ℂ).im : ℂ) * I * (Real.log n : ℂ)) := by
  rw [normalizedLineConjIntegerPhaseGain_eq_exp hn]
  congr 1
  simp [xiSpectralPoint, Complex.mul_re]

/-- Applying one fixed integer shift on each line-conjugate source evaluation fibre produces the
phase gain.  No ordinate-dependent scalar is inserted after divisor evaluation. -/
theorem sourceEvaluation_integerShift_lineConj_tensor
    {n : ℕ} (hn : 0 < n) (z : ℂ) (f g : ℝ → ℂ) :
    (n : ℂ) * sourceEvaluation z (integerShift n f) *
        sourceEvaluation (star z) (integerShift n g) =
      normalizedLineConjIntegerPhaseGain n z *
        (sourceEvaluation z f * sourceEvaluation (star z) g) := by
  rw [sourceEvaluation_integerShift z f hn,
    sourceEvaluation_integerShift (star z) g hn,
    normalizedLineConjIntegerPhaseGain]
  ring

/-- Critical-rigging evaluation is an exact continuous-dual eigenvector of every normalized
integer shift. -/
theorem criticalEvaluation_comp_criticalIntegerShift
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : |z.im| < 1 / 2) :
    (criticalEvaluation z hz).comp (criticalIntegerShift hn) =
      ((n : ℂ) ^ (-(dirichletExponent z))) • criticalEvaluation z hz := by
  ext f
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  exact criticalEvaluation_criticalIntegerShift hn hz f

/-- The source-native pure ordinate character persists after bounded critical-rigging closure on
both line-conjugate evaluation fibres. -/
theorem criticalEvaluation_integerShift_lineConj_tensor
    {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : |z.im| < 1 / 2)
    (f g : CriticalL2) :
    (n : ℂ) * criticalEvaluation z hz (criticalIntegerShift hn f) *
        criticalEvaluation (star z) (by simpa using hz) (criticalIntegerShift hn g) =
      normalizedLineConjIntegerPhaseGain n z *
        (criticalEvaluation z hz f *
          criticalEvaluation (star z) (by simpa using hz) g) := by
  rw [criticalEvaluation_criticalIntegerShift,
    criticalEvaluation_criticalIntegerShift,
    normalizedLineConjIntegerPhaseGain]
  ring

theorem norm_normalizedLineConjIntegerPhaseGain
    {n : ℕ} (hn : 0 < n) (z : ℂ) :
    ‖normalizedLineConjIntegerPhaseGain n z‖ = 1 := by
  rw [normalizedLineConjIntegerPhaseGain_eq_exp hn, Complex.norm_exp]
  have harg : ((-2 * z.re : ℂ) * I * (Real.log n : ℂ)) =
      I * ((-2 * z.re * Real.log n : ℝ) : ℂ) := by
    push_cast
    ring
  have hre : (((-2 * z.re : ℂ) * I * (Real.log n : ℂ))).re = 0 := by
    rw [harg]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, sub_zero]
  rw [hre, Real.exp_zero]

/-- Weighted correlation of two source-native gains is the critical-line Dirichlet character at
the difference of their real spectral coordinates. -/
theorem invNatCast_mul_phaseGain_mul_star_phaseGain_eq_gpow
    {n : ℕ} (hn : 0 < n) (z w : ℂ) :
    (((n : ℝ)⁻¹ : ℝ) : ℂ) * normalizedLineConjIntegerPhaseGain n z *
        star (normalizedLineConjIntegerPhaseGain n w) =
      gpow (-2 * (z.re - w.re)) n := by
  rw [normalizedLineConjIntegerPhaseGain_eq_exp hn,
    normalizedLineConjIntegerPhaseGain_eq_exp hn, gpow]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hinvR : (n : ℝ)⁻¹ = Real.exp (-Real.log n) := by
    rw [Real.exp_neg, Real.exp_log hnR]
  have hinvC : (((n : ℝ)⁻¹ : ℝ) : ℂ) =
      Complex.exp (-(Real.log n : ℂ)) := by
    calc
      (((n : ℝ)⁻¹ : ℝ) : ℂ) =
          (Real.exp (-Real.log n) : ℂ) := congrArg Complex.ofReal hinvR
      _ = Complex.exp ((-Real.log n : ℝ) : ℂ) :=
        Complex.ofReal_exp (-Real.log n)
      _ = Complex.exp (-(Real.log n : ℂ)) := by
        congr 1
        push_cast
        rfl
  change (((n : ℝ)⁻¹ : ℝ) : ℂ) *
      Complex.exp ((-2 * z.re : ℂ) * I * (Real.log n : ℂ)) *
      (starRingEnd ℂ) (Complex.exp
        ((-2 * w.re : ℂ) * I * (Real.log n : ℂ))) = _
  rw [hinvC, ← Complex.exp_conj]
  simp only [map_mul, map_neg, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Correlation of two actual Xi modes depends only on their physical ordinate gap. -/
theorem invNatCast_mul_xi_phaseGain_mul_star_xi_phaseGain_eq_gpow
    {n : ℕ} (hn : 0 < n) (q w : XiZeroCopy) :
    (((n : ℝ)⁻¹ : ℝ) : ℂ) *
        normalizedLineConjIntegerPhaseGain n (xiSpectralPoint q) *
        star (normalizedLineConjIntegerPhaseGain n (xiSpectralPoint w)) =
      gpow (-2 * ((q.1 : ℂ).im - (w.1 : ℂ).im)) n := by
  simpa [xiSpectralPoint, Complex.mul_re] using
    invNatCast_mul_phaseGain_mul_star_phaseGain_eq_gpow hn
      (xiSpectralPoint q) (xiSpectralPoint w)

/-- Logarithmically normalized harmonic kernel generated by the integer-shift tensor. -/
def integerHarmonicOrdinateKernel (delta : ℝ) (N : ℕ) : ℂ :=
  (∑ n ∈ Finset.range N,
      gpow (-2 * delta) ((n : ℝ) + 1)) / (Real.log N : ℂ)

/-- Integer harmonic averaging projects exactly onto zero ordinate gap. -/
theorem tendsto_integerHarmonicOrdinateKernel (delta : ℝ) :
    Tendsto (integerHarmonicOrdinateKernel delta) atTop
      (nhds (if delta = 0 then 1 else 0)) := by
  by_cases hdelta : delta = 0
  · subst delta
    simp
    have hreal := GaloisForLFunctions.tendsto_harmonic_div_log
    have hcomplex' : Tendsto
        (fun N : ℕ => ((((harmonic N : ℝ) / Real.log N : ℝ)) : ℂ))
        atTop (nhds 1) := by
      simpa only [Complex.ofReal_one] using!
        (Complex.continuous_ofReal.continuousAt.tendsto.comp hreal)
    have hcomplex : Tendsto
        (fun N : ℕ => ((harmonic N : ℝ) : ℂ) / (Real.log N : ℂ))
        atTop (nhds 1) := by
      refine hcomplex'.congr' ?_
      filter_upwards with N
      push_cast
      rfl
    refine hcomplex.congr' ?_
    filter_upwards with N
    rw [integerHarmonicOrdinateKernel]
    congr 1
    rw [harmonic]
    push_cast
    apply Finset.sum_congr rfl
    intro n hn
    rw [gpow]
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    have hcoef : (-1 + ((-2 * (0 : ℝ) : ℝ) : ℂ) * I) = (-1 : ℂ) := by
      norm_num
    rw [hcoef, neg_one_mul, Complex.exp_neg, ← Complex.ofReal_exp,
      Real.exp_log hpos]
    push_cast
    rfl
  · simp only [if_neg hdelta]
    exact GaloisForLFunctions.tendsto_dirichlet_line_div_log
      (-2 * delta) (mul_ne_zero (by norm_num) hdelta)

/-- Cubic zero-pair trace with source-native integer-harmonic dephasing. -/
def finiteHolomorphicCubicIntegerHarmonicTrace {ι : Type*}
    (s : Finset ι) (a gamma : ι → ℝ) (m : ι → ℕ) (N : ℕ) : ℂ :=
  ∑ p ∈ s.product s,
    ((m p.1 : ℝ) * (m p.2 : ℝ) : ℂ) *
      holomorphicCubicLaplaceKernel (a p.1 + a p.2) (gamma p.1 - gamma p.2) *
        integerHarmonicOrdinateKernel (gamma p.1 - gamma p.2) N

/-- The source-native trace converges to the same equal-ordinate cubic fibre energy as the
post-divisor Bohr model. -/
theorem tendsto_finiteHolomorphicCubicIntegerHarmonicTrace {ι : Type*}
    (s : Finset ι) (a gamma : ι → ℝ) (m : ι → ℕ) :
    Tendsto (finiteHolomorphicCubicIntegerHarmonicTrace s a gamma m) atTop
      (nhds (finiteHolomorphicCubicOrdinateFiberEnergy s a gamma m : ℂ)) := by
  classical
  rw [finiteHolomorphicCubicOrdinateFiberEnergy, Complex.ofReal_sum]
  simp only [Finset.sum_filter, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_pow]
  unfold finiteHolomorphicCubicIntegerHarmonicTrace
  apply tendsto_finsetSum
  intro p hp
  have hphase := tendsto_integerHarmonicOrdinateKernel (gamma p.1 - gamma p.2)
  have hscaled := hphase.const_mul
    (((m p.1 : ℝ) * (m p.2 : ℝ) : ℂ) *
      holomorphicCubicLaplaceKernel (a p.1 + a p.2) (gamma p.1 - gamma p.2))
  by_cases hgamma : gamma p.1 = gamma p.2
  · have hzero : gamma p.1 - gamma p.2 = 0 := sub_eq_zero.mpr hgamma
    rw [hzero, holomorphicCubicLaplaceKernel_zero_gap] at hscaled
    rw [if_pos hgamma, hzero, holomorphicCubicLaplaceKernel_zero_gap]
    push_cast at hscaled ⊢
    simpa using hscaled
  · rw [if_neg hgamma]
    have hne : gamma p.1 - gamma p.2 ≠ 0 := sub_ne_zero.mpr hgamma
    simp only [if_neg hne, mul_zero] at hscaled
    simpa only [if_neg hne, mul_zero] using hscaled

end

end RHTower
