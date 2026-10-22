import GaloisForLFunctions.RHTower.CriticalContinuousChebyshevDivisorLaplaceWeld
import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinGrowingCumulativeBound
import GaloisForLFunctions.RHTower.ChebyshevThetaPowerLog
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalSourceCurrentNonconstancy
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalMellinMass
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalSourceFiniteJet

noncomputable section
open Complex MeasureTheory Set ArithmeticFunction Finset Filter Topology
namespace RHTower

def criticalStepSourceMellin (s : ℂ) : ℂ :=
  ∫ t in Ioi (1 : ℝ),
    (psiDefect ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1))

private theorem stepCumulative_eq_psiDefect (t : ℝ) :
    (psiDefect ⌊t⌋₊ : ℂ) =
      (criticalCumulative (fun n => vonMangoldt n) t : ℂ) -
        ((⌊t⌋₊ : ℕ) : ℂ) + 2 * (Real.eulerMascheroniConstant : ℂ) := by
  rw [criticalCumulative_vonMangoldt_eq_chebyshevPsi,
    psi_eq_chebyshevPsi_floor]
  simp only [psiDefect]
  push_cast
  ring

private theorem floor_natCast_eq_self_sub_fract {t : ℝ} (ht : 0 ≤ t) :
    ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - ((Int.fract t : ℝ) : ℂ) := by
  have h : ((⌊t⌋₊ : ℕ) : ℤ) = ⌊t⌋ := Int.natCast_floor_eq_floor ht
  have h2 : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
    have h3 : ((⌊t⌋₊ : ℕ) : ℝ) = ((⌊t⌋ : ℤ) : ℝ) := by
      exact_mod_cast congrArg (fun n : ℤ => (n : ℝ)) h
    rw [h3, Int.self_sub_fract]
  rw [show ((⌊t⌋₊ : ℕ) : ℂ) = (((⌊t⌋₊ : ℕ) : ℝ) : ℂ) by push_cast; ring, h2]
  push_cast
  ring

private theorem integrableOn_floor_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hlin := integrableOn_linear_mul_cpow hs
  have hfract := integrableOn_Ioi_one_fract_cpow (by linarith)
  refine (hlin.sub hfract).congr_fun ?_ measurableSet_Ioi
  intro t ht
  change (t : ℂ) * (t : ℂ) ^ (-(s + 1)) -
      ((Int.fract t : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) =
      ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1))
  rw [floor_natCast_eq_self_sub_fract (le_of_lt (lt_trans one_pos ht))]
  ring

private theorem integral_Ioi_one_cpow_shift {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (-(s + 1))) = 1 / s := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  rw [integral_Ioi_cpow_of_lt (by
    rw [Complex.neg_re, Complex.add_re, Complex.one_re]
    linarith) one_pos, Complex.ofReal_one, Complex.one_cpow]
  rw [show -(s + 1) + 1 = -s by ring]
  simp

/-- Mellin identity of the exact stepwise critical source. -/
theorem criticalStepSourceMellin_eq_centeredCurrentGap
    {s : ℂ} (hs : 1 < s.re) :
    criticalStepSourceMellin s =
      (centeredPrimeTailCurrentContinuation 1 -
        centeredPrimeTailCurrentContinuation s) / s := by
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hcum := integrableOn_criticalCumulative_mul_cpow hs
  have hfloor := integrableOn_floor_mul_cpow hs
  have hpow := integrableOn_Ioi_one_cpow (by linarith : 0 < s.re)
  have hconst : IntegrableOn
      (fun t : ℝ => (2 * (Real.eulerMascheroniConstant : ℂ)) *
        (t : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    hpow.const_mul _
  have hsource : ∀ t ∈ Ioi (1 : ℝ),
      (psiDefect ⌊t⌋₊ : ℂ) * (t : ℂ) ^ (-(s + 1)) =
        (criticalCumulative (fun n => vonMangoldt n) t : ℂ) *
          (t : ℂ) ^ (-(s + 1)) -
        ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1)) +
        (2 * (Real.eulerMascheroniConstant : ℂ)) *
          (t : ℂ) ^ (-(s + 1)) := by
    intro t ht
    rw [stepCumulative_eq_psiDefect t]
    ring
  have hsplit : criticalStepSourceMellin s =
      (∫ t in Ioi (1 : ℝ),
        (criticalCumulative (fun n => vonMangoldt n) t : ℂ) *
          (t : ℂ) ^ (-(s + 1))) -
      (∫ t in Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1))) +
      (∫ t in Ioi (1 : ℝ),
        (2 * (Real.eulerMascheroniConstant : ℂ)) *
          (t : ℂ) ^ (-(s + 1))) := by
    rw [criticalStepSourceMellin,
      setIntegral_congr_fun measurableSet_Ioi hsource]
    have hsum := integral_add (hcum.sub hfloor) hconst
    simp only [Pi.sub_apply] at hsum
    rw [integral_sub hcum hfloor] at hsum
    simpa only [Pi.add_apply] using hsum
  have hcumval :
      (∫ t in Ioi (1 : ℝ),
        (criticalCumulative (fun n => vonMangoldt n) t : ℂ) *
          (t : ℂ) ^ (-(s + 1))) =
        LSeries (fun n => (vonMangoldt n : ℂ)) s / s := by
    have h := vonMangoldtLSeries_eq_mul_integral_criticalCumulative hs
    rw [h]
    field_simp
  have hfloorval :
      (∫ t in Ioi (1 : ℝ), ((⌊t⌋₊ : ℕ) : ℂ) * (t : ℂ) ^ (-(s + 1))) =
        riemannZeta s / s := by
    have h := riemannZeta_eq_mul_integral_floor hs
    rw [h]
    field_simp
  have hconstval :
      (∫ t in Ioi (1 : ℝ),
        (2 * (Real.eulerMascheroniConstant : ℂ)) *
          (t : ℂ) ^ (-(s + 1))) =
        2 * (Real.eulerMascheroniConstant : ℂ) / s := by
    rw [integral_const_mul, integral_Ioi_one_cpow_shift hs]
    ring
  rw [hsplit, hcumval, hfloorval, hconstval]
  rw [← infinitePrimeFlux_eq_vonMangoldtLSeries hs, infinitePrimeFlux]
  rw [← criticalSourceMellinNumerator_eq_centeredCurrentGap hs]
  ring

/-- The literal critical step-source Mellin integral is nonflat at the
convergence boundary: its zero at the pole is isolated on the right. -/
theorem criticalStepSourceMellin_eventually_ne_zero_right :
    ∀ᶠ s : ℂ in 𝓝 1, 1 < s.re → criticalStepSourceMellin s ≠ 0 := by
  obtain ⟨r, hr, g, hga, hg0, hfac⟩ := criticalSourceCurrentGap_finiteJet
  have hgne : ∀ᶠ s : ℂ in 𝓝 1, g s ≠ 0 :=
    hga.continuousAt.eventually_ne hg0
  filter_upwards [hfac, hgne] with s hs hgs hsr
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hsr
    norm_num at hsr
  have hs0 : s ≠ 0 := ne_zero_of_re_pos (by linarith)
  have hnum : centeredPrimeTailCurrentContinuation 1 -
      centeredPrimeTailCurrentContinuation s ≠ 0 := by
    rw [hs]
    exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hs1)) hgs
  rw [criticalStepSourceMellin_eq_centeredCurrentGap hsr]
  exact div_ne_zero hnum hs0

end RHTower
