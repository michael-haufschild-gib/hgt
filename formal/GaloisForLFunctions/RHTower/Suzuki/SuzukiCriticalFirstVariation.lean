import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalCuspEstimate
import GaloisForLFunctions.BiScaleUncertainty.CompactFiniteJumpWeilFormula

/-!
# The complete critical first variation of Suzuki's literal arithmetic source

The forming Gamma atom, both polar exponentials, and all prime-power cusps
recover the real complete Weil quadratic form on every compact smooth source.
The theorem asserts an exact tangent; it imposes no positivity premise.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators
open scoped CompactlySupported
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm

namespace RHTower
noncomputable section

private theorem exp_neg_half_log {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-Real.log n / 2) = 1 / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hn0.le, Real.rpow_def_of_pos hn0]
  congr 1
  ring

private theorem completeWeil_eq_finite (f : C_c(ℝ, ℝ)) (hf : ContDiff ℝ 2 (f : ℝ → ℝ))
    {A : ℝ} (hcut : ∀ t : ℝ, A ≤ t → autocorr f t = 0) :
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      EF.gammaBracket 0 * autocorr f 0 + biScaleLevyEnergy f +
        4 * (∫ t in Ioi 0, autocorr f t * Real.cosh (t / 2)) -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
          (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
            autocorr f (Real.log n) := by
  have htail : ∀ n : ℕ, n ∉ Finset.Icc 2 ⌊Real.exp A⌋₊ → primeTerm (autocorr f) n = 0 := by
    intro n hn
    by_cases h2 : 2 ≤ n
    · have hN : ⌊Real.exp A⌋₊ < n := by
        simp only [Finset.mem_Icc] at hn
        omega
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have he : Real.exp A < n := by
        calc
          _ < (⌊Real.exp A⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
          _ ≤ n := by exact_mod_cast Nat.succ_le_iff.mpr hN
      have hlog : A ≤ Real.log n := ((Real.lt_log_iff_exp_lt hn0).mpr he).le
      rw [primeTerm, if_pos h2, hcut _ hlog, mul_zero]
    · rw [primeTerm, if_neg h2]
  have hts : (∑' n : ℕ, primeTerm (autocorr f) n) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊, primeTerm (autocorr f) n :=
    tsum_eq_sum htail
  have hprime : (∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
      (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
        autocorr f (Real.log n)) =
      2 * ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊, primeTerm (autocorr f) n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn2 := (Finset.mem_Icc.mp hn).1
    rw [primeTerm, if_pos hn2, primeWeight, exp_neg_half_log (by omega : 1 ≤ n)]
    ring
  have hpolar : (∫ t in Ici (0 : ℝ), polarDensity t * autocorr f t) =
      2 * ∫ t in Ioi 0, autocorr f t * Real.cosh (t / 2) := by
    rw [integral_Ici_eq_integral_Ioi, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    unfold polarDensity
    ring
  rw [re_weilFullFunctional_eq_of_compact_finite_jump f
    (integrableOn_biScaleLevyIntegrand hf f.hasCompactSupport), fullPairing, hts, hpolar, hprime]
  ring

/-- The positive-shift first variation of the literal complete Suzuki source is exactly
Weil's full quadratic form. Compact smoothness discharges every analytic premise. -/
theorem tendsto_suzukiCriticalSourcePairing_firstVariation (f : C_c(ℝ, ℝ))
    (hf : ContDiff ℝ 2 (f : ℝ → ℝ)) :
    Tendsto (fun omega : ℝ =>
      (autocorr f 0 - suzukiCriticalSourcePairing f omega) / omega) (𝓝[>] 0)
      (𝓝 (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re) := by
  obtain ⟨A, hA, hcut⟩ := exists_suzukiCriticalCorrelation_cutoff f.hasCompactSupport
  have h := tendsto_suzukiCriticalSourcePairing_firstVariation_finite hf f.hasCompactSupport hA hcut
  rw [suzukiCriticalWeil_normalization hf f.hasCompactSupport,
    ← completeWeil_eq_finite f hf hcut] at h
  exact h

/-- Unbundled compact `C²` form of the complete source first-variation theorem. -/
theorem tendsto_suzukiCriticalSourcePairing_firstVariation_of_contDiff {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Tendsto (fun omega : ℝ =>
      (autocorr f 0 - suzukiCriticalSourcePairing f omega) / omega) (𝓝[>] 0)
      (𝓝 (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re) := by
  exact tendsto_suzukiCriticalSourcePairing_firstVariation
    (⟨⟨f, hf.continuous⟩, hfc⟩ : C_c(ℝ, ℝ)) hf

end
end RHTower
