import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalL2Arithmetic
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalL2WeilNormalization
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarHalfLineDomain

/-!
# Full critical Suzuki variation for compact real L² sources

The literal arithmetic pairing converges to the extended Weil energy, with
all Gamma, prime, and polar terms retained. Only the nonnegative Lévy energy
can be infinite. In that case the normalized deficit tends to positive
infinity and the literal source pairing is strictly below its mass.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ENNReal
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm


namespace RHTower
noncomputable section

private theorem exp_neg_half_log {n : ℕ} (hn : 1 ≤ n) :
    Real.exp (-Real.log n/2) = 1/Real.sqrt n := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hn0.le, Real.rpow_def_of_pos hn0]
  congr 1
  ring

private theorem finite_prime_polar {f : ℝ → ℝ} {A : ℝ}
    (hcut : ∀ t : ℝ, A ≤ t → autocorr f t = 0) :
    4*(∫ t in Ioi 0, autocorr f t * Real.cosh (t/2)) -
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
        (2*ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n/2))*autocorr f (Real.log n) =
      -2*fullPairing (autocorr f) := by
  have htail : ∀ n : ℕ, n ∉ Finset.Icc 2 ⌊Real.exp A⌋₊ → primeTerm (autocorr f) n = 0 := by
    intro n hn
    by_cases h2 : 2 ≤ n
    · have hN : ⌊Real.exp A⌋₊ < n := by
        simp only [Finset.mem_Icc] at hn
        omega
      have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
      have he : Real.exp A < n := by
        calc
          _ < (⌊Real.exp A⌋₊ : ℝ)+1 := Nat.lt_floor_add_one _
          _ ≤ n := by exact_mod_cast Nat.succ_le_iff.mpr hN
      have hlog : A ≤ Real.log n := ((Real.lt_log_iff_exp_lt hn0).mpr he).le
      rw [primeTerm, if_pos h2, hcut _ hlog, mul_zero]
    · rw [primeTerm, if_neg h2]
  have hts : (∑' n : ℕ, primeTerm (autocorr f) n) =
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊, primeTerm (autocorr f) n := tsum_eq_sum htail
  have hprime : (∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
      (2*ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n/2))*autocorr f (Real.log n)) =
      2*∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊, primeTerm (autocorr f) n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn2 := (Finset.mem_Icc.mp hn).1
    rw [primeTerm, if_pos hn2, primeWeight, exp_neg_half_log (by omega : 1 ≤ n)]
    ring
  have hpolar : (∫ t in Ici (0 : ℝ), polarDensity t * autocorr f t) =
      2*∫ t in Ioi 0, autocorr f t * Real.cosh (t/2) := by
    rw [integral_Ici_eq_integral_Ioi, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    unfold polarDensity
    ring
  rw [fullPairing, hts, hpolar, hprime]
  ring

private theorem finite_energy_normalization {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfc : HasCompactSupport f) {A : ℝ}
    (hcut : ∀ t : ℝ, A ≤ t → autocorr f t = 0) :
    (suzukiCriticalLimitingCompensatedEnergy (fun t => autocorr f 0-autocorr f t) : EReal) +
      ((((Complex.digamma ((5/4 : ℝ) : ℂ)).re-Real.log Real.pi)*autocorr f 0 +
        2*(∫ t in Ioi 0, autocorr f t * Real.exp (t/2)) -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
          (2*ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n/2))*
            autocorr f (Real.log n)) : ℝ) =
      (sourceLevyEnergy f : EReal) +
        ((EF.gammaBracket 0 * autocorr f 0-2*fullPairing (autocorr f) : ℝ) : EReal) := by
  have h := congrArg (fun z : EReal => z +
    ((-(∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
      (2*ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n/2))*
        autocorr f (Real.log n)) : ℝ) : EReal)) (suzukiCriticalL2Weil_normalization hf hfc)
  simp only [add_assoc, ← EReal.coe_add, ← sub_eq_add_neg] at h
  have hreal : EF.gammaBracket 0 * autocorr f 0 +
      4*(∫ t in Ioi 0, autocorr f t * Real.cosh (t/2)) -
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
        (2*ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n/2))*autocorr f (Real.log n) =
      EF.gammaBracket 0 * autocorr f 0-2*fullPairing (autocorr f) := by
    have hp := finite_prime_polar hcut
    linarith only [hp]
  rw [hreal] at h
  exact h

/-- Every compact real L² source has its full extended Weil first variation. -/
theorem tendsto_suzukiCriticalSourcePairing_extended_firstVariation {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfc : HasCompactSupport f) :
    Tendsto (fun omega : ℝ =>
      (((autocorr f 0-suzukiCriticalSourcePairing f omega)/omega : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 ((sourceLevyEnergy f : EReal) +
        ((EF.gammaBracket 0 * autocorr f 0-2*fullPairing (autocorr f) : ℝ) : EReal))) := by
  obtain ⟨A,hA,hcut⟩ := exists_pos_autocorr_cutoff hfc
  have h := tendsto_suzukiCriticalSourcePairing_extended_firstVariation_finite hf hfc hA hcut
  rw [finite_energy_normalization hf hfc hcut] at h
  exact h

/-- Infinite Lévy energy forces a strict literal source deficit at all sufficiently small shifts. -/
theorem eventually_suzukiCriticalSourcePairing_lt_mass_of_infiniteEnergy {f : ℝ → ℝ}
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f) (hJ : sourceLevyEnergy f = ⊤) :
    ∀ᶠ omega : ℝ in 𝓝[>] 0, suzukiCriticalSourcePairing f omega < autocorr f 0 := by
  have h := tendsto_suzukiCriticalSourcePairing_extended_firstVariation hf hfc
  rw [hJ, EReal.coe_ennreal_top, EReal.top_add_coe] at h
  have he := h.eventually (Ioi_mem_nhds (show (0 : EReal)<⊤ by simp))
  filter_upwards [self_mem_nhdsWithin, he] with omega homega hq
  change 0 < omega at homega
  have hq' : 0 < (autocorr f 0-suzukiCriticalSourcePairing f omega)/omega := EReal.coe_pos.mp hq
  have hpos := (lt_div_iff₀ homega).mp hq'
  simp only [zero_mul] at hpos
  exact sub_pos.mp hpos

end
end RHTower
