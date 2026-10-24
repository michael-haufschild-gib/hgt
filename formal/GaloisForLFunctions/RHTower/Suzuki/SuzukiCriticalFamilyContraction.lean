import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalFirstVariation
import GaloisForLFunctions.«arithmetic-positivity-theory».CompactCriticalSourceWeilPositivity
import GaloisForLFunctions.«arithmetic-positivity-theory».FactorialRampFullWeilSmoothingLimit

/-!
# A strict Suzuki pairing deficit on compact critical arithmetic sources

High dyadic critical sources have positive complete Weil energy at every
allowed compact truncation. Finite-jump smoothing preserves that energy in
the limit, and the literal Suzuki tangent converts it into a strict
finite-shift deficit. The small-shift threshold depends on the source.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators CompactlySupported
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.CHMDDoobGraph

namespace RHTower
noncomputable section
set_option autoImplicit false

/-- Every sufficiently high nonzero dyadic critical source has smooth approximants
whose literal Suzuki pairings have a positive first-order deficit. The truncation
aperture is unrestricted; each approximant has its own positive-shift neighbourhood. -/
theorem exists_suzukiCriticalFamily_strict_deficit :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ V : ℝ, ∀ hV : 0 < V, criticalTruncationThreshold ≤ V →
      ∀ S : Finset ℕ, DyadicScaleBlock S M → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
        0 < compactFullWeilEnergy (criticalTruncatedTest hV S b) ∧
        ∀ᶠ k : ℕ in atTop, ∀ᶠ omega : ℝ in 𝓝[>] 0,
          omega * (compactFullWeilEnergy (criticalTruncatedTest hV S b) / 4) <
            autocorr (smoothCompactSource (criticalTruncatedTest hV S b) k) 0 -
              suzukiCriticalSourcePairing (smoothCompactSource (criticalTruncatedTest hV S b) k) omega ∧
          suzukiCriticalSourcePairing (smoothCompactSource (criticalTruncatedTest hV S b) k) omega <
            autocorr (smoothCompactSource (criticalTruncatedTest hV S b) k) 0 := by
  obtain ⟨M₀, hpositive⟩ := exists_compactFullWeilEnergy_criticalTruncatedTest_pos
  refine ⟨M₀, fun M hM V hV hVt S hS b hb => ?_⟩
  let g := criticalTruncatedTest hV S b
  have hg : 0 < compactFullWeilEnergy g := hpositive M hM V hV hVt S hS b hb
  refine ⟨hg, ?_⟩
  obtain ⟨K, hK⟩ := exists_lipschitz_criticalTruncatedSource hV S b
  have hJ := integrableOn_levy_of_lipschitz g hK
  have hlim := re_weilFullFunctional_smooth_tendsto g hJ
  have hkpos : ∀ᶠ k : ℕ in atTop,
      compactFullWeilEnergy g / 2 < compactFullWeilEnergy (smoothCompactSource g k) :=
    hlim.eventually (Ioi_mem_nhds (by change compactFullWeilEnergy g / 2 < compactFullWeilEnergy g; linarith))
  filter_upwards [hkpos] with k hk
  have hsm : ContDiff ℝ 2 (smoothCompactSource g k : ℝ → ℝ) :=
    smooth_contDiff (g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport) k
  have hvariation := tendsto_suzukiCriticalSourcePairing_firstVariation (smoothCompactSource g k) hsm
  have hmargin : compactFullWeilEnergy g / 4 <
      compactFullWeilEnergy (smoothCompactSource g k) := by linarith only [hg, hk]
  have hquotient := hvariation.eventually (Ioi_mem_nhds hmargin)
  filter_upwards [self_mem_nhdsWithin, hquotient] with omega homega hq
  change 0 < omega at homega
  change compactFullWeilEnergy g / 4 <
    (autocorr (smoothCompactSource g k) 0 -
      suzukiCriticalSourcePairing (smoothCompactSource g k) omega) / omega at hq
  have hdeficit : omega * (compactFullWeilEnergy g / 4) <
      autocorr (smoothCompactSource g k) 0 -
        suzukiCriticalSourcePairing (smoothCompactSource g k) omega := by
    simpa only [mul_comm] using (lt_div_iff₀ homega).mp hq
  exact ⟨hdeficit, by
    have hpos := mul_pos homega (div_pos hg (by norm_num : (0 : ℝ) < 4))
    linarith only [hdeficit, hpos]⟩

end
end RHTower

#print axioms RHTower.exists_suzukiCriticalFamily_strict_deficit
