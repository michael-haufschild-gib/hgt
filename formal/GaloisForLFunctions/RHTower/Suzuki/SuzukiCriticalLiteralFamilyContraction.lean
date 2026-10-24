import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalL2FirstVariation
import GaloisForLFunctions.«arithmetic-positivity-theory».CompactCriticalSourceWeilPositivity

/-!
# Literal Suzuki deficits on the compact critical arithmetic family

The compact L² first variation applies directly to the Lipschitz critical
source. Its known complete Weil positivity therefore gives a strict literal
source deficit at all sufficiently small positive shifts, with every prime
and pole term retained.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators CompactlySupported
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.CHMDDoobGraph

namespace RHTower
noncomputable section

private theorem critical_energy_eq {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ) :
    (sourceLevyEnergy (criticalTruncatedTest hV S b) : EReal) +
      ((EF.gammaBracket 0 * autocorr (criticalTruncatedTest hV S b) 0 -
        2 * fullPairing (autocorr (criticalTruncatedTest hV S b)) : ℝ) : EReal) =
      (compactFullWeilEnergy (criticalTruncatedTest hV S b) : EReal) := by
  let f := criticalTruncatedTest hV S b
  have hf : MemLp (f : ℝ → ℝ) 2 volume :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  obtain ⟨K, hK⟩ := exists_lipschitz_criticalTruncatedSource hV S b
  have hJ := integrableOn_levy_of_lipschitz f (K := K) hK
  have hW := re_weilFullFunctional_eq_of_compact_finite_jump f hJ
  have hac (x : ℝ) : sourceAutocorrelation f x = autocorr f x := by
    rw [← autocorr_neg]
    unfold sourceAutocorrelation autocorr
    simp only [sub_eq_add_neg]
  have hnn : ∀ x ∈ Ioi (0 : ℝ),
      0 ≤ (autocorr f 0-autocorr f x) * archLevySinhWeight x := by
    intro x hx
    exact mul_nonneg (AutocorrelationKrein.deficit_nonneg hf x) (archLevySinhWeight_pos hx).le
  have hlev : (sourceLevyEnergy f : EReal) = (biScaleLevyEnergy f : ℝ) := by
    unfold sourceLevyEnergy biScaleLevyEnergy
    simp only [hac]
    rw [← ofReal_integral_eq_lintegral_ofReal hJ
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hnn)),
      EReal.coe_ennreal_ofReal, max_eq_left (setIntegral_nonneg measurableSet_Ioi hnn)]
  change (sourceLevyEnergy f : EReal) +
    ((EF.gammaBracket 0*autocorr f 0-2*fullPairing (autocorr f) : ℝ) : EReal) =
      (compactFullWeilEnergy f : EReal)
  rw [hlev, ← EReal.coe_add]
  congr 1
  unfold compactFullWeilEnergy
  rw [hW]
  ring

/-- The actual compact critical arithmetic source has its full Weil first variation. -/
theorem tendsto_suzukiCriticalLiteralFamily_firstVariation {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) :
    Tendsto (fun omega : ℝ =>
      (((autocorr (criticalTruncatedTest hV S b) 0-
        suzukiCriticalSourcePairing (criticalTruncatedTest hV S b) omega)/omega : ℝ) : EReal))
      (𝓝[>] 0) (𝓝 (compactFullWeilEnergy (criticalTruncatedTest hV S b) : EReal)) := by
  have hf : MemLp (criticalTruncatedTest hV S b : ℝ → ℝ) 2 volume :=
    (criticalTruncatedTest hV S b).continuous.memLp_of_hasCompactSupport
      (criticalTruncatedTest hV S b).hasCompactSupport
  have h := tendsto_suzukiCriticalSourcePairing_extended_firstVariation
    (f := (criticalTruncatedTest hV S b : ℝ → ℝ)) hf
    (criticalTruncatedTest hV S b).hasCompactSupport
  rw [critical_energy_eq hV S b] at h
  exact h

/-- High dyadic critical sources themselves have a strict literal Suzuki deficit. -/
theorem exists_suzukiCriticalLiteralFamily_strict_deficit :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ V : ℝ, ∀ hV : 0 < V, criticalTruncationThreshold ≤ V →
      ∀ S : Finset ℕ, DyadicScaleBlock S M → ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
        0 < compactFullWeilEnergy (criticalTruncatedTest hV S b) ∧
        ∀ᶠ omega : ℝ in 𝓝[>] 0,
          omega * (compactFullWeilEnergy (criticalTruncatedTest hV S b) / 2) <
            autocorr (criticalTruncatedTest hV S b) 0 -
              suzukiCriticalSourcePairing (criticalTruncatedTest hV S b) omega ∧
          suzukiCriticalSourcePairing (criticalTruncatedTest hV S b) omega <
            autocorr (criticalTruncatedTest hV S b) 0 := by
  obtain ⟨M₀, hpositive⟩ := exists_compactFullWeilEnergy_criticalTruncatedTest_pos
  refine ⟨M₀, fun M hM V hV hVt S hS b hb => ?_⟩
  let g := criticalTruncatedTest hV S b
  have hg : 0 < compactFullWeilEnergy g := hpositive M hM V hV hVt S hS b hb
  refine ⟨hg, ?_⟩
  have hlim := tendsto_suzukiCriticalLiteralFamily_firstVariation hV S b
  have hmargin : ((compactFullWeilEnergy g / 2 : ℝ) : EReal) <
      (compactFullWeilEnergy g : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
  have he := hlim.eventually (Ioi_mem_nhds hmargin)
  filter_upwards [self_mem_nhdsWithin, he] with omega homega hq
  change 0 < omega at homega
  have hq' : compactFullWeilEnergy g / 2 <
      (autocorr g 0-suzukiCriticalSourcePairing g omega)/omega := EReal.coe_lt_coe_iff.mp hq
  have hd : omega * (compactFullWeilEnergy g / 2) <
      autocorr g 0-suzukiCriticalSourcePairing g omega := by
    simpa only [mul_comm] using (lt_div_iff₀ homega).mp hq'
  exact ⟨hd, by
    have hp := mul_pos homega (div_pos hg (by norm_num : (0 : ℝ)<2))
    linarith only [hd, hp]⟩

end
end RHTower

#print axioms RHTower.suzukiCriticalCompensatedEnergy
#print axioms RHTower.suzukiCriticalLimitingCompensatedEnergy
#print axioms RHTower.tendsto_suzukiCriticalCompensatedEnergy
#print axioms RHTower.autocorr_congr_ae
#print axioms RHTower.autocorr_eq_inner_physicalTranslation
#print axioms RHTower.autocorr_eq_inner_toLp
#print axioms RHTower.continuous_autocorr_of_memLp
#print axioms RHTower.autocorr_zero_eq_norm_toLp_sq
#print axioms RHTower.abs_autocorr_le_zero_of_memLp
#print axioms RHTower.autocorr_sub_le_L2_norms
#print axioms RHTower.tendsto_suzukiCriticalCompensatedEnergy_autocorr
#print axioms RHTower.suzukiCriticalPrimaryCusp_congr_ae
#print axioms RHTower.integrableOn_suzukiCriticalPrimaryCusp_integrand_of_memLp
#print axioms RHTower.abs_suzukiCriticalPrimaryCusp_sub_le_L2_norms
#print axioms RHTower.tendstoUniformly_suzukiCriticalPrimaryCusp_L2
#print axioms RHTower.tendstoUniformly_suzukiCriticalPrimaryCusp_of_memLp
#print axioms RHTower.integrableOn_suzukiCriticalCompensatedAutocorr
#print axioms RHTower.integral_suzukiCriticalCompensatedAutocorr
#print axioms RHTower.coe_suzukiCriticalCompensatedEnergy_autocorr
#print axioms RHTower.tendsto_suzukiCriticalPrimaryCusp_extended_firstVariation
#print axioms RHTower.measurable_suzukiCriticalPoleDensity
#print axioms RHTower.suzukiCriticalPoleDensity_eq_zero_of_nonpos
#print axioms RHTower.suzukiCriticalSourceDensity_eq_zero_of_nonpos
#print axioms RHTower.suzukiCriticalPrimaryFirstMoment
#print axioms RHTower.integrableOn_suzukiCriticalPrimaryFirstMoment
#print axioms RHTower.tendsto_suzukiCriticalPrimaryFirstMoment
#print axioms RHTower.suzukiCriticalPoleDensity_bounds
#print axioms RHTower.tendsto_suzukiCriticalPoleDensity
#print axioms RHTower.integrable_suzukiCriticalPoleCusp_integrand_of_memLp
#print axioms RHTower.tendsto_suzukiCriticalPoleCusp_of_memLp
#print axioms RHTower.integrableOn_suzukiCriticalSourceCusp_integrand_of_memLp
#print axioms RHTower.suzukiCriticalSourceCusp_eq_of_memLp
#print axioms RHTower.tendsto_suzukiCriticalSourceCusp_of_memLp
#print axioms RHTower.tendsto_suzukiCriticalSourceCusp_extended_firstVariation
#print axioms RHTower.integrableOn_suzukiCriticalSourcePairing_of_memLp
#print axioms RHTower.suzukiCriticalSourcePairing_eq_finite_of_memLp
#print axioms RHTower.tendsto_suzukiCriticalSourcePairing_extended_firstVariation_finite
#print axioms RHTower.sourceLevyEnergy_eq_suzukiCriticalEnergy
#print axioms RHTower.coe_sourceLevyEnergy_eq_suzukiCriticalEnergy
#print axioms RHTower.suzukiCriticalL2Weil_normalization
#print axioms RHTower.tendsto_suzukiCriticalSourcePairing_extended_firstVariation
#print axioms RHTower.eventually_suzukiCriticalSourcePairing_lt_mass_of_infiniteEnergy
#print axioms RHTower.tendsto_suzukiCriticalLiteralFamily_firstVariation
#print axioms RHTower.exists_suzukiCriticalLiteralFamily_strict_deficit
