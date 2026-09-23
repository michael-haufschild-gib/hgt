import GaloisForLFunctions.RHTower.RouteEPCubicHellingerPluckerLoadBridge

/-!
# Route E/P cubic source-normalization debt

The unit-diagonal fourth-depth block clears the local SP-E quadratic floor, but unit normalization
is not free on Route P's coefficient-faithful prime--Gamma carrier.  Each arithmetic depth square
contracts transported cubic diagonal energy by `1/8`; two iterations therefore contract by
`1/64`.

Keeping that native source weight changes the canonical fourth-depth pair ratio from
`11529/62500` to `737856/66015625`, which lies strictly below both `13/98` and `1/6`.  Thus the
unit-normalized block cannot itself be used as a source-faithful cofinal assembly.

The obstruction is exact.  Restoring equal diagonal energy requires, and for nonnegative gain
uniquely requires, an extra amplitude factor `8`.  Rebalancing raises pair trace from `65w/64` to
`2w`, an exact trace debt `63w/64`.  Any completed Route E/P/SP-E construction must therefore
supply this factor through a genuine Gamma/co-Poisson/Stokes correction or pay the corresponding
global budget; it cannot be inserted as a harmless normalization.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

private theorem routePPrimitiveBaseCauchyCubicWeight_pos_forNormalizationDebt
    (pe : Nat.Primes × ℕ) :
    0 < routePPrimitiveBaseCauchyCubicWeight pe := by
  rw [routePPrimitiveBaseCauchyCubicWeight,
    xiGammaEulerPrimitiveCubicLogMomentWeight, invNatLogSq]
  have hp : (0 : ℝ) < (pe.1 : ℝ) := by
    exact_mod_cast pe.1.property.pos
  have hlog : 0 < Real.log (pe.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast pe.1.property.one_lt)
  positivity

/-- Combined coefficient-preserving modular gain for two arithmetic depth-square steps. -/
def routePPrimitiveFourthDepthModularGain (pe : Nat.Primes × ℕ) : ℝ :=
  routePPrimitiveDepthSquareModularGain (routePPrimitiveDepthSquare pe) *
    routePPrimitiveDepthSquareModularGain pe

/-- Two coefficient-faithful depth-square steps contract native cubic source energy by `1/64`. -/
theorem routePPrimitiveFourthDepth_cubicWeight_modularGain_sq
    (pe : Nat.Primes × ℕ) :
    xiGammaEulerPrimitiveCubicLogMomentWeight (routePPrimitiveFourthDepth pe) *
        routePPrimitiveFourthDepthModularGain pe ^ (2 : ℕ) =
      xiGammaEulerPrimitiveCubicLogMomentWeight pe / 64 := by
  rw [routePPrimitiveFourthDepth, routePPrimitiveFourthDepthModularGain, mul_pow]
  rw [← mul_assoc,
    routePPrimitiveDepthSquare_cubicWeight_modularGain_sq
      (routePPrimitiveDepthSquare pe)]
  calc
    xiGammaEulerPrimitiveCubicLogMomentWeight (routePPrimitiveDepthSquare pe) / 8 *
          routePPrimitiveDepthSquareModularGain pe ^ (2 : ℕ) =
        (xiGammaEulerPrimitiveCubicLogMomentWeight (routePPrimitiveDepthSquare pe) *
          routePPrimitiveDepthSquareModularGain pe ^ (2 : ℕ)) / 8 := by ring
    _ = (xiGammaEulerPrimitiveCubicLogMomentWeight pe / 8) / 8 := by
      rw [routePPrimitiveDepthSquare_cubicWeight_modularGain_sq]
    _ = xiGammaEulerPrimitiveCubicLogMomentWeight pe / 64 := by ring

/-- The literal base-Cauchy diagonal obeys the same fourth-depth `1/64` contraction. -/
theorem routePPrimitiveFourthDepth_baseCauchyWeight_modularGain_sq
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveBaseCauchyCubicWeight (routePPrimitiveFourthDepth pe) *
        routePPrimitiveFourthDepthModularGain pe ^ (2 : ℕ) =
      routePPrimitiveBaseCauchyCubicWeight pe / 64 := by
  rw [routePPrimitiveBaseCauchyCubicWeight,
    routePPrimitiveBaseCauchyCubicWeight]
  calc
    216 / 115 * xiGammaEulerPrimitiveCubicLogMomentWeight
          (routePPrimitiveFourthDepth pe) *
          routePPrimitiveFourthDepthModularGain pe ^ (2 : ℕ) =
        216 / 115 *
          (xiGammaEulerPrimitiveCubicLogMomentWeight
            (routePPrimitiveFourthDepth pe) *
              routePPrimitiveFourthDepthModularGain pe ^ (2 : ℕ)) := by ring
    _ = 216 / 115 *
          (xiGammaEulerPrimitiveCubicLogMomentWeight pe / 64) := by
      rw [routePPrimitiveFourthDepth_cubicWeight_modularGain_sq]
    _ = (216 / 115 * xiGammaEulerPrimitiveCubicLogMomentWeight pe) / 64 := by ring

/-- Exact unweighted cubic Pluecker defect of the fourth-depth rate pair. -/
theorem routePPrimitiveFourthDepth_cubicPluckerDefect
    (pe : Nat.Primes × ℕ) :
    1 - routePBaseCauchyCubicNormalizedCoherenceSq
          (xiGammaEulerPrimitiveLogFrequency pe)
          (xiGammaEulerPrimitiveLogFrequency (routePPrimitiveFourthDepth pe)) 0 =
      11529 / 15625 := by
  have h := routeEPCubicNormalizedPairGramRatio_primitiveFourthDepth pe
  unfold routeEPCubicNormalizedPairGramRatio at h
  nlinarith

/-- Scale-free degree-two ratio of a two-column Gram with prescribed diagonal weights and
normalized Pluecker defect. -/
def routeEPCubicWeightedPairGramRatio (left right defect : ℝ) : ℝ :=
  left * right * defect / (left + right) ^ (2 : ℕ)

/-- Actual degree-two ratio after coefficient-faithful transport to the fourth-depth partner. -/
def routeEPCubicSourceFaithfulFourthDepthPairGramRatio
    (pe : Nat.Primes × ℕ) : ℝ :=
  routeEPCubicWeightedPairGramRatio
    (routePPrimitiveBaseCauchyCubicWeight pe)
    (routePPrimitiveBaseCauchyCubicWeight (routePPrimitiveFourthDepth pe) *
      routePPrimitiveFourthDepthModularGain pe ^ (2 : ℕ))
    (1 - routePBaseCauchyCubicNormalizedCoherenceSq
      (xiGammaEulerPrimitiveLogFrequency pe)
      (xiGammaEulerPrimitiveLogFrequency (routePPrimitiveFourthDepth pe)) 0)

/-- Exact source-faithful fourth-depth pair ratio.  The prime and depth cancel projectively. -/
theorem routeEPCubicSourceFaithfulFourthDepthPairGramRatio_eq
    (pe : Nat.Primes × ℕ) :
    routeEPCubicSourceFaithfulFourthDepthPairGramRatio pe =
      737856 / 66015625 := by
  rw [routeEPCubicSourceFaithfulFourthDepthPairGramRatio,
    routePPrimitiveFourthDepth_baseCauchyWeight_modularGain_sq,
    routePPrimitiveFourthDepth_cubicPluckerDefect]
  unfold routeEPCubicWeightedPairGramRatio
  have hw := routePPrimitiveBaseCauchyCubicWeight_pos_forNormalizationDebt pe
  field_simp [hw.ne']
  ring

/-- Source-faithful transport falls strictly below the uniform-Boolean `13/98` ceiling. -/
theorem routeEPCubicSourceFaithfulFourthDepthPairGramRatio_lt_thirteen_div_ninetyEight
    (pe : Nat.Primes × ℕ) :
    routeEPCubicSourceFaithfulFourthDepthPairGramRatio pe < 13 / 98 := by
  rw [routeEPCubicSourceFaithfulFourthDepthPairGramRatio_eq]
  norm_num

/-- Source-faithful transport also falls strictly below the theta floor `1/6`. -/
theorem routeEPCubicSourceFaithfulFourthDepthPairGramRatio_lt_one_div_six
    (pe : Nat.Primes × ℕ) :
    routeEPCubicSourceFaithfulFourthDepthPairGramRatio pe < 1 / 6 := by
  rw [routeEPCubicSourceFaithfulFourthDepthPairGramRatio_eq]
  norm_num

/-- Abstract balance law: a `1/64` energy carrier is restored exactly by squared gain `64`. -/
theorem routeEPCubic_fourthDepth_rebalance_iff
    {w c : ℝ} (hw : 0 < w) :
    w / 64 * c ^ (2 : ℕ) = w ↔ c ^ (2 : ℕ) = 64 := by
  constructor
  · intro h
    apply (mul_left_cancel₀ hw.ne')
    nlinarith
  · intro h
    rw [h]
    ring

/-- Among nonnegative amplitudes, the unique fourth-depth rebalancing factor is `8`. -/
theorem routeEPCubic_fourthDepth_rebalance_eq_eight
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hbalance : w / 64 * c ^ (2 : ℕ) = w) :
    c = 8 := by
  have hc2 : c ^ (2 : ℕ) = 64 :=
    (routeEPCubic_fourthDepth_rebalance_iff hw).mp hbalance
  nlinarith

/-- On the literal prime--Gamma carrier, rebalancing the transported fourth-depth column is
equivalent to multiplying its amplitude by a square root of `64`. -/
theorem routePPrimitiveFourthDepth_baseCauchy_rebalance_iff
    (pe : Nat.Primes × ℕ) (c : ℝ) :
    routePPrimitiveBaseCauchyCubicWeight (routePPrimitiveFourthDepth pe) *
          (routePPrimitiveFourthDepthModularGain pe * c) ^ (2 : ℕ) =
        routePPrimitiveBaseCauchyCubicWeight pe ↔
      c ^ (2 : ℕ) = 64 := by
  rw [mul_pow, ← mul_assoc,
    routePPrimitiveFourthDepth_baseCauchyWeight_modularGain_sq]
  exact routeEPCubic_fourthDepth_rebalance_iff
    (routePPrimitiveBaseCauchyCubicWeight_pos_forNormalizationDebt pe)

/-- Source-native uniqueness: every nonnegative balancing correction is exactly `8`. -/
theorem routePPrimitiveFourthDepth_baseCauchy_rebalance_eq_eight
    (pe : Nat.Primes × ℕ) {c : ℝ} (hc : 0 ≤ c)
    (hbalance :
      routePPrimitiveBaseCauchyCubicWeight (routePPrimitiveFourthDepth pe) *
          (routePPrimitiveFourthDepthModularGain pe * c) ^ (2 : ℕ) =
        routePPrimitiveBaseCauchyCubicWeight pe) :
    c = 8 := by
  have hc2 :=
    (routePPrimitiveFourthDepth_baseCauchy_rebalance_iff pe c).mp hbalance
  nlinarith

/-- Coefficient-faithful pair trace is only `65/64` times the parent diagonal. -/
theorem routePPrimitiveFourthDepth_sourceFaithful_pairTrace
    (pe : Nat.Primes × ℕ) :
    routePPrimitiveBaseCauchyCubicWeight pe +
        routePPrimitiveBaseCauchyCubicWeight (routePPrimitiveFourthDepth pe) *
          routePPrimitiveFourthDepthModularGain pe ^ (2 : ℕ) =
      65 / 64 * routePPrimitiveBaseCauchyCubicWeight pe := by
  rw [routePPrimitiveFourthDepth_baseCauchyWeight_modularGain_sq]
  ring

/-- Exact trace cost of replacing a coefficient-faithful `1/64` partner by a balanced partner. -/
theorem routeEPCubic_fourthDepth_rebalancingTraceDebt (w : ℝ) :
    2 * w - (w + w / 64) = 63 / 64 * w := by
  ring

end

end RHTower
