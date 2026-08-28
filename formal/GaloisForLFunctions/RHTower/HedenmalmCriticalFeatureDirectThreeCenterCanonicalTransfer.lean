import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureCanonicalHeightWindow
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureDirectThreeCenterHolomorphicCharge

/-!
# Canonical source gate at the direct three-center HCF constant

The direct holomorphic-square receiver raises the admissible corrected HCF source ceiling from
`1452/4225` to `7936/21125`.  On the canonical height window the von Mangoldt channel is already
`o(N)`, so this file records the exact remaining source-only target at that improved constant.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- At the direct three-center constant, the corrected HCF budget ceiling is equivalent to the
zero-independent pole--Gamma Plemelj covariance ceiling. -/
theorem canonical_correctedBudget_ceiling_iff_plemeljCovariance_ceiling_directThreeCenter :
    CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePrimeGammaOffLineLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n))
        (7936 / 21125) ↔
      CriticalFeatureCanonicalAsymptoticUpper
        (fun n => criticalFeaturePoleGammaPlemeljCovariance
          (criticalFeatureCanonicalLatticeWindow n))
        (7936 / 21125) := by
  have hdiff := tendsto_canonical_correctedBudget_sub_plemeljCovariance_div
  have htransfer (X Y : ℕ → ℝ)
      (hXY : Tendsto
        (fun n => (X n - Y n) / criticalFeatureCanonicalZeroCount n)
        atTop (𝒩 0))
      (hY : CriticalFeatureCanonicalAsymptoticUpper Y (7936 / 21125)) :
      CriticalFeatureCanonicalAsymptoticUpper X (7936 / 21125) := by
    intro ε hε
    have hY' := hY (ε / 2) (by linarith)
    have herr : ∀ᶠ n : ℕ in atTop,
        (X n - Y n) / criticalFeatureCanonicalZeroCount n < ε / 2 :=
      (tendsto_order.1 hXY).2 _ (by linarith)
    filter_upwards [hY', herr, eventually_criticalFeatureCanonicalZeroCount_pos]
      with n hYn heren hN
    have hdiffn : X n - Y n <
        (ε / 2) * criticalFeatureCanonicalZeroCount n :=
      (div_lt_iff₀ hN).mp heren
    nlinarith
  constructor
  · intro hcorrected
    apply htransfer _ _ ?_ hcorrected
    have hneg := hdiff.neg
    simp only [neg_zero] at hneg
    convert hneg using 1
    funext n
    ring
  · exact htransfer _ _ hdiff

end

end RHTower
