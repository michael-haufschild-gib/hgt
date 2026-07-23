import GaloisForLFunctions.RHTower.VonMangoldtGammaFactorialBetaReflection
import GaloisForLFunctions.RHTower.VonMangoldtGammaCofinalStrictBianchiLaw

open Filter

namespace RHTower

noncomputable section

/-! Canonical factorial/Beta reflection reverses matrix-order phase of the positive raw
von Mangoldt--Gamma source on the first separated even-order packet. -/

/-- On the same even-order packet, the positive raw Gamma--Bianchi source and its canonical
factorial/Beta reflection eventually occupy opposite matrix-order phases. -/
theorem vonMangoldtGamma_betaReflectionPositivityGapUniversality :
    ∀ᶠ x : ℝ in atTop,
      (vonMangoldtGammaCofinalBianchiGram x ![0, 2]).PosDef ∧
        0 < (vonMangoldtGammaCofinalBianchiGram x ![0, 2]).det ∧
        ¬ (infiniteVonMangoldtGammaFactorialTraceGram x ![0, 2]).PosSemidef := by
  have hinj : Function.Injective (![0, 2] : Fin 2 → ℕ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  filter_upwards
    [eventually_gt_atTop (0 : ℝ),
      infiniteVonMangoldtGammaFactorialBetaReflection_eventually_not_posSemidef]
      with x hx hreflection
  have hraw := vonMangoldtGammaCofinalBianchiGram_posDef_of_injective hx ![0, 2] hinj
  exact ⟨hraw, hraw.det_pos, hreflection⟩

end

end RHTower
