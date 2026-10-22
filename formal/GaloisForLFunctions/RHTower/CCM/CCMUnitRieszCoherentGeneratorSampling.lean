import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszCoherentPolarSamplingNoGo

/-!
# Fixed-sample generator representation of the coherent packet

The coherent polar-sampling no-go leaves an exact positive survivor: the fixed lag-one sample of
the four-lag coherent packet is a fixed multiple of the packet's source-Gram quadratic, and hence
of its piecewise weak-generator graph energy.  This file records the second, generator-side form
of that representation.

The statement is unconditional and source-side.  It bounds no arithmetic packet and proves no
zero-free region.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

theorem unitExponentialThirdDifferenceCoefficient_pos (h : ℝ) :
    0 < unitExponentialThirdDifferenceCoefficient h := by
  unfold unitExponentialThirdDifferenceCoefficient
  have h₁ := Real.exp_pos (h / 2)
  have h₂ := Real.exp_pos (-h / 2)
  linarith

/-- **Exact generator representation of the fixed sample.**  The lag-one sample square of the
coherent packet is the packet's weak-generator graph energy times the explicit scale
`(exp(h/2) - exp(-h/2)) / (8 (1 + exp(h/2) + exp(-h/2)))`. -/
theorem unitExponentialThirdDifference_fixedSample_eq_generatorEnergy
    {h : ℝ} (hh : 0 < h) :
    unitExponentialThirdDifferenceResponse (1 - h) h 1 ^ (2 : ℕ) =
      ((Real.exp (h / 2) - Real.exp (-h / 2)) /
          (8 * unitExponentialThirdDifferenceCoefficient h)) *
        unitExponentialThirdDifferenceGeneratorEnergy (1 - h) h := by
  have hA : unitExponentialThirdDifferenceCoefficient h ≠ 0 :=
    (unitExponentialThirdDifferenceCoefficient_pos h).ne'
  rw [unitExponentialThirdDifferenceGeneratorEnergy_eq_sourceGram _ hh.le,
    unitExponentialThirdDifference_fixedSample_eq_sourceGram hh]
  field_simp
  ring

end GaloisForLFunctions.RHTower
