import GaloisForLFunctions.ArithmeticDefectRigidity.ResettingTheMovingOriginAddsTheMaxKernel
import GaloisForLFunctions.ArithmeticDefectRigidity.PositiveOriginMixturesAreFaithful

/-!
# Escape realizes every positive origin boundary

For every positive boundary mass, escaping actual sources admit moving
origins whose own-normalized Gram is a faithful max-kernel mixture. These
are shifted rows; the construction does not identify them as unshifted
actual cofactor limits.
-/

section
noncomputable section
set_option autoImplicit false
open scoped NNReal
open Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Escape realizes every positive reset-origin boundary as a faithful Wiener Gram module. -/
theorem admits_or_every_positive_faithful_boundary_is_realized (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨ ∀ c : ℝ≥0, 0 < (c : ℝ) →
      ∃ (L : ActualCofactorLimit ε) (h : ℕ → ℕ),
        (∀ᶠ m in atTop, h m < L.subsequence m) ∧
        Tendsto (fun m => pmPowerDampedCenteredDivisorPrefix ε (h m) ^ 2 /
          dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 (c : ℝ)) ∧
        (∀ j k : ℕ+, Tendsto (fun m =>
          pronicPairing (L.subsequence m + 1)
            (rowDilate j (resetOriginReceiver ε (h m)))
            (rowDilate k (resetOriginReceiver ε (h m))) /
              pronicNorm (L.subsequence m + 1) (resetOriginReceiver ε (h m)) ^ 2) atTop
          (𝓝 (MixedOriginModule.kernel L c j k))) ∧
        MixedOriginModule.annihilator L c = ⊥ ∧ MixedOriginModule.hull L c = Set.univ := by
  rcases admits_or_every_positive_resetOrigin_boundary_is_realized ε with hpaid | hrealize
  · exact Or.inl hpaid
  refine Or.inr fun c hc => ?_
  obtain ⟨L, h, hbefore, htrace, hgram⟩ := hrealize c hc
  refine ⟨L, h, hbefore, htrace, ?_, MixedOriginModule.annihilator_eq_bot L c hc,
    MixedOriginModule.hull_eq_univ L c hc⟩
  intro j k
  simpa only [MixedOriginModule.kernel, OriginStepModule.kernel, mul_one_div] using hgram j k

/-- Zero step mass recovers the original actual Gram exactly. -/
theorem mixedOrigin_kernel_zero {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    MixedOriginModule.kernel L 0 = L.kernel := by
  funext j k
  simp only [MixedOriginModule.kernel, NNReal.coe_zero, zero_mul, add_zero, div_one]

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.admits_or_every_positive_faithful_boundary_is_realized
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.mixedOrigin_kernel_zero
end
end
