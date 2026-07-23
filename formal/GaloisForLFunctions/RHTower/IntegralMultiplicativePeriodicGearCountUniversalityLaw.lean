import GaloisForLFunctions.RHTower.UnboundedGearCount
import GaloisForLFunctions.RHTower.DichotomyInstances

/-!
# Integral multiplicative periodic gear-count universality

The integral multiplicative functional-equation class has members with arbitrarily many distinct
off-critical real zero locations. Its class-wide periodicity dichotomy promotes every one of
those zeros to a full two-sided vertical progression. Hence one carrier can contain arbitrarily
many distinct off-critical periodic zero combs.
-/

open Complex

namespace RHTower

noncomputable section

/-- **Integral multiplicative periodic gear-count universality law.** For every finite bound, one
integral multiplicative degree-zero functional-equation carrier has at least that many distinct
real parts in `(0, 1/2)`, each supporting a full two-sided vertical arithmetic progression of
zeros. -/
theorem integralMultiplicativeFEClass_periodicGearCount_unbounded (n : ℕ) :
    ∃ f, IntegralMultiplicativeFEClass f ∧ ∃ R : Finset ℝ,
      n ≤ R.card ∧
      ∀ σ ∈ R, 0 < σ ∧ σ < 1 / 2 ∧
        ∃ T : ℝ, 0 < T ∧
          ∀ k : ℤ, f ((σ : ℂ) + (k * T) * Complex.I) = 0 := by
  obtain ⟨f, hf, R, hcard, hR⟩ :=
    integralMultiplicativeFEClass_gear_count_unbounded n
  refine ⟨f, hf, R, hcard, ?_⟩
  intro σ hσ
  obtain ⟨hσ0, hσhalf, hzero⟩ := hR σ hσ
  have hσone : σ < 1 := hσhalf.trans (by norm_num)
  rcases integralMultiplicativeFEClass_periodicityDichotomy hf
      (σ : ℂ) (by simpa using hσ0) (by simpa using hσone) hzero with
    hline | hperiodic
  · have : σ = 1 / 2 := by simpa using hline
    exact (hσhalf.ne this).elim
  · exact ⟨hσ0, hσhalf, hperiodic⟩

end

end RHTower
