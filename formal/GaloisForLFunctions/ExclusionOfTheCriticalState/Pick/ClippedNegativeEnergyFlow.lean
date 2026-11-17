import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ClippedProbeIndex
import GaloisForLFunctions.HilbertMetric.Spectral.ClippedCertificates
import GaloisForLFunctions.HTGeometry.KernelNestedFiniteSectionInertia

/-!
# Negative probe energy along the confinement ratio

The zero-cutoff energy is the squared negative spectrum of a finite probe
matrix. It increases with the ratio because confinement decreases, and it is
zero throughout the positive regime, including the critical ratio. This is a
quantitative spectral observable of the finite index flow.
-/

open Matrix
open scoped ComplexOrder
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations HTGeometry HilbertMetric.Clipped
noncomputable section

/-- Increasing the ratio adds no confinement: the difference of the two matrices is positive. -/
theorem confinedProbeGram_difference_posSemidef {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S)
    {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) :
    (confinedProbeGram R p - confinedProbeGram S p).PosSemidef := by
  have he : confinedProbeGram R p - confinedProbeGram S p =
      ((criticalAliasCoefficient R - criticalAliasCoefficient S : ℝ) : ℂ) •
        probeConfinementGram p := by
    rw [confinedProbeGram_eq R hp, confinedProbeGram_eq S hp, Complex.ofReal_sub, sub_smul]
    abel
  rw [he]
  exact (probeConfinementGram_posSemidef hp).smul
    (Complex.nonneg_iff.mpr ⟨sub_nonneg.mpr (criticalAliasCoefficient_antitone hR hRS), rfl⟩)

/-- Squared negative spectral energy increases with the actual confinement ratio. -/
theorem confinedProbe_negativeEnergy_mono {R S : ℝ} (hR : 0 < R) (hRS : R ≤ S)
    {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) :
    energy 0 (confinedProbeGram R p) ≤ energy 0 (confinedProbeGram S p) :=
  energy_zero_antitone (confinedProbeGram_isHermitian (lt_of_lt_of_le hR hRS) hp)
    (confinedProbeGram_isHermitian hR hp) (confinedProbeGram_difference_posSemidef hR hRS hp)

/-- This real-valued observable vanishes exactly when the finite index is zero. -/
theorem confinedProbe_negativeEnergy_zero_iff {R : ℝ} (hR : 0 < R)
    {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) :
    energy 0 (confinedProbeGram R p) = 0 ↔ hermNegIndex (confinedProbeGram R p) = 0 := by
  rw [energy_zero_eq_zero_iff (confinedProbeGram_isHermitian hR hp),
    hermNegIndex_eq_zero_iff_posSemidef (confinedProbeGram_isHermitian hR hp)]

/-- Every finite probe packet has zero negative energy below the global threshold. -/
theorem confinedProbe_negativeEnergy_zero_below_threshold {R : ℝ} (hR : 0 < R)
    (hle : (R : EReal) ≤ ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A)
    {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) :
    energy 0 (confinedProbeGram R p) = 0 :=
  (confinedProbe_negativeEnergy_zero_iff hR hp).mpr
    (confinedProbeGram_index_zero_of_le_threshold hR hle hp)

/-- The critical ratio lies in the zero-energy regime for every actual probe family. -/
theorem criticalRatio_probe_negativeEnergy_zero {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) :
    energy 0 (confinedProbeGram W₀ p) = 0 :=
  confinedProbe_negativeEnergy_zero_below_threshold hW ht.ge hp

#print axioms confinedProbe_negativeEnergy_mono
#print axioms confinedProbe_negativeEnergy_zero_iff
#print axioms criticalRatio_probe_negativeEnergy_zero

end
end GaloisForLFunctions.ExclusionOfTheCriticalState
