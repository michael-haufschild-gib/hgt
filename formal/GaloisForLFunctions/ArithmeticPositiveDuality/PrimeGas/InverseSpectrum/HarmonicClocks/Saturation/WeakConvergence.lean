import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.Harmonics
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Saturation.CyclicPhase
import GaloisForLFunctions.HTGeometry.BernsteinSzegoProbabilityApproximation

/-! # Weak convergence of the entire composition phase law -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

private theorem conjugate_moment (ρ : ProbabilityMeasure Circle) (k : ℕ) :
    circleMeasureMomentZ (ρ : Measure Circle) (k:ℤ) = conj (∫ z : Circle, (z:ℂ)^k ∂(ρ : Measure Circle)) := by
  have he (z : Circle) : ((z:ℂ)^k)⁻¹ = conj ((z:ℂ)^k) :=
    Complex.inv_eq_conj (by rw [norm_pow,Circle.norm_coe,one_pow])
  simp only [circleMeasureMomentZ,zpow_neg,zpow_natCast,he,integral_conj]

private theorem positive_moment (ρ : ProbabilityMeasure Circle) (k : ℕ) :
    circleMeasureMomentZ (ρ : Measure Circle) (Int.negSucc k) =
      ∫ z : Circle, (z:ℂ)^(k+1) ∂(ρ : Measure Circle) := by
  change (∫ z : Circle, (z:ℂ)^((k+1:ℕ):ℤ) ∂(ρ : Measure Circle)) = _
  simp only [zpow_natCast]

/-- Every saturated preparation has the same weak phase law, including for drifting tolerances. -/
theorem saturated_phase_law {r : ℕ+} {t d : ℕ → ℝ} {δ : ℝ} (h₀ : 0 ≤ δ) (h₁ : δ ≤ 1)
    {v : ℕ → MissingWave} {m : ℕ+ → ℝ}
    (ht : Tendsto t atTop (𝓝 0)) (hd : Tendsto d atTop (𝓝 δ))
    (hc : ∀ j, harmonicTest r (d j) (v j) (t j))
    (hm : ∀ n, Tendsto (fun j => occupationProbability (v j) n) atTop (𝓝 (m n)))
    (hs : HasSum m (retentionCeiling r δ)) :
    Tendsto (fun j => occupationPhaseLaw (v j) (t j)) atTop (𝓝 (cyclicPhaseLaw r δ h₀ h₁)) := by
  have h (k : ℕ) : Tendsto (fun j => ∫ z : Circle, (z:ℂ)^k ∂(occupationPhaseLaw (v j) (t j) : Measure Circle))
      atTop (𝓝 (∫ z : Circle, (z:ℂ)^k ∂(cyclicPhaseLaw r δ h₀ h₁ : Measure Circle))) := by
    simpa only [occupationPhaseLaw_moment,cyclicPhaseLaw_moment] using saturated_harmonic_limit ht hd hc hm hs k
  rw [isClosedEmbedding_completeCircleMomentSequence.isEmbedding.tendsto_nhds_iff,tendsto_pi_nhds]
  intro k
  cases k with
  | ofNat l =>
    simpa only [Function.comp_def,completeCircleMomentSequence,Int.ofNat_eq_natCast,conjugate_moment] using
      Complex.continuous_conj.continuousAt.tendsto.comp (h l)
  | negSucc l =>
    simpa only [Function.comp_def,completeCircleMomentSequence,positive_moment] using h (l+1)

#print axioms saturated_phase_law

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
