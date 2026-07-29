import GaloisForLFunctions.RHTower.SoninLogClockFidelityAsymmetry

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-!
# Sonin logarithmic-clock exact ray distance

Logarithmic Sonin scattering has only two real phase chambers.  One of the signs `±1` attains
the exact projective ray distance, determined by the smaller invariant/anti-invariant sector.
On arbitrary states, the projective asymmetry is an exact homogeneous quadratic function of this
distance and total mass.  The normalized law is a corollary.
-/

/-- Exact squared distance from a Sonin state to the closer of its two scattering rays. -/
def soninLogFourierScatteringRayDistanceSq (ψ : SoninL2) : ℝ :=
  4 * min (‖soninLogFourierInvariantAverage ψ‖ ^ 2)
    (‖(1 - soninLogFourierInvariantAverage) ψ‖ ^ 2)

/-- **Exact Sonin ray-selection law.**  One of the two real phases realizes the exact projective
ray distance to logarithmic Sonin scattering. -/
theorem exists_sign_soninLogFourierScatteringRayDistanceSq
    (ψ : SoninL2) :
    ∃ c : ℂ, (c = 1 ∨ c = -1) ∧ ‖c‖ = 1 ∧
      ‖soninLogFourierScattering ψ - c • ψ‖ ^ 2 =
        soninLogFourierScatteringRayDistanceSq ψ := by
  let P : SoninL2 →L[ℂ] SoninL2 := soninLogFourierInvariantAverage
  let a : SoninL2 := P ψ
  let b : SoninL2 := (1 - P) ψ
  have hψ : ψ = a + b := by
    simp only [a, b, P, _root_.sub_apply,
      one_apply_eq_self]
    module
  have hSψ : soninLogFourierScattering ψ = a - b := by
    have hPapply := HTGeometry.finiteInvolutiveGaugeAverage_apply
      soninLogFourierScattering ψ
    change P ψ = ((2 : ℂ)⁻¹) • (ψ + soninLogFourierScattering ψ) at hPapply
    change soninLogFourierScattering ψ = P ψ - (ψ - P ψ)
    rw [hPapply]
    norm_num
    module
  by_cases hab : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2
  · refine ⟨-1, Or.inr rfl, by norm_num, ?_⟩
    have hdist : soninLogFourierScattering ψ - (-1 : ℂ) • ψ =
        (2 : ℂ) • a := by
      rw [hSψ, hψ]
      module
    rw [hdist, norm_smul]
    change (‖(2 : ℂ)‖ * ‖a‖) ^ 2 = 4 * min (‖a‖ ^ 2) (‖b‖ ^ 2)
    rw [min_eq_left hab]
    norm_num
    ring
  · have hba : ‖b‖ ^ 2 ≤ ‖a‖ ^ 2 := le_of_not_ge hab
    refine ⟨1, Or.inl rfl, norm_one, ?_⟩
    have hdist : soninLogFourierScattering ψ - (1 : ℂ) • ψ =
        (-2 : ℂ) • b := by
      rw [hSψ, hψ]
      module
    rw [hdist, norm_smul]
    change (‖(-2 : ℂ)‖ * ‖b‖) ^ 2 = 4 * min (‖a‖ ^ 2) (‖b‖ ^ 2)
    rw [min_eq_right hba]
    norm_num
    ring

/-- **Homogeneous Sonin ray/asymmetry law.**  For every state, projective asymmetry is the exact
product of squared signed-ray distance and its complement inside the total squared mass. -/
theorem soninLogFourierScattering_projectiveAsymmetry_eq_rayDistanceSq_mul_massComplement
    (ψ : SoninL2) :
    HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) ψ
        (soninLogFourierScattering ψ) =
      soninLogFourierScatteringRayDistanceSq ψ *
        (‖ψ‖ ^ 2 - soninLogFourierScatteringRayDistanceSq ψ / 4) := by
  have hsum := norm_soninLogFourierInvariantAverage_sq_add_complement_sq ψ
  rw [soninLogFourierScattering_projectiveAsymmetry_eq_four_mul_sectorWeights
    ψ]
  unfold soninLogFourierScatteringRayDistanceSq
  by_cases hab : ‖soninLogFourierInvariantAverage ψ‖ ^ 2 ≤
      ‖(1 - soninLogFourierInvariantAverage) ψ‖ ^ 2
  · rw [min_eq_left hab]
    nlinarith
  · rw [min_eq_right (le_of_not_ge hab)]
    nlinarith

/-- **Normalized Sonin ray/asymmetry conversion law.**  On unit states, the homogeneous mass
complement specializes to the familiar unit complement. -/
theorem soninLogFourierScattering_projectiveAsymmetry_eq_rayDistanceSq_mul_complement
    {ψ : SoninL2} (hψnorm : ‖ψ‖ = 1) :
    HTGeometry.projectiveGramTangentEnergy (𝕜 := ℂ) ψ
        (soninLogFourierScattering ψ) =
      soninLogFourierScatteringRayDistanceSq ψ *
        (1 - soninLogFourierScatteringRayDistanceSq ψ / 4) := by
  rw [soninLogFourierScattering_projectiveAsymmetry_eq_rayDistanceSq_mul_massComplement,
    hψnorm]
  norm_num

end

end RHTower
