import GaloisForLFunctions.RHTower.SoninLogClockFidelityAsymmetry

/-!
# Sonin fidelity-orientation physical-sector universality

Fidelity saturation alone sees both real rays of involutive logarithmic Fourier scattering.
The sign of the scattering overlap selects the physical positive ray and therefore the exact
kernel of the static Sonin constraint.
-/

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- **Sonin fidelity-orientation law.**  Zero homogeneous fidelity deficit together with
nonnegative scattering overlap is equivalent to the physical `+1` scattering sector. -/
theorem soninLogFourierScattering_physicalState_iff_fidelitySaturated_nonnegative :
    ∀ ψ : SoninL2,
      GaloisForLFunctions.PhysicalState
          (soninLogFourierScattering - 1).toLinearMap ψ ↔
        ‖ψ‖ ^ (4 : ℕ) - ‖inner ℂ ψ (soninLogFourierScattering ψ)‖ ^ (2 : ℕ) = 0 ∧
          0 ≤ (inner ℂ ψ (soninLogFourierScattering ψ)).re := by
  intro ψ
  constructor
  · intro hphysical
    have hfixed :=
      (physicalState_soninLogFourierScattering_iff_invariantAverage_fixed ψ).1
        hphysical
    have hcomplement :
        (1 - soninLogFourierInvariantAverage) ψ = 0 := by
      simpa only [_root_.sub_apply, one_apply_eq_self,
        sub_eq_zero] using hfixed.symm
    constructor
    · rw [soninLogFourierScattering_homogeneousFidelityDeficit_eq_four_mul_sectorWeights,
        hcomplement, norm_zero]
      ring
    · have hoverlap :=
        congrArg Complex.re (inner_soninLogFourierScattering_eq_sectorNormSq_sub ψ)
      rw [hfixed, hcomplement, norm_zero] at hoverlap
      rw [hoverlap]
      norm_num
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
      exact sq_nonneg ‖ψ‖
  · rintro ⟨hdeficit, hoverlapNonneg⟩
    have hsectorProduct :
        ‖soninLogFourierInvariantAverage ψ‖ ^ (2 : ℕ) *
            ‖(1 - soninLogFourierInvariantAverage) ψ‖ ^ (2 : ℕ) = 0 := by
      rw [soninLogFourierScattering_homogeneousFidelityDeficit_eq_four_mul_sectorWeights]
        at hdeficit
      nlinarith
    have hoverlap :
        (inner ℂ ψ (soninLogFourierScattering ψ)).re =
          ‖soninLogFourierInvariantAverage ψ‖ ^ (2 : ℕ) -
            ‖(1 - soninLogFourierInvariantAverage) ψ‖ ^ (2 : ℕ) := by
      exact congrArg Complex.re
        (inner_soninLogFourierScattering_eq_sectorNormSq_sub ψ)
    have hcomplementSq :
        ‖(1 - soninLogFourierInvariantAverage) ψ‖ ^ (2 : ℕ) = 0 := by
      rcases mul_eq_zero.mp hsectorProduct with hinvariant | hcomplement
      · rw [hinvariant] at hoverlap
        nlinarith [sq_nonneg ‖(1 - soninLogFourierInvariantAverage) ψ‖]
      · exact hcomplement
    have hcomplementNorm :
        ‖(1 - soninLogFourierInvariantAverage) ψ‖ = 0 := by
      nlinarith [norm_nonneg ((1 - soninLogFourierInvariantAverage) ψ)]
    have hcomplement :
        (1 - soninLogFourierInvariantAverage) ψ = 0 :=
      norm_eq_zero.mp hcomplementNorm
    apply
      (physicalState_soninLogFourierScattering_iff_invariantAverage_fixed ψ).2
    have hsub :
        ψ - soninLogFourierInvariantAverage ψ = 0 := by
      simpa only [_root_.sub_apply,
        one_apply_eq_self] using hcomplement
    exact (sub_eq_zero.mp hsub).symm

end

end RHTower
