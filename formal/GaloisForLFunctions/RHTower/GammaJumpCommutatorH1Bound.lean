import GaloisForLFunctions.RHTower.GammaJumpCommutatorFourierKernel
import GaloisForLFunctions.RHTower.GammaJumpNearDiagonalLipschitz
import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

/-!
# The Gamma jump commutator gains one physical derivative

The kernel identity `(33)` puts the commutator's frequency density in the form

`∫ ψ(ξ−η)[r(ξ) − r(η)]Φ(η) dη`,

and the global symbol-difference bound

`(1+|ξ|)|r(ξ) − r(η)| ≤ C(|ξ−η| + |ξ−η|²)`

turns the weight `1+|ξ|` demanded by an `H¹` estimate into a *convolution* kernel in `ξ−η` alone —
with no region hypothesis, so the card's near/far split is not needed.  Young's inequality
`L¹ ⋆ L² → L²` then gives the bound, the `L¹` norm of the kernel being the cutoff transform's first
and second moments.

The logarithmic growth of `r` never enters: in the far region the separation already controls both
frequencies, so the affine bound suffices there and the mean value theorem suffices near the
diagonal.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- **`(32)`: the Gamma jump commutator gains one physical derivative.** -/
theorem exists_bound_lintegral_sq_gammaJumpCommutatorDensity :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : ℝ → ℂ) (Φ : ℝ → X),
      Measurable (fun t : ℝ => ‖ψ t‖) → Measurable (fun η : ℝ => ‖Φ η‖ₑ) →
      (∫⁻ ξ : ℝ, ‖(1 + |ξ|) • gammaJumpCommutatorDensity ψ Φ ξ‖ₑ ^ 2)
        ≤ (∫⁻ t : ℝ, ENNReal.ofReal (C * (‖ψ t‖ * (|t| + t ^ 2)))) ^ 2
          * ∫⁻ η : ℝ, ‖Φ η‖ₑ ^ 2 := by
  obtain ⟨C, hC, hglob⟩ := exists_bound_gammaJump_global
  refine ⟨C, hC, fun ψ Φ hψ hΦ => ?_⟩
  set K : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (C * (‖ψ t‖ * (|t| + t ^ 2))) with hKdef
  set F : ℝ → ℝ≥0∞ := fun η => ‖Φ η‖ₑ with hFdef
  have hKmeas : Measurable K := by
    rw [hKdef]
    exact (ENNReal.measurable_ofReal.comp (((hψ.mul (((measurable_id.abs).add
      (measurable_id.pow_const 2))))).const_mul C))
  have hpt : ∀ ξ : ℝ, ‖(1 + |ξ|) • gammaJumpCommutatorDensity ψ Φ ξ‖ₑ
      ≤ ∫⁻ y : ℝ, K y * F (ξ - y) := by
    intro ξ
    have h1 : ‖(1 + |ξ|) • gammaJumpCommutatorDensity ψ Φ ξ‖ₑ
        = ENNReal.ofReal (1 + |ξ|) * ‖gammaJumpCommutatorDensity ψ Φ ξ‖ₑ := by
      rw [enorm_smul, ← ofReal_norm, Real.norm_of_nonneg (by positivity)]
    have h2 : ‖gammaJumpCommutatorDensity ψ Φ ξ‖ₑ
        ≤ ∫⁻ η : ℝ, ‖ψ (ξ - η) • ((gammaJumpMultiplier ξ - gammaJumpMultiplier η) • Φ η)‖ₑ := by
      rw [gammaJumpCommutatorDensity]
      exact enorm_integral_le_lintegral_enorm _
    have h3 : ENNReal.ofReal (1 + |ξ|)
          * ∫⁻ η : ℝ, ‖ψ (ξ - η) • ((gammaJumpMultiplier ξ - gammaJumpMultiplier η) • Φ η)‖ₑ
        = ∫⁻ η : ℝ, ENNReal.ofReal (1 + |ξ|)
            * ‖ψ (ξ - η) • ((gammaJumpMultiplier ξ - gammaJumpMultiplier η) • Φ η)‖ₑ :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    have h4 : ∀ η : ℝ, ENNReal.ofReal (1 + |ξ|)
          * ‖ψ (ξ - η) • ((gammaJumpMultiplier ξ - gammaJumpMultiplier η) • Φ η)‖ₑ
        ≤ K (ξ - η) * F η := by
      intro η
      have he : ‖ψ (ξ - η) • ((gammaJumpMultiplier ξ - gammaJumpMultiplier η) • Φ η)‖ₑ
          = ENNReal.ofReal (‖ψ (ξ - η)‖
              * |gammaJumpMultiplier ξ - gammaJumpMultiplier η|) * ‖Φ η‖ₑ := by
        rw [enorm_smul, enorm_smul, ← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs,
          ← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg _)]
      rw [he, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have hg := hglob ξ η
      have hnn : (0 : ℝ) ≤ ‖ψ (ξ - η)‖ := norm_nonneg _
      calc (1 + |ξ|) * (‖ψ (ξ - η)‖ * |gammaJumpMultiplier ξ - gammaJumpMultiplier η|)
          = ‖ψ (ξ - η)‖ * ((1 + |ξ|) * |gammaJumpMultiplier ξ - gammaJumpMultiplier η|) := by
            ring
        _ ≤ ‖ψ (ξ - η)‖ * (C * (|ξ - η| + |ξ - η| ^ 2)) :=
            mul_le_mul_of_nonneg_left hg hnn
        _ = C * (‖ψ (ξ - η)‖ * (|ξ - η| + (ξ - η) ^ 2)) := by rw [sq_abs]; ring
    have hcv : (∫⁻ η : ℝ, K (ξ - η) * F η) = ∫⁻ y : ℝ, K y * F (ξ - y) := by
      have hself := lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
        (fun y : ℝ => K y * F (ξ - y)) ξ
      rw [← hself]
      refine lintegral_congr fun η => ?_
      rw [sub_sub_cancel]
    calc ‖(1 + |ξ|) • gammaJumpCommutatorDensity ψ Φ ξ‖ₑ
        = ENNReal.ofReal (1 + |ξ|) * ‖gammaJumpCommutatorDensity ψ Φ ξ‖ₑ := h1
      _ ≤ ENNReal.ofReal (1 + |ξ|)
            * ∫⁻ η : ℝ, ‖ψ (ξ - η) • ((gammaJumpMultiplier ξ - gammaJumpMultiplier η) • Φ η)‖ₑ :=
          mul_le_mul' le_rfl h2
      _ = ∫⁻ η : ℝ, ENNReal.ofReal (1 + |ξ|)
            * ‖ψ (ξ - η) • ((gammaJumpMultiplier ξ - gammaJumpMultiplier η) • Φ η)‖ₑ := h3
      _ ≤ ∫⁻ η : ℝ, K (ξ - η) * F η := lintegral_mono h4
      _ = ∫⁻ y : ℝ, K y * F (ξ - y) := hcv
  exact GaloisForLFunctions.HTGeometry.lintegral_enorm_sq_le_of_convolution_bound hKmeas hΦ hpt

end GaloisForLFunctions.RHTower
