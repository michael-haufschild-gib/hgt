import GaloisForLFunctions.RHTower.ShiftedSymbolWeightedDifference
import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

/-!
# `(35a)`: the shifted Gamma jump commutator gains one physical derivative

Conjugating by `e^{σL}` turns the jump operator's multiplier `r(ξ)` into `r(ξ+iσ) = wallSymbol σ ξ`,
so the commutator's frequency density on the shifted line is the same convolution against the symbol
*difference*.  With the global weighted-difference bound of the shifted symbol in hand, Young's
inequality gives the same order-minus-one estimate, now with a `σ`-dependent constant — which is
`(35a)`, the statement that `[R,χ]` maps `e^{-σL}L²` to `e^{-σL}H¹` for every `0 < σ < 1`.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

/-- The commutator's frequency density on the shifted line. -/
def shiftedJumpCommutatorDensity (σ : ℝ) (ψ : ℝ → ℂ) (Φ : ℝ → X) (ξ : ℝ) : X :=
  ∫ η : ℝ, ψ (ξ - η) • ((wallSymbol σ ξ - wallSymbol σ η) • Φ η)

omit [CompleteSpace X] in
/-- **`(35a)`: the shifted Gamma jump commutator gains one physical derivative.** -/
theorem exists_bound_lintegral_sq_shiftedJumpCommutatorDensity {σ : ℝ}
    (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : ℝ → ℂ) (Φ : ℝ → X),
      Measurable (fun t : ℝ => ‖ψ t‖) → Measurable (fun η : ℝ => ‖Φ η‖ₑ) →
      (∫⁻ ξ : ℝ, ‖(1 + |ξ|) • shiftedJumpCommutatorDensity σ ψ Φ ξ‖ₑ ^ 2)
        ≤ (∫⁻ t : ℝ, ENNReal.ofReal (C * (‖ψ t‖ * (|t| + t ^ 2)))) ^ 2
          * ∫⁻ η : ℝ, ‖Φ η‖ₑ ^ 2 := by
  obtain ⟨C, hC, hglob⟩ := exists_bound_wallSymbol_global hσ0 hσ1
  refine ⟨C, hC, fun ψ Φ hψ hΦ => ?_⟩
  set K : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (C * (‖ψ t‖ * (|t| + t ^ 2))) with hKdef
  set F : ℝ → ℝ≥0∞ := fun η => ‖Φ η‖ₑ with hFdef
  have hKmeas : Measurable K := by
    rw [hKdef]
    exact (ENNReal.measurable_ofReal.comp (((hψ.mul (((measurable_id.abs).add
      (measurable_id.pow_const 2))))).const_mul C))
  have hpt : ∀ ξ : ℝ, ‖(1 + |ξ|) • shiftedJumpCommutatorDensity σ ψ Φ ξ‖ₑ
      ≤ ∫⁻ y : ℝ, K y * F (ξ - y) := by
    intro ξ
    have h1 : ‖(1 + |ξ|) • shiftedJumpCommutatorDensity σ ψ Φ ξ‖ₑ
        = ENNReal.ofReal (1 + |ξ|) * ‖shiftedJumpCommutatorDensity σ ψ Φ ξ‖ₑ := by
      rw [enorm_smul, ← ofReal_norm, Real.norm_of_nonneg (by positivity)]
    have h2 : ‖shiftedJumpCommutatorDensity σ ψ Φ ξ‖ₑ
        ≤ ∫⁻ η : ℝ, ‖ψ (ξ - η) • ((wallSymbol σ ξ - wallSymbol σ η) • Φ η)‖ₑ := by
      rw [shiftedJumpCommutatorDensity]
      exact enorm_integral_le_lintegral_enorm _
    have h3 : ENNReal.ofReal (1 + |ξ|)
          * ∫⁻ η : ℝ, ‖ψ (ξ - η) • ((wallSymbol σ ξ - wallSymbol σ η) • Φ η)‖ₑ
        = ∫⁻ η : ℝ, ENNReal.ofReal (1 + |ξ|)
            * ‖ψ (ξ - η) • ((wallSymbol σ ξ - wallSymbol σ η) • Φ η)‖ₑ :=
      (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    have h4 : ∀ η : ℝ, ENNReal.ofReal (1 + |ξ|)
          * ‖ψ (ξ - η) • ((wallSymbol σ ξ - wallSymbol σ η) • Φ η)‖ₑ
        ≤ K (ξ - η) * F η := by
      intro η
      have he : ‖ψ (ξ - η) • ((wallSymbol σ ξ - wallSymbol σ η) • Φ η)‖ₑ
          = ENNReal.ofReal (‖ψ (ξ - η)‖ * ‖wallSymbol σ ξ - wallSymbol σ η‖) * ‖Φ η‖ₑ := by
        rw [enorm_smul, enorm_smul, ← ofReal_norm, ← ofReal_norm, ← mul_assoc,
          ← ENNReal.ofReal_mul (norm_nonneg _)]
      rw [he, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have hg := hglob ξ η
      have hnn : (0 : ℝ) ≤ ‖ψ (ξ - η)‖ := norm_nonneg _
      calc (1 + |ξ|) * (‖ψ (ξ - η)‖ * ‖wallSymbol σ ξ - wallSymbol σ η‖)
          = ‖ψ (ξ - η)‖ * ((1 + |ξ|) * ‖wallSymbol σ ξ - wallSymbol σ η‖) := by ring
        _ ≤ ‖ψ (ξ - η)‖ * (C * (|ξ - η| + |ξ - η| ^ 2)) := mul_le_mul_of_nonneg_left hg hnn
        _ = C * (‖ψ (ξ - η)‖ * (|ξ - η| + (ξ - η) ^ 2)) := by rw [sq_abs]; ring
    have hcv : (∫⁻ η : ℝ, K (ξ - η) * F η) = ∫⁻ y : ℝ, K y * F (ξ - y) := by
      have hself := lintegral_sub_left_eq_self (μ := (volume : Measure ℝ))
        (fun y : ℝ => K y * F (ξ - y)) ξ
      rw [← hself]
      refine lintegral_congr fun η => ?_
      rw [sub_sub_cancel]
    calc ‖(1 + |ξ|) • shiftedJumpCommutatorDensity σ ψ Φ ξ‖ₑ
        = ENNReal.ofReal (1 + |ξ|) * ‖shiftedJumpCommutatorDensity σ ψ Φ ξ‖ₑ := h1
      _ ≤ ENNReal.ofReal (1 + |ξ|)
            * ∫⁻ η : ℝ, ‖ψ (ξ - η) • ((wallSymbol σ ξ - wallSymbol σ η) • Φ η)‖ₑ :=
          mul_le_mul' le_rfl h2
      _ = ∫⁻ η : ℝ, ENNReal.ofReal (1 + |ξ|)
            * ‖ψ (ξ - η) • ((wallSymbol σ ξ - wallSymbol σ η) • Φ η)‖ₑ := h3
      _ ≤ ∫⁻ η : ℝ, K (ξ - η) * F η := lintegral_mono h4
      _ = ∫⁻ y : ℝ, K y * F (ξ - y) := hcv
  exact GaloisForLFunctions.HTGeometry.lintegral_enorm_sq_le_of_convolution_bound hKmeas hΦ hpt

end GaloisForLFunctions.RHTower
