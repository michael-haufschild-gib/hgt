import GaloisForLFunctions.HTGeometry.RabiHatanoNelsonAlgebra
import GaloisForLFunctions.RHTower.EulerSquarefreeWickNonreciprocalWilsonOrientation
import GaloisForLFunctions.RHTower.SuzukiHatanoNelsonEllipse
import GaloisForLFunctions.RHTower.SuzukiLatticeLimitSymbol

/-!
# Rabi--Hatano--Nelson applications in the arithmetic corpus

The directional hopping symbol from Huang--Yang is identified with every rank-one summand of the
Suzuki Hatano--Nelson lattice limit.  Its imaginary gauge gives exact open-boundary sine modes.
The same forward/backward hopping defect also feeds the completed Euler--Wick directional Wilson
orientation channel.
-/

open scoped BigOperators Matrix

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry.RabiHatanoNelson

/-- Suzuki's Hatano--Nelson ellipse is exactly the paper's directional hopping symbol under
`J = cosh κ` and directional strength `sinh κ`. -/
theorem hatanoNelsonSymbol_eq_directionalHoppingSymbol (κ θ : ℝ) :
    hatanoNelsonSymbol κ θ =
      directionalHoppingSymbol (Real.cosh κ) (Real.sinh κ) θ := by
  apply Complex.ext
  · rw [hatanoNelsonSymbol_re, directionalHoppingSymbol_re]
  · rw [hatanoNelsonSymbol_im, directionalHoppingSymbol_im]

theorem hatanoNelsonSymbol_quarter_eq (κ : ℝ) :
    hatanoNelsonSymbol κ (Real.pi / 2) =
      2 * Real.sinh κ * Complex.I := by
  rw [hatanoNelsonSymbol_eq_directionalHoppingSymbol,
    directionalHoppingSymbol_quarter]

/-- Every finite-rank Suzuki limit symbol is a sum of Huang--Yang directional hopping symbols. -/
theorem latticeLimitSymbol_eq_directionalHoppingSum {d : ℕ}
    (c₀ : ℝ) (Q : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ)
    (κ : ℝ) (θ : Fin d → ℝ) :
    latticeLimitSymbol c₀ Q c κ θ = (c₀ : ℂ) +
      ∑ q ∈ Q, (c q : ℂ) *
        directionalHoppingSymbol
          (Real.cosh (κ * (orbitLength q : ℝ)))
          (Real.sinh (κ * (orbitLength q : ℝ)))
          (∑ i, ((q i : ℤ) : ℝ) * θ i) := by
  rw [latticeLimitSymbol]
  apply congrArg ((c₀ : ℂ) + ·)
  apply Finset.sum_congr rfl
  intro q _
  rw [hatanoNelsonSymbol_eq_directionalHoppingSymbol]

/-- Every finite prime-step adjacency symbol is likewise a sum of the paper's directional hopping
symbols. -/
theorem primeStepSymbol_eq_directionalHoppingSum {ι : Type*} [Fintype ι]
    (c₀ : ℝ) (Q : Finset (ι → ℤ)) (c : (ι → ℤ) → ℝ)
    (κ : ℝ) (θ : ι → ℝ) :
    primeStepSymbol c₀ Q c κ θ = (c₀ : ℂ) +
      ∑ q ∈ Q, (c q : ℂ) *
        directionalHoppingSymbol
          (Real.cosh (κ * (latticeL1 q : ℝ)))
          (Real.sinh (κ * (latticeL1 q : ℝ)))
          (∑ i, (q i : ℝ) * θ i) := by
  rw [primeStepSymbol]
  apply congrArg ((c₀ : ℂ) + ·)
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  rw [directionalHoppingSymbol_eq]
  rw [← hatanoNelsonSymbol_eq]
  rfl

/-- Raw imaginary-gauge recurrence for exponential Suzuki weights. -/
theorem exponentialSkinMode_recurrence (κ k : ℝ) (n : ℕ) :
    (Real.exp (-κ) * Real.exp κ ^ 2) *
          skinSineMode (Real.exp κ) k n +
        Real.exp (-κ) * skinSineMode (Real.exp κ) k (n + 2) =
      (2 * Real.exp (-κ) * Real.exp κ * Real.cos k) *
        skinSineMode (Real.exp κ) k (n + 1) :=
  skinSineMode_recurrence (Real.exp (-κ)) (Real.exp κ) k n

/-- Normalized Hatano--Nelson recurrence: the exponential gauge makes asymmetric hoppings
`e^κ,e^-κ` act with reciprocal eigenvalue `2 cos k`. -/
theorem exponentialSkinMode_recurrence_normalized (κ k : ℝ) (n : ℕ) :
    Real.exp κ * skinSineMode (Real.exp κ) k n +
        Real.exp (-κ) * skinSineMode (Real.exp κ) k (n + 2) =
      2 * Real.cos k * skinSineMode (Real.exp κ) k (n + 1) := by
  have h := exponentialSkinMode_recurrence κ k n
  rw [Real.exp_neg] at h ⊢
  have hexp : Real.exp κ ≠ 0 := ne_of_gt (Real.exp_pos κ)
  field_simp [hexp] at h ⊢
  linear_combination h

end

end RHTower

namespace GaloisForLFunctions.RHTower

noncomputable section

open HTGeometry.RabiHatanoNelson

/-- The paper's forward/backward hopping defect becomes a literal Euler--Wick Wilson orientation
source.  Dependence on the reciprocal hopping `J` cancels. -/
theorem ewqDirectionalWilsonContrast_of_directionalHopping (J κ : ℝ) :
    ewqDirectionalWilsonSignedContrast ((J + κ) - (J - κ)) = 8 * κ := by
  rw [directionalHopping_forward_sub_backward,
    ewqDirectionalWilsonSignedContrast_eq]
  ring

end

end GaloisForLFunctions.RHTower
