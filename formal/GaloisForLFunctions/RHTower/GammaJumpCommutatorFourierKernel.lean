import GaloisForLFunctions.RHTower.GammaJumpMultiplierAction
import GaloisForLFunctions.RHTower.VectorFourierPlancherelIntegral

/-!
# The Fourier kernel of the Gamma jump commutator

Writing both factors as superpositions of characters — the cutoff over `t`, the profile over `η` —
the jump operator inserts its multiplier under each integral sign, and the two insertions differ
only in *which* frequency the multiplier is evaluated at: `r(ξ)` for the product, `r(η)` for the
factor.  Subtracting leaves the symbol *difference*,

`𝓕([R,χ]F)(ξ) = ∫ χ̂(ξ−η)[r(ξ) − r(η)]F̂(η) dη`,

which is `(33)`.  Nothing about the cutoff's exterior constants is needed: a constant multiplication
operator commutes with every multiplier, so only the transform of the cutoff enters, and the
convolution structure comes from the transform of a product.
-/

open Complex MeasureTheory Set Convolution
open scoped FourierTransform

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- The superposition is the angular transform at the reflected frequency. -/
theorem freqSuperposition_eq_vectorAngularTransform (Φ : ℝ → X) (L : ℝ) :
    freqSuperposition Φ L = vectorAngularTransform Φ (-L) := by
  rw [freqSuperposition, vectorAngularTransform]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  unfold freqChar
  push_cast
  ring_nf

omit [CompleteSpace X] in
/-- The superposition is a Fourier integral. -/
theorem freqSuperposition_eq_fourier (Φ : ℝ → X) (L : ℝ) :
    freqSuperposition Φ L = 𝓕 Φ ((-L) / (2 * Real.pi)) := by
  rw [freqSuperposition_eq_vectorAngularTransform, vectorAngularTransform_eq_fourier]

/-- **The product of two superpositions is the superposition of the convolution.** -/
theorem freqSuperposition_smul_freqSuperposition {ψ : ℝ → ℂ} {Φ : ℝ → X}
    (hψ : Integrable ψ) (hΦ : Integrable Φ) (L : ℝ) :
    freqSuperposition ψ L • freqSuperposition Φ L
      = freqSuperposition (fun ξ : ℝ => ∫ η : ℝ, ψ (ξ - η) • Φ η) L := by
  have hconv : (fun ξ : ℝ => ∫ η : ℝ, ψ (ξ - η) • Φ η)
      = ψ ⋆[ContinuousLinearMap.lsmul ℂ ℂ] Φ := by
    funext ξ
    rw [convolution_eq_swap]
    rfl
  rw [freqSuperposition_eq_fourier, freqSuperposition_eq_fourier, freqSuperposition_eq_fourier,
    hconv, Real.fourier_smul_convolution_eq hψ hΦ]

/-- The frequency kernel of the Gamma jump commutator. -/
def gammaJumpCommutatorDensity (ψ : ℝ → ℂ) (Φ : ℝ → X) (ξ : ℝ) : X :=
  ∫ η : ℝ, ψ (ξ - η) • ((gammaJumpMultiplier ξ - gammaJumpMultiplier η) • Φ η)

omit [CompleteSpace X] in
/-- The convolution of two integrable densities is integrable. -/
theorem integrable_convolution_freq {ψ : ℝ → ℂ} {Φ : ℝ → X}
    (hψ : Integrable ψ) (hΦ : Integrable Φ) :
    Integrable fun ξ : ℝ => ∫ η : ℝ, ψ (ξ - η) • Φ η := by
  have hconv : (fun ξ : ℝ => ∫ η : ℝ, ψ (ξ - η) • Φ η)
      = ψ ⋆[ContinuousLinearMap.lsmul ℂ ℂ] Φ := by
    funext ξ
    rw [convolution_eq_swap]
    rfl
  rw [hconv]
  exact Integrable.integrable_convolution (ContinuousLinearMap.lsmul ℂ ℂ) hψ hΦ

/-- **`(33)`: the Fourier kernel of the Gamma jump commutator.**  The commutator of the jump
operator with a multiplication operator is, in frequency variables, the double integral of the
cutoff transform against the *difference* of the symbol at the two frequencies. -/
theorem gammaJump_commutator_kernel {ψ : ℝ → ℂ} {Φ : ℝ → X}
    (hψ : Integrable ψ) (hΦ : Integrable Φ)
    (hrΦ : Integrable fun η : ℝ => gammaJumpMultiplier η • Φ η)
    (hconv : ∀ ξ : ℝ, Integrable fun η : ℝ => ψ (ξ - η) • Φ η)
    (hconvr : ∀ ξ : ℝ, Integrable fun η : ℝ => ψ (ξ - η) • (gammaJumpMultiplier η • Φ η))
    (hrC : Integrable fun ξ : ℝ => gammaJumpMultiplier ξ • ∫ η : ℝ, ψ (ξ - η) • Φ η)
    (L : ℝ) :
    gammaJumpOperator (fun M : ℝ => freqSuperposition ψ M • freqSuperposition Φ M) L
        - freqSuperposition ψ L • gammaJumpOperator (freqSuperposition Φ) L
      = freqSuperposition (gammaJumpCommutatorDensity ψ Φ) L := by
  have hCint : Integrable (fun ξ : ℝ => ∫ η : ℝ, ψ (ξ - η) • Φ η) :=
    integrable_convolution_freq hψ hΦ
  have hDint : Integrable
      (fun ξ : ℝ => ∫ η : ℝ, ψ (ξ - η) • (gammaJumpMultiplier η • Φ η)) :=
    integrable_convolution_freq hψ hrΦ
  have hA : (fun M : ℝ => freqSuperposition ψ M • freqSuperposition Φ M)
      = freqSuperposition (fun ξ : ℝ => ∫ η : ℝ, ψ (ξ - η) • Φ η) := by
    funext M
    exact freqSuperposition_smul_freqSuperposition hψ hΦ M
  have hB : gammaJumpOperator
      (freqSuperposition (fun ξ : ℝ => ∫ η : ℝ, ψ (ξ - η) • Φ η)) L
      = ∫ ξ : ℝ, gammaJumpMultiplier ξ • (freqChar ξ L • ∫ η : ℝ, ψ (ξ - η) • Φ η) :=
    gammaJumpOperator_freqSuperposition hCint hrC L
  have hC1 : gammaJumpOperator (freqSuperposition Φ) L
      = ∫ η : ℝ, gammaJumpMultiplier η • (freqChar η L • Φ η) :=
    gammaJumpOperator_freqSuperposition hΦ hrΦ L
  have hC2 : (∫ η : ℝ, gammaJumpMultiplier η • (freqChar η L • Φ η))
      = freqSuperposition (fun η : ℝ => gammaJumpMultiplier η • Φ η) L := by
    rw [freqSuperposition]
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    exact smul_comm _ _ _
  have hD1 : freqSuperposition ψ L
        • freqSuperposition (fun η : ℝ => gammaJumpMultiplier η • Φ η) L
      = freqSuperposition
          (fun ξ : ℝ => ∫ η : ℝ, ψ (ξ - η) • (gammaJumpMultiplier η • Φ η)) L :=
    freqSuperposition_smul_freqSuperposition hψ hrΦ L
  have hI1 : Integrable fun ξ : ℝ =>
      gammaJumpMultiplier ξ • (freqChar ξ L • ∫ η : ℝ, ψ (ξ - η) • Φ η) := by
    refine (integrable_freqChar_smul hrC L).congr (Filter.Eventually.of_forall fun ξ => ?_)
    exact smul_comm _ _ _
  have hI2 : Integrable fun ξ : ℝ =>
      freqChar ξ L • ∫ η : ℝ, ψ (ξ - η) • (gammaJumpMultiplier η • Φ η) :=
    integrable_freqChar_smul hDint L
  rw [hA, hB, hC1, hC2, hD1, freqSuperposition, freqSuperposition, ← integral_sub hI1 hI2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
  show gammaJumpMultiplier ξ • (freqChar ξ L • ∫ η : ℝ, ψ (ξ - η) • Φ η)
      - freqChar ξ L • ∫ η : ℝ, ψ (ξ - η) • (gammaJumpMultiplier η • Φ η)
    = freqChar ξ L • gammaJumpCommutatorDensity ψ Φ ξ
  rw [smul_comm (gammaJumpMultiplier ξ), ← smul_sub]
  congr 1
  have hJ1 : Integrable (fun η : ℝ => gammaJumpMultiplier ξ • (ψ (ξ - η) • Φ η)) volume :=
    Integrable.smul (gammaJumpMultiplier ξ) (hconv ξ)
  have hJ2 : Integrable (fun η : ℝ => ψ (ξ - η) • (gammaJumpMultiplier η • Φ η)) volume :=
    hconvr ξ
  rw [gammaJumpCommutatorDensity, ← integral_smul, ← integral_sub hJ1 hJ2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  show gammaJumpMultiplier ξ • (ψ (ξ - η) • Φ η) - ψ (ξ - η) • (gammaJumpMultiplier η • Φ η)
    = ψ (ξ - η) • ((gammaJumpMultiplier ξ - gammaJumpMultiplier η) • Φ η)
  rw [sub_smul, smul_sub, smul_comm (gammaJumpMultiplier ξ) (ψ (ξ - η))]

end GaloisForLFunctions.RHTower
