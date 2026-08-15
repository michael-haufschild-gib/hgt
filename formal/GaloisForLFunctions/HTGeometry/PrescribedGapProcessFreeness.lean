import GaloisForLFunctions.HTGeometry.MovingDivisorEvenFreeness
import GaloisForLFunctions.HTGeometry.MovingDivisorEvenProduct
import GaloisForLFunctions.HTGeometry.GeneralMovingDivisor

/-!
# A prescribed gap process inside the order-one maximally free cage

Every shift-ergodic positive gap law of mean one is realized by the positive zeros of an even real
entire function of exact order one whose symmetric carrier has, for a dense residual set of
location parameters, a differentially algebraically independent full complex translation family.

The gap law is carried by the deterministic generic sequence supplied by Birkhoff's theorem, and
the shrinking location radii are small enough against the gaps to leave every finite-block
empirical law unchanged while keeping the parameter derivative nonzero in every coordinate.
-/

open MeasureTheory Filter
open scoped Topology NNReal

namespace GaloisForLFunctions.HTGeometry

open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

/-- **Every stationary ergodic positive gap law of mean one is realized inside the order-one
maximally free cage.**  The realizing divisor is strictly increasing, positive, of unit asymptotic
density, and its gaps carry exactly the prescribed finite-block law; for a dense residual set of
location parameters the symmetric carrier has no algebraic differential relation among any finite
family of distinct complex translates. -/
theorem exists_prescribedGapProcess_maximalTranslationFreeness
    {P : Measure (ℕ → ℝ)} [IsProbabilityMeasure P]
    (hErg : Ergodic shiftSeq P) (hint : Integrable (fun ω => ω 0) P)
    (hmean : ∫ ω, ω 0 ∂P = 1) (hpos : ∀ᵐ ω ∂P, ∀ n, 0 < ω n) :
    ∃ (g : ℕ → ℝ) (hgpos : ∀ j, 0 < g j)
      (hgmean : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, g j) atTop (𝓝 1)),
      ∃ Θ : Set BoundedRealSequence,
        Dense Θ ∧ Θ ∈ residual BoundedRealSequence ∧
        ∀ θ ∈ Θ,
          StrictMono (gapLocation g (θ : ℕ → ℝ)) ∧
          (∀ j, 0 < gapLocation g (θ : ℕ → ℝ) j) ∧
          Tendsto (fun j : ℕ => gapLocation g (θ : ℕ → ℝ) j / j) atTop (𝓝 1) ∧
          (∀ (k : ℕ) (Φ : (Fin k → ℝ) → ℝ) (C : ℝ≥0), LipschitzWith C Φ →
            (∃ M : ℝ, ∀ x, |Φ x| ≤ M) →
            Tendsto
              (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N,
                Φ (fun i : Fin k => gapLocationGap g (θ : ℕ → ℝ) (j + i)))
              atTop (𝓝 (∫ ω, Φ (blockMap k ω) ∂P))) ∧
          OrderOneEnvelope ((gapMovingDivisor g hgpos hgmean).evenCanonicalProduct
            (θ : ℕ → ℝ)) ∧
          (∀ n, analyticOrderAt ((gapMovingDivisor g hgpos hgmean).evenCanonicalProduct
              (θ : ℕ → ℝ)) (gapLocation g (θ : ℕ → ℝ) n : ℂ) = 1) ∧
          (∀ n, analyticOrderAt ((gapMovingDivisor g hgpos hgmean).evenCanonicalProduct
              (θ : ℕ → ℝ)) (-(gapLocation g (θ : ℕ → ℝ) n : ℂ)) = 1) ∧
          ∀ (m : ℕ) (shift : InjectiveShiftConfiguration (Fin m)),
            ¬ FamilyDifferentiallyAlgebraicOn
              (fun i z => (gapMovingDivisor g hgpos hgmean).evenCarrierB θ (z + shift.1 i))
              (commonUpperTranslationDomain shift) := by
  classical
  obtain ⟨g, hgpos, hgmean, hgblock⟩ :=
    exists_prescribedGapProcess_locations hErg hint hmean hpos
  refine ⟨g, hgpos, hgmean, ?_⟩
  set Dv : MovingDivisor := gapMovingDivisor g hgpos hgmean with hDv
  have hfree := Dv.movingDivisor_fullTranslationFreeness_denseResidual
  obtain ⟨hdense, hres, hnoRel⟩ := hfree
  refine ⟨_, hdense, hres, fun θ hθ => ?_⟩
  obtain ⟨hmono, hposθ, hdens, hblock⟩ := hgblock (θ : ℕ → ℝ)
  refine ⟨hmono, hposθ, hdens, hblock, ?_, ?_, ?_, hnoRel θ hθ⟩
  · exact Dv.evenCanonicalProduct_orderOneEnvelope (θ : ℕ → ℝ)
  · intro n
    exact Dv.evenCanonicalProduct_pos_zero_analyticOrderAt (θ : ℕ → ℝ) n
  · intro n
    exact Dv.evenCanonicalProduct_neg_zero_analyticOrderAt (θ : ℕ → ℝ) n

end

end GaloisForLFunctions.HTGeometry
