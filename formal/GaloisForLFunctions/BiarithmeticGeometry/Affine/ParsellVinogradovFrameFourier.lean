import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovProfileFourier
import GaloisForLFunctions.HTGeometry.Fourier.AffineIntegralNorm

/-!
# Uniform Fourier integral norms in physical moment coordinates

Every nondegenerate moment frame has an invertible linear part. Conjugating
this part to Euclidean coordinates transfers the finite normalized-profile
bound to the physical covering weights by affine Fourier invariance.
-/

open scoped FourierTransform
open MeasureTheory
open GaloisForLFunctions.HTGeometry.IntegerLatticePoisson

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- The linear part of a moment frame, with inverse obtained from the affine inverse. -/
def momentFrameLinearEquiv (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) : AffineAxisSpace r k ≃ₗ[ℝ] AffineAxisSpace r k where
  toLinearMap := Matrix.toLin' (scaledAffineMatrix r k ε δ t)
  invFun y := momentFrameInverse r k ε δ t (horizontalMoment r k 0 t + y)
  left_inv x := momentFrameInverse_frame r k ε hε δ t x
  right_inv y := by
    have h := momentFrame_frameInverse r k ε hε δ t (horizontalMoment r k 0 t + y)
    exact add_left_cancel h

/-- Finite-dimensional moment-frame linear maps are continuous in both directions. -/
def momentFrameLinearContinuousEquiv (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) : AffineAxisSpace r k ≃L[ℝ] AffineAxisSpace r k where
  toLinearEquiv := momentFrameLinearEquiv r k ε hε δ t
  continuous_toFun :=
    (LinearMap.toContinuousLinearMap (Matrix.toLin' (scaledAffineMatrix r k ε δ t))).continuous
  continuous_invFun := (contDiff_momentFrameInverse r k ε δ t).continuous.comp
    (continuous_const.add continuous_id)

/-- The linear frame in the Euclidean model of ambient moment space. -/
def momentFrameEuclideanLinearEquiv (r k : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    EuclideanSpace ℝ (AffineAxisIndex r k) ≃L[ℝ] EuclideanSpace ℝ (AffineAxisIndex r k) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : AffineAxisIndex r k => ℝ)).trans
    (momentFrameLinearContinuousEquiv r k ε hε δ t)).trans
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : AffineAxisIndex r k => ℝ)).symm

/-- A covering weight as a complex Schwartz function on moment coordinates. -/
def coveringWeightSchwartz (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i : ℤ) : SchwartzMap (AffineAxisSpace r k) ℂ :=
  ((hasCompactSupport_coveringWeight r k q ε hε δ i).comp_left
    (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (contDiff_coveringWeight r k q ε δ i))

/-- The physical covering weight in Euclidean moment coordinates. -/
def coveringWeightEuclideanSchwartz (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i : ℤ) :
    SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : AffineAxisIndex r k => ℝ))
      (coveringWeightSchwartz r k q ε hε δ i)

/-- Normalization pulls back the physical weight by an invertible affine Euclidean map. -/
theorem normalizedCoveringWeight_eq_affine (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i : ℤ) :
    normalizedCoveringWeight r k q ε δ i = fun x =>
      coveringWeightEuclideanSchwartz r k q ε hε δ i
        (WithLp.toLp 2 (horizontalMoment r k 0 (ε * (i : ℝ) / (q + 1 : ℝ))) +
          momentFrameEuclideanLinearEquiv r k ε hε δ (ε * (i : ℝ) / (q + 1 : ℝ)) x) := by
  funext x
  rfl

/-- Normalization preserves the entire inverse Fourier integral norm. -/
theorem normalizedCoveringWeight_fourierL1_eq (r k q : ℕ) (ε : ℝ) (hε : ε ≠ 0)
    (δ : Fin (r + 1) → ℝ) (i : ℤ) :
    (∫ x, ‖𝓕⁻ (normalizedCoveringWeight r k q ε δ i) x‖) =
      ∫ x, ‖(𝓕⁻ (coveringWeightEuclideanSchwartz r k q ε hε δ i) :
        SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r k)) ℂ) x‖ := by
  rw [normalizedCoveringWeight_eq_affine r k q ε hε, SchwartzMap.fourierInv_coe]
  exact integral_norm_fourierInv_comp_affine
    (coveringWeightEuclideanSchwartz r k q ε hε δ i :
      EuclideanSpace ℝ (AffineAxisIndex r k) → ℂ)
    (momentFrameEuclideanLinearEquiv r k ε hε δ (ε * (i : ℝ) / (q + 1 : ℝ)))
    (WithLp.toLp 2 (horizontalMoment r k 0 (ε * (i : ℝ) / (q + 1 : ℝ))))

/-- All physical ordered weights have uniformly bounded inverse Fourier integral norms. -/
theorem exists_uniform_coveringWeight_fourierL1 (r k q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : ε ≠ 0) (δ : Fin (r + 1) → ℝ) (i : ℤ),
      i ∈ dimensionCoveringGrid r q ε →
      (∫ x, ‖(𝓕⁻ (coveringWeightEuclideanSchwartz r (k + 1) q ε hε δ i) :
        SchwartzMap (EuclideanSpace ℝ (AffineAxisIndex r (k + 1))) ℂ) x‖) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_normalizedCoveringWeight_fourierL1 r k q
  refine ⟨C, hC, ?_⟩
  intro ε hε δ i hi
  rw [← normalizedCoveringWeight_fourierL1_eq]
  exact (hbound ε hε δ i hi).2


end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
