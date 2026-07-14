import GaloisForLFunctions.RHTower.SemilocalProjectionPhasePolarization
import GaloisForLFunctions.RHTower.SemilocalCompressedEulerOrientation

/-!
# Phase-polarized finite Euler orientation

This module wires the canonical projection phase rotation to the concrete finite Euler orientation
operator.  Every complex coefficient packet splits exactly into real and imaginary orientation
Grams.  For a real packet, the finite Euler orientation is the skew Gram of the weighted and
universal boundary sections.  Therefore a phase-rotated projection family with those literal
normal corners and compact base-compressed mixed derivative produces a compact finite Euler
orientation Gram.

Combined with finite quadratic Calkin faithfulness, this is the exact constraint-side interface
needed by the Sonin prime-seam route.  The remaining input is construction of the completed
prime--Gamma families on actual Xi zero fibres, not another algebraic orientation identity.
-/

open Complex

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-- The finite orientation matrix splits into its real and imaginary coefficient packets. -/
theorem finiteEulerOrientationMatrix_re_im
    {n : ℕ} (u : Fin n → ℂ) :
    finiteEulerOrientationMatrix u =
      finiteEulerOrientationMatrix (fun i ↦ ((u i).re : ℂ)) +
        Complex.I • finiteEulerOrientationMatrix (fun i ↦ ((u i).im : ℂ)) := by
  ext i j
  simp only [finiteEulerOrientationMatrix, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  apply Complex.ext <;> simp

/-- The finite Euler orientation Gram splits into real and imaginary packet orientations. -/
theorem finiteArchimedeanEulerOrientationGram_re_im
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (u : Fin n → ℂ) :
    finiteArchimedeanEulerOrientationGram a r u =
      finiteArchimedeanEulerOrientationGram a r (fun i ↦ ((u i).re : ℂ)) +
        Complex.I •
          finiteArchimedeanEulerOrientationGram a r (fun i ↦ ((u i).im : ℂ)) := by
  classical
  unfold finiteArchimedeanEulerOrientationGram
  rw [finiteEulerOrientationMatrix_re_im]
  unfold finiteArchimedeanPrimeEulerGramCombination
  simp only [Matrix.add_apply, Matrix.smul_apply, add_smul, smul_smul, Finset.sum_add_distrib,
    Finset.smul_sum, smul_eq_mul]

/-- For a real coefficient packet, the finite Euler orientation Gram is the literal skew Gram of
the weighted and universal boundary sections. -/
theorem finiteArchimedeanEulerOrientationGram_ofReal_eq_boundarySkew
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (u : Fin n → ℝ) :
    finiteArchimedeanEulerOrientationGram a r (fun i ↦ (u i : ℂ)) =
      adjoint
          (crossBoundary (archimedeanBoundaryCarrierProjection a)
            (finiteArchimedeanEulerSource r (fun i ↦ (u i : ℂ)))) *
        crossBoundary (archimedeanBoundaryCarrierProjection a)
          (finiteArchimedeanEulerSource r (fun _ ↦ 1)) -
      adjoint
          (crossBoundary (archimedeanBoundaryCarrierProjection a)
            (finiteArchimedeanEulerSource r (fun _ ↦ 1))) *
        crossBoundary (archimedeanBoundaryCarrierProjection a)
          (finiteArchimedeanEulerSource r (fun i ↦ (u i : ℂ))) := by
  simpa using finiteArchimedeanEulerOrientationGram_eq_boundary_skew
    a r (fun i ↦ (u i : ℂ))

/-- Compact phase-polarized skew Grams for the real and imaginary packets recombine into
compactness of the full complex finite Euler orientation Gram. -/
theorem finiteArchimedeanEulerOrientationGram_isCompact_of_re_im_boundarySkew
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (u : Fin n → ℂ)
    (hre : IsCompactOperator
      (finiteArchimedeanEulerOrientationGram a r (fun i ↦ ((u i).re : ℂ))))
    (him : IsCompactOperator
      (finiteArchimedeanEulerOrientationGram a r (fun i ↦ ((u i).im : ℂ)))) :
    IsCompactOperator (finiteArchimedeanEulerOrientationGram a r u) := by
  rw [finiteArchimedeanEulerOrientationGram_re_im]
  exact hre.add (him.smul Complex.I)

/-- A phase-rotated projection family with the concrete real-weighted and universal Euler
normal corners makes the corresponding finite Euler orientation Gram compact as soon as its
base-compressed mixed derivative is compact. -/
theorem finiteArchimedeanEulerOrientationGram_isCompact_of_phaseRotatedFamily
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (u : Fin n → ℝ)
    (F : ℝ → ℝ →
      (ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2))
    (Dt : ℝ → (ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2))
    (D Dst : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2)
    (ht : ∀ s, HasDerivAt (F s) (Dt s) 0)
    (hidem : ∀ s, (fun t ↦ F s t * F s t) =ᶠ[nhds 0] F s)
    (hs : HasDerivAt (fun s ↦ F s 0)
      (projectionPhaseRotation (F 0 0) D) 0)
    (hst : HasDerivAt Dt Dst 0)
    (hPadj : adjoint (F 0 0) = F 0 0)
    (hDadj : adjoint D = D)
    (hDtadj : adjoint (Dt 0) = Dt 0)
    (hnormalT : projectionNormalCorner (F 0 0) (Dt 0) =
      crossBoundary (archimedeanBoundaryCarrierProjection a)
        (finiteArchimedeanEulerSource r (fun i ↦ (u i : ℂ))))
    (hnormalD : projectionNormalCorner (F 0 0) D =
      crossBoundary (archimedeanBoundaryCarrierProjection a)
        (finiteArchimedeanEulerSource r (fun _ ↦ 1)))
    (hcompressed : IsCompactOperator (F 0 0 * Dst * F 0 0)) :
    IsCompactOperator
      (finiteArchimedeanEulerOrientationGram a r (fun i ↦ (u i : ℂ))) := by
  have hskew :=
    selfAdjointIdempotentFamily_phaseRotated_normalSkewGram_isCompact
      F Dt D Dst ht hidem hs hst hPadj hDadj hDtadj hcompressed
  rw [hnormalT, hnormalD] at hskew
  rw [finiteArchimedeanEulerOrientationGram_ofReal_eq_boundarySkew]
  exact hskew

end


end RHTower
