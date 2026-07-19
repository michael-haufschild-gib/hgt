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

/-- The finite orientation matrix is complex-linear in its coefficient packet. -/
theorem finiteEulerOrientationMatrix_linearCombination
    {n : ℕ} (alpha beta : ℂ) (u v : Fin n → ℂ) :
    finiteEulerOrientationMatrix (fun i ↦ alpha * u i + beta * v i) =
      alpha • finiteEulerOrientationMatrix u +
        beta • finiteEulerOrientationMatrix v := by
  ext i j
  simp only [finiteEulerOrientationMatrix, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- The complete finite Euler orientation Gram is complex-linear in its coefficient packet. -/
theorem finiteArchimedeanEulerOrientationGram_linearCombination
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (alpha beta : ℂ)
    (u v : Fin n → ℂ) :
    finiteArchimedeanEulerOrientationGram a r
        (fun i ↦ alpha * u i + beta * v i) =
      alpha • finiteArchimedeanEulerOrientationGram a r u +
        beta • finiteArchimedeanEulerOrientationGram a r v := by
  unfold finiteArchimedeanEulerOrientationGram
  rw [finiteEulerOrientationMatrix_linearCombination]
  unfold finiteArchimedeanPrimeEulerGramCombination
  simp only [Matrix.add_apply, Matrix.smul_apply, add_smul, smul_smul,
    Finset.sum_add_distrib, Finset.smul_sum, smul_eq_mul]

/-- Negating the coefficient packet negates the finite Euler orientation Gram. -/
theorem finiteArchimedeanEulerOrientationGram_neg
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (u : Fin n → ℂ) :
    finiteArchimedeanEulerOrientationGram a r (fun i ↦ -u i) =
      -finiteArchimedeanEulerOrientationGram a r u := by
  simpa using finiteArchimedeanEulerOrientationGram_linearCombination
    a r (-1) 0 u 0

/-- Adjointing a finite Euler orientation Gram conjugates its coefficient packet and reverses
orientation. -/
theorem adjoint_finiteArchimedeanEulerOrientationGram
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (u : Fin n → ℂ) :
    ContinuousLinearMap.adjoint (finiteArchimedeanEulerOrientationGram a r u) =
      -finiteArchimedeanEulerOrientationGram a r (fun i ↦ star (u i)) := by
  rw [finiteArchimedeanEulerOrientationGram_eq_boundary_skew,
    finiteArchimedeanEulerOrientationGram_eq_boundary_skew]
  let adj :
      (ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) ≃ₗᵢ⋆[ℂ]
        (ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) :=
    ContinuousLinearMap.adjoint
  have hadjMul (S T : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) :
      adj (S * T) = adj T * adj S := by
    exact ContinuousLinearMap.adjoint_comp S T
  have hadjAdj (S : ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2) :
      adj (adj S) = S := adjoint_adjoint S
  change adj (_ - _) = -(_ - _)
  rw [adj.map_sub, hadjMul, hadjMul, hadjAdj, hadjAdj]
  simp only [show (fun i ↦ star (star (u i))) = u by
    funext i
    simp]
  noncomm_ring

/-- Real coefficient packets produce skew-adjoint finite Euler orientation Grams without a
separate adjoint hypothesis. -/
theorem adjoint_finiteArchimedeanEulerOrientationGram_ofReal
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (u : Fin n → ℝ) :
    ContinuousLinearMap.adjoint
        (finiteArchimedeanEulerOrientationGram a r (fun i ↦ (u i : ℂ))) =
      -finiteArchimedeanEulerOrientationGram a r (fun i ↦ (u i : ℂ)) := by
  rw [adjoint_finiteArchimedeanEulerOrientationGram]
  congr 2
  funext i
  exact Complex.conj_ofReal _

/-- Purely imaginary coefficient packets produce self-adjoint finite Euler orientation Grams
without a separately supplied proposition. -/
theorem finiteArchimedeanEulerOrientationGram_ofImag_isSelfAdjoint
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (u : Fin n → ℝ) :
    IsSelfAdjoint
      (finiteArchimedeanEulerOrientationGram a r
        (fun i ↦ Complex.I * (u i : ℂ))) := by
  rw [isSelfAdjoint_iff]
  change ContinuousLinearMap.adjoint
      (finiteArchimedeanEulerOrientationGram a r
        (fun i ↦ Complex.I * (u i : ℂ))) = _
  rw [adjoint_finiteArchimedeanEulerOrientationGram]
  have hconj : (fun i ↦ star (Complex.I * (u i : ℂ))) =
      (fun i ↦ -(Complex.I * (u i : ℂ))) := by
    funext i
    simp
  rw [hconj, finiteArchimedeanEulerOrientationGram_neg]
  simp

/-- The finite orientation matrix splits into its real and imaginary coefficient packets. -/
theorem finiteEulerOrientationMatrix_re_im
    {n : ℕ} (u : Fin n → ℂ) :
    finiteEulerOrientationMatrix u =
      finiteEulerOrientationMatrix (fun i ↦ ((u i).re : ℂ)) +
        Complex.I • finiteEulerOrientationMatrix (fun i ↦ ((u i).im : ℂ)) := by
  rw [show u = fun i ↦ 1 * ((u i).re : ℂ) + Complex.I * ((u i).im : ℂ) by
    funext i
    apply Complex.ext <;> simp]
  simpa using finiteEulerOrientationMatrix_linearCombination
    1 Complex.I (fun i ↦ ((u i).re : ℂ)) (fun i ↦ ((u i).im : ℂ))

/-- The finite Euler orientation Gram splits into real and imaginary packet orientations. -/
theorem finiteArchimedeanEulerOrientationGram_re_im
    {n : ℕ} (a : ℝ) (r : Fin n → ℝ) (u : Fin n → ℂ) :
    finiteArchimedeanEulerOrientationGram a r u =
      finiteArchimedeanEulerOrientationGram a r (fun i ↦ ((u i).re : ℂ)) +
        Complex.I •
          finiteArchimedeanEulerOrientationGram a r (fun i ↦ ((u i).im : ℂ)) := by
  rw [show u = fun i ↦ 1 * ((u i).re : ℂ) + Complex.I * ((u i).im : ℂ) by
    funext i
    apply Complex.ext <;> simp]
  simpa using finiteArchimedeanEulerOrientationGram_linearCombination
    a r 1 Complex.I (fun i ↦ ((u i).re : ℂ)) (fun i ↦ ((u i).im : ℂ))

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
