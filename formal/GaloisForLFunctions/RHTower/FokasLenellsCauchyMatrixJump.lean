import GaloisForLFunctions.RHTower.FokasLenellsCauchyMatrixNorm
import GaloisForLFunctions.RHTower.FokasLenellsLinftyScattering

/-!
# Exact Cauchy norm laws for every existing matrix jump generator

The genuine regularized jump, time derivative, space derivative, mixed
operator, and internally compatible second-time derivative are matrices
of ordinary L-infinity symbols. Their full norms and mutual distances are
preserved by the signed boundary Cauchy projection.
-/

open MeasureTheory Matrix
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
namespace RHTower.FokasLenells
noncomputable section

/-- The actual directJumpPerturbation written as a matrix of its own L-infinity symbols. -/
def directLinftyJumpMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ)) :=
  regularizedLinftyJumpMatrix (directLinftySymbol q t x false) (directLinftySymbol q t x true)

/-- This matrix representation is exactly the previously implemented jump operator. -/
theorem directJumpPerturbation_eq_boundaryLinftyMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    directJumpPerturbation q t x = boundaryLinftyMatrix (directLinftyJumpMatrix q t x) := by
  apply ContinuousLinearMap.ext
  intro u
  change (-directMultiplier q t x false u.2,
    directMultiplier q t x true u.1 - directMultiplier q t x false (directMultiplier q t x true u.2)) =
      boundaryLinftyMatrix (regularizedLinftyJumpMatrix
        (directLinftySymbol q t x false) (directLinftySymbol q t x true)) u
  rw [boundaryLinftyMatrix_regularizedJump_apply]
  simp only [directMultiplier_eq_lineLinftyMultiplier]

/-- Cauchy compression preserves the complete norm of the actual directJumpPerturbation. -/
theorem norm_directCauchyOperator_eq_jump (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directCauchyOperator q t x‖ = ‖directJumpPerturbation q t x‖ := by
  change ‖boundaryCauchy.comp (directJumpPerturbation q t x)‖ = _
  rw [directJumpPerturbation_eq_boundaryLinftyMatrix, norm_boundaryCauchy_comp_boundaryLinftyMatrix]

/-- Approximation errors between any two members of this actual family retain their full norm. -/
theorem dist_directCauchyOperator_eq_jump (q p : SchwartzMap ℝ ℂ) (t x s y : ℝ) :
    dist (directCauchyOperator q t x) (directCauchyOperator p s y) =
      dist (directJumpPerturbation q t x) (directJumpPerturbation p s y) := by
  change dist (boundaryCauchy.comp (directJumpPerturbation q t x))
    (boundaryCauchy.comp (directJumpPerturbation p s y)) = _
  rw [directJumpPerturbation_eq_boundaryLinftyMatrix, directJumpPerturbation_eq_boundaryLinftyMatrix]
  exact dist_boundaryCauchy_comp_boundaryLinftyMatrix _ _

/-- The actual directJumpTimeOperator written as a matrix of its own L-infinity symbols. -/
def directLinftyTimeMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ)) :=
  offDiagonalLinftyMatrix (directTimeLinftySymbol q t x false) (directTimeLinftySymbol q t x true)

/-- This matrix representation is exactly the previously implemented jump operator. -/
theorem directJumpTimeOperator_eq_boundaryLinftyMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    directJumpTimeOperator q t x = boundaryLinftyMatrix (directLinftyTimeMatrix q t x) := by
  apply ContinuousLinearMap.ext
  intro u
  change (-directTimeMultiplier q t x false u.2, directTimeMultiplier q t x true u.1) =
    boundaryLinftyMatrix (offDiagonalLinftyMatrix
      (directTimeLinftySymbol q t x false) (directTimeLinftySymbol q t x true)) u
  rw [boundaryLinftyMatrix_offDiagonal_apply]
  simp only [directTimeMultiplier_eq_lineLinftyMultiplier]

/-- Cauchy compression preserves the complete norm of the actual directJumpTimeOperator. -/
theorem norm_directCauchyTimeOperator_eq_jump (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directCauchyTimeOperator q t x‖ = ‖directJumpTimeOperator q t x‖ := by
  change ‖boundaryCauchy.comp (directJumpTimeOperator q t x)‖ = _
  rw [directJumpTimeOperator_eq_boundaryLinftyMatrix, norm_boundaryCauchy_comp_boundaryLinftyMatrix]

/-- Approximation errors between any two members of this actual family retain their full norm. -/
theorem dist_directCauchyTimeOperator_eq_jump (q p : SchwartzMap ℝ ℂ) (t x s y : ℝ) :
    dist (directCauchyTimeOperator q t x) (directCauchyTimeOperator p s y) =
      dist (directJumpTimeOperator q t x) (directJumpTimeOperator p s y) := by
  change dist (boundaryCauchy.comp (directJumpTimeOperator q t x))
    (boundaryCauchy.comp (directJumpTimeOperator p s y)) = _
  rw [directJumpTimeOperator_eq_boundaryLinftyMatrix, directJumpTimeOperator_eq_boundaryLinftyMatrix]
  exact dist_boundaryCauchy_comp_boundaryLinftyMatrix _ _

/-- Exact two-channel norm of the actual derivative, with no budget overestimate. -/
theorem norm_directJumpTimeOperator_eq_linfty (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directJumpTimeOperator q t x‖ = max ‖directTimeLinftySymbol q t x false‖ ‖directTimeLinftySymbol q t x true‖ := by
  rw [directJumpTimeOperator_eq_boundaryLinftyMatrix]
  exact norm_boundaryLinftyMatrix_offDiagonal _ _

/-- The exact two-channel derivative norm also holds after Cauchy projection. -/
theorem norm_directCauchyTimeOperator_eq_linfty (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directCauchyTimeOperator q t x‖ = max ‖directTimeLinftySymbol q t x false‖ ‖directTimeLinftySymbol q t x true‖ := by
  rw [norm_directCauchyTimeOperator_eq_jump, norm_directJumpTimeOperator_eq_linfty]

/-- The actual directJumpSpaceOperator written as a matrix of its own L-infinity symbols. -/
def directLinftySpaceMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ)) :=
  offDiagonalLinftyMatrix (directSpaceLinftySymbol q t x false) (directSpaceLinftySymbol q t x true)

/-- This matrix representation is exactly the previously implemented jump operator. -/
theorem directJumpSpaceOperator_eq_boundaryLinftyMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    directJumpSpaceOperator q t x = boundaryLinftyMatrix (directLinftySpaceMatrix q t x) := by
  apply ContinuousLinearMap.ext
  intro u
  change (-directSpaceMultiplier q t x false u.2, directSpaceMultiplier q t x true u.1) =
    boundaryLinftyMatrix (offDiagonalLinftyMatrix
      (directSpaceLinftySymbol q t x false) (directSpaceLinftySymbol q t x true)) u
  rw [boundaryLinftyMatrix_offDiagonal_apply]
  simp only [directSpaceMultiplier_eq_lineLinftyMultiplier]

/-- Cauchy compression preserves the complete norm of the actual directJumpSpaceOperator. -/
theorem norm_directCauchySpaceOperator_eq_jump (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directCauchySpaceOperator q t x‖ = ‖directJumpSpaceOperator q t x‖ := by
  change ‖boundaryCauchy.comp (directJumpSpaceOperator q t x)‖ = _
  rw [directJumpSpaceOperator_eq_boundaryLinftyMatrix, norm_boundaryCauchy_comp_boundaryLinftyMatrix]

/-- Approximation errors between any two members of this actual family retain their full norm. -/
theorem dist_directCauchySpaceOperator_eq_jump (q p : SchwartzMap ℝ ℂ) (t x s y : ℝ) :
    dist (directCauchySpaceOperator q t x) (directCauchySpaceOperator p s y) =
      dist (directJumpSpaceOperator q t x) (directJumpSpaceOperator p s y) := by
  change dist (boundaryCauchy.comp (directJumpSpaceOperator q t x))
    (boundaryCauchy.comp (directJumpSpaceOperator p s y)) = _
  rw [directJumpSpaceOperator_eq_boundaryLinftyMatrix, directJumpSpaceOperator_eq_boundaryLinftyMatrix]
  exact dist_boundaryCauchy_comp_boundaryLinftyMatrix _ _

/-- Exact two-channel norm of the actual derivative, with no budget overestimate. -/
theorem norm_directJumpSpaceOperator_eq_linfty (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directJumpSpaceOperator q t x‖ = max ‖directSpaceLinftySymbol q t x false‖ ‖directSpaceLinftySymbol q t x true‖ := by
  rw [directJumpSpaceOperator_eq_boundaryLinftyMatrix]
  exact norm_boundaryLinftyMatrix_offDiagonal _ _

/-- The exact two-channel derivative norm also holds after Cauchy projection. -/
theorem norm_directCauchySpaceOperator_eq_linfty (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directCauchySpaceOperator q t x‖ = max ‖directSpaceLinftySymbol q t x false‖ ‖directSpaceLinftySymbol q t x true‖ := by
  rw [norm_directCauchySpaceOperator_eq_jump, norm_directJumpSpaceOperator_eq_linfty]

/-- The actual directJumpMixedOperator written as a matrix of its own L-infinity symbols. -/
def directLinftyMixedMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ)) :=
  offDiagonalLinftyMatrix (directLinftySymbol q t x false) (directLinftySymbol q t x true)

/-- This matrix representation is exactly the previously implemented jump operator. -/
theorem directJumpMixedOperator_eq_boundaryLinftyMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    directJumpMixedOperator q t x = boundaryLinftyMatrix (directLinftyMixedMatrix q t x) := by
  apply ContinuousLinearMap.ext
  intro u
  change (-directMultiplier q t x false u.2, directMultiplier q t x true u.1) =
    boundaryLinftyMatrix (offDiagonalLinftyMatrix
      (directLinftySymbol q t x false) (directLinftySymbol q t x true)) u
  rw [boundaryLinftyMatrix_offDiagonal_apply]
  simp only [directMultiplier_eq_lineLinftyMultiplier]

/-- Cauchy compression preserves the complete norm of the actual directJumpMixedOperator. -/
theorem norm_directCauchyMixedOperator_eq_jump (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directCauchyMixedOperator q t x‖ = ‖directJumpMixedOperator q t x‖ := by
  change ‖boundaryCauchy.comp (directJumpMixedOperator q t x)‖ = _
  rw [directJumpMixedOperator_eq_boundaryLinftyMatrix, norm_boundaryCauchy_comp_boundaryLinftyMatrix]

/-- Approximation errors between any two members of this actual family retain their full norm. -/
theorem dist_directCauchyMixedOperator_eq_jump (q p : SchwartzMap ℝ ℂ) (t x s y : ℝ) :
    dist (directCauchyMixedOperator q t x) (directCauchyMixedOperator p s y) =
      dist (directJumpMixedOperator q t x) (directJumpMixedOperator p s y) := by
  change dist (boundaryCauchy.comp (directJumpMixedOperator q t x))
    (boundaryCauchy.comp (directJumpMixedOperator p s y)) = _
  rw [directJumpMixedOperator_eq_boundaryLinftyMatrix, directJumpMixedOperator_eq_boundaryLinftyMatrix]
  exact dist_boundaryCauchy_comp_boundaryLinftyMatrix _ _

/-- Exact two-channel norm of the actual derivative, with no budget overestimate. -/
theorem norm_directJumpMixedOperator_eq_linfty (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directJumpMixedOperator q t x‖ = max ‖directLinftySymbol q t x false‖ ‖directLinftySymbol q t x true‖ := by
  rw [directJumpMixedOperator_eq_boundaryLinftyMatrix]
  exact norm_boundaryLinftyMatrix_offDiagonal _ _

/-- The exact two-channel derivative norm also holds after Cauchy projection. -/
theorem norm_directCauchyMixedOperator_eq_linfty (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖directCauchyMixedOperator q t x‖ = max ‖directLinftySymbol q t x false‖ ‖directLinftySymbol q t x true‖ := by
  rw [norm_directCauchyMixedOperator_eq_jump, norm_directJumpMixedOperator_eq_linfty]

/-- The actual compatibleJumpSecondTimeOperator written as a matrix of its own L-infinity symbols. -/
def compatibleLinftySecondTimeMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    Matrix (Fin 2) (Fin 2) (Lp ℂ ∞ (volume : Measure ℝ)) :=
  offDiagonalLinftyMatrix (compatibleSecondTimeLinftySymbol q t x false) (compatibleSecondTimeLinftySymbol q t x true)

/-- This matrix representation is exactly the previously implemented jump operator. -/
theorem compatibleJumpSecondTimeOperator_eq_boundaryLinftyMatrix (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    compatibleJumpSecondTimeOperator q t x = boundaryLinftyMatrix (compatibleLinftySecondTimeMatrix q t x) := by
  apply ContinuousLinearMap.ext
  intro u
  change (-compatibleSecondTimeMultiplier q t x false u.2, compatibleSecondTimeMultiplier q t x true u.1) =
    boundaryLinftyMatrix (offDiagonalLinftyMatrix
      (compatibleSecondTimeLinftySymbol q t x false) (compatibleSecondTimeLinftySymbol q t x true)) u
  rw [boundaryLinftyMatrix_offDiagonal_apply]
  simp only [compatibleSecondTimeMultiplier_eq_lineLinftyMultiplier]

/-- Cauchy compression preserves the complete norm of the actual compatibleJumpSecondTimeOperator. -/
theorem norm_compatibleCauchySecondTimeOperator_eq_jump (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖compatibleCauchySecondTimeOperator q t x‖ = ‖compatibleJumpSecondTimeOperator q t x‖ := by
  change ‖boundaryCauchy.comp (compatibleJumpSecondTimeOperator q t x)‖ = _
  rw [compatibleJumpSecondTimeOperator_eq_boundaryLinftyMatrix, norm_boundaryCauchy_comp_boundaryLinftyMatrix]

/-- Approximation errors between any two members of this actual family retain their full norm. -/
theorem dist_compatibleCauchySecondTimeOperator_eq_jump (q p : SchwartzMap ℝ ℂ) (t x s y : ℝ) :
    dist (compatibleCauchySecondTimeOperator q t x) (compatibleCauchySecondTimeOperator p s y) =
      dist (compatibleJumpSecondTimeOperator q t x) (compatibleJumpSecondTimeOperator p s y) := by
  change dist (boundaryCauchy.comp (compatibleJumpSecondTimeOperator q t x))
    (boundaryCauchy.comp (compatibleJumpSecondTimeOperator p s y)) = _
  rw [compatibleJumpSecondTimeOperator_eq_boundaryLinftyMatrix, compatibleJumpSecondTimeOperator_eq_boundaryLinftyMatrix]
  exact dist_boundaryCauchy_comp_boundaryLinftyMatrix _ _

/-- Exact two-channel norm of the actual derivative, with no budget overestimate. -/
theorem norm_compatibleJumpSecondTimeOperator_eq_linfty (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖compatibleJumpSecondTimeOperator q t x‖ = max ‖compatibleSecondTimeLinftySymbol q t x false‖ ‖compatibleSecondTimeLinftySymbol q t x true‖ := by
  rw [compatibleJumpSecondTimeOperator_eq_boundaryLinftyMatrix]
  exact norm_boundaryLinftyMatrix_offDiagonal _ _

/-- The exact two-channel derivative norm also holds after Cauchy projection. -/
theorem norm_compatibleCauchySecondTimeOperator_eq_linfty (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ‖compatibleCauchySecondTimeOperator q t x‖ = max ‖compatibleSecondTimeLinftySymbol q t x false‖ ‖compatibleSecondTimeLinftySymbol q t x true‖ := by
  rw [norm_compatibleCauchySecondTimeOperator_eq_jump, norm_compatibleJumpSecondTimeOperator_eq_linfty]

/-- Equality of Cauchy operators is equivalent to equality of the full genuine jump operators. -/
theorem directCauchyOperator_eq_iff_jump (q p : SchwartzMap ℝ ℂ) (t x s y : ℝ) :
    directCauchyOperator q t x = directCauchyOperator p s y ↔
      directJumpPerturbation q t x = directJumpPerturbation p s y := by
  constructor
  · intro h
    apply eq_of_dist_eq_zero
    rw [← dist_directCauchyOperator_eq_jump]
    exact dist_eq_zero.mpr h
  · intro h
    apply eq_of_dist_eq_zero
    rw [dist_directCauchyOperator_eq_jump]
    exact dist_eq_zero.mpr h

end
end RHTower.FokasLenells
