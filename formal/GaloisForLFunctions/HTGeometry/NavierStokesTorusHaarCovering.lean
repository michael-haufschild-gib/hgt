import GaloisForLFunctions.HTGeometry.IntegerTorusReturnVolume
import Mathlib.Tactic.NormNum

/-!
# Navier-Stokes torus-covering Haar invariance

This file extracts the Haar-average assertion (6.19) in Lemma 6.2 of the supplied
Navier-Stokes paper.  The corpus already proves that every nonsingular integer matrix pushes
normalized torus Haar measure to itself.  We expose the corresponding Bochner-integral
invariance and specialize it to the paper's matrix

`Jg = !![3, 1; 1, 5]`, whose determinant is `14`.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry.NavierStokesTorusHaarCovering

noncomputable section

variable {k : Type*} [Fintype k] [DecidableEq k]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Pushforward by a nonsingular integer torus endomorphism preserves normalized Haar measure. -/
theorem map_torusIntegerHom_haar {N : Matrix k k ℤ} (hdet : N.det ≠ 0) :
    Measure.map (torusIntegerHom (N : k → k → ℤ))
        (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) =
      (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) := by
  have hmap := congrArg (fun μ : ProbabilityMeasure (UnitAddTorus k) =>
    (μ : Measure (UnitAddTorus k))) (orbitClosureHaar_eq_haar hdet)
  simpa [orbitClosureHaar, ProbabilityMeasure.toMeasure_map] using hmap

/-- **Lemma 6.2, Haar-average form.** Pullback by a nonsingular integer torus
endomorphism preserves every strongly measurable Bochner integral. -/
theorem integral_comp_torusIntegerHom {N : Matrix k k ℤ} (hdet : N.det ≠ 0)
    (f : UnitAddTorus k → F)
    (hf : AEStronglyMeasurable f
      (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k))) :
    (∫ x, f (torusIntegerHom (N : k → k → ℤ) x)
        ∂(finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k))) =
      ∫ x, f x
        ∂(finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) := by
  let μ := (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k))
  have hfmap : AEStronglyMeasurable f
      (Measure.map (torusIntegerHom (N : k → k → ℤ)) μ) := by
    rw [map_torusIntegerHom_haar hdet]
    exact hf
  calc
    (∫ x, f (torusIntegerHom (N : k → k → ℤ) x) ∂μ) =
        ∫ x, f x ∂Measure.map (torusIntegerHom (N : k → k → ℤ)) μ :=
      (integral_map (continuous_torusIntegerHom (N : k → k → ℤ)).aemeasurable hfmap).symm
    _ = ∫ x, f x ∂μ := by rw [map_torusIntegerHom_haar hdet]

/-- Integer covering matrix `Jg` from equation (6.2). -/
def navierStokesCoverMatrix : Matrix (Fin 2) (Fin 2) ℤ :=
  !![3, 1; 1, 5]

/-- The paper's covering has degree fourteen. -/
theorem det_navierStokesCoverMatrix : navierStokesCoverMatrix.det = 14 := by
  norm_num [navierStokesCoverMatrix, Matrix.det_fin_two]

/-- Every iterated covering in Lemma 6.2 remains nonsingular. -/
theorem det_pow_navierStokesCoverMatrix_ne_zero (n : ℕ) :
    (navierStokesCoverMatrix ^ n).det ≠ 0 := by
  rw [Matrix.det_pow, det_navierStokesCoverMatrix]
  exact pow_ne_zero n (by norm_num)

/-- **Equation (6.19).** Haar averages agree after pullback by every power of the paper's
degree-fourteen torus covering. -/
theorem integral_comp_navierStokesCoverMatrix_pow (n : ℕ)
    (f : UnitAddTorus (Fin 2) → F)
    (hf : AEStronglyMeasurable f
      (finiteTorusHaarProbabilityMeasure (Fin 2) : Measure (UnitAddTorus (Fin 2)))) :
    (∫ x, f (torusIntegerHom
        ((navierStokesCoverMatrix ^ n : Matrix (Fin 2) (Fin 2) ℤ) : Fin 2 → Fin 2 → ℤ) x)
        ∂(finiteTorusHaarProbabilityMeasure (Fin 2) : Measure (UnitAddTorus (Fin 2)))) =
      ∫ x, f x
        ∂(finiteTorusHaarProbabilityMeasure (Fin 2) : Measure (UnitAddTorus (Fin 2))) := by
  exact integral_comp_torusIntegerHom (det_pow_navierStokesCoverMatrix_ne_zero n) f hf

end

end GaloisForLFunctions.HTGeometry.NavierStokesTorusHaarCovering
