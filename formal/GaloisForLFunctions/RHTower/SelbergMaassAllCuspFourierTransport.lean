import GaloisForLFunctions.RHTower.SelbergMaassAffineFourierTransport

/-!
# Fourier transport for an upper-triangular cusp summand

An upper-triangular positive real action is affine on each horizontal cusp slice.
This file packages the existing matrix-coordinate and affine-Fourier identities into the
coefficient formula needed for an individual summand of a finite all-cusp trace.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory
open _root_.RHTower
open Complex UpperHalfPlane SelbergMaassMean
open scoped MatrixGroups

noncomputable section

/-- An upper-triangular positive real action sends a Fourier coefficient to the corresponding
shifted source window.  No periodicity is assumed: this is the form that applies to individual
summands before a finite all-cusp trace restores a common period. -/
theorem deningerFourierCoeff_upperTriangular_windowed_pullback
    (U : GL (Fin 2) ℝ) (hU : U 1 0 = 0) (hdet : 0 < U.det.val)
    {w y : ℝ} (hw : w ≠ 0) (hy : 0 < y) (F : ℂ → ℂ) (n : ℤ) :
    deningerFourierCoeff w
        (fun x => F (((U • ofComplex (point x y) : ℍ) : ℂ))) n =
      deningerFourierCoeff (upperTriangularScale U * w)
        (fun x => F (point (x + upperTriangularShift U)
          (upperTriangularScale U * y))) n := by
  have hscale : upperTriangularScale U ≠ 0 :=
    ne_of_gt (upperTriangular_scale_pos U hU hdet)
  have hrewrite :
      (fun x => F (((U • ofComplex (point x y) : ℍ) : ℂ))) =
        fun x => F (point (upperTriangularScale U * x + upperTriangularShift U)
          (upperTriangularScale U * y)) := by
    funext x
    rw [upperTriangular_smul_point U hU hdet x y hy]
  rw [hrewrite]
  simpa only using deningerFourierCoeff_comp_mul hw hscale
    (F := fun x => F (point (x + upperTriangularShift U)
      (upperTriangularScale U * y))) n

/-- An upper-triangular positive real action transports a horizontal Fourier coefficient by
its literal cusp scale and translation character. -/
theorem deningerFourierCoeff_upperTriangular_pullback
    (U : GL (Fin 2) ℝ) (hU : U 1 0 = 0) (hdet : 0 < U.det.val)
    {w y : ℝ} (hw : w ≠ 0) (hy : 0 < y) (F : ℂ → ℂ)
    (hper : Function.Periodic
      (fun x => F (point x (upperTriangularScale U * y)))
      (upperTriangularScale U * w)) (n : ℤ) :
    deningerFourierCoeff w
        (fun x => F (((U • ofComplex (point x y) : ℍ) : ℂ))) n =
      deningerFourierKernel (upperTriangularScale U * w) n (-upperTriangularShift U) *
        deningerFourierCoeff (upperTriangularScale U * w)
          (fun x => F (point x (upperTriangularScale U * y))) n := by
  have hscale : upperTriangularScale U ≠ 0 :=
    ne_of_gt (upperTriangular_scale_pos U hU hdet)
  have hrewrite :
      (fun x => F (((U • ofComplex (point x y) : ℍ) : ℂ))) =
        fun x => F (point (upperTriangularScale U * x + upperTriangularShift U)
          (upperTriangularScale U * y)) := by
    funext x
    rw [upperTriangular_smul_point U hU hdet x y hy]
  rw [hrewrite]
  exact deningerFourierCoeff_comp_affine hw hscale hper n

end

end GaloisForLFunctions.RHTower
