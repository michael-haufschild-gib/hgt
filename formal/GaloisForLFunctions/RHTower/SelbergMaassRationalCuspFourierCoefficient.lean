import GaloisForLFunctions.RHTower.SelbergMaassRationalCuspFourierTransport

/-!
# Coefficients of a rational Maass pullback at every cusp

A positive rational correspondence transports each literal cusp Fourier
coefficient to one Fourier coefficient of an integral translate of the original
Maass source, with an explicit unit-modulus translation character. This removes
the remaining analytic coordinate freedom from an individual trace summand.
Finite trace aggregation and sign orientation are not established here.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory
open _root_.RHTower
open Complex UpperHalfPlane SelbergMaassMean Matrix SpecialLinearGroup GeneralLinearGroup
open SelbergMaassCuspTransport SelbergMaassFourier
open scoped MatrixGroups

noncomputable section

theorem rationalGL_pullback_cusp_fourier_coefficient (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val) (B : SL2Z)
    {y : ℝ} (hy : 0 < y) (n : ℤ) :
    ∃ A : SL2Z, ∃ U : GL (Fin 2) ℝ,
      U 1 0 = 0 ∧ 0 < U.det.val ∧
      deningerFourierCoeff ((N + 1 : ℕ) / upperTriangularScale U)
          (fun x => f.1.1 (g.map (algebraMap ℚ ℝ) •
            (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y)))) n =
        deningerFourierKernel (N + 1 : ℕ) n (-upperTriangularShift U) *
          maassCoefficient N (translate (N + 1) A f) n (upperTriangularScale U * y) := by
  obtain ⟨A, U, hU, hdet, hfactor⟩ := rationalGL_integral_cusp_factor g hg B
  refine ⟨A, U, hU, hdet, ?_⟩
  let F : ℂ → ℂ := fun z => (translate (N + 1) A f).1.1 (UpperHalfPlane.ofComplex z)
  have hscale : upperTriangularScale U ≠ 0 :=
    ne_of_gt (upperTriangular_scale_pos U hU hdet)
  have hwidth : upperTriangularScale U * ((N + 1 : ℕ) / upperTriangularScale U) =
      (N + 1 : ℕ) := by
    field_simp
  have hperiod0 : Function.Periodic
      (fun x => F (point x (upperTriangularScale U * y))) (N + 1 : ℕ) := by
    intro x
    exact maass_periodic N (translate (N + 1) A f) x
      (mul_pos (upperTriangular_scale_pos U hU hdet) hy)
  have hperiod : Function.Periodic
      (fun x => F (point x (upperTriangularScale U * y)))
      (upperTriangularScale U * ((N + 1 : ℕ) / upperTriangularScale U)) := by
    rw [hwidth]
    exact hperiod0
  have hleft :
      (fun x => f.1.1 (g.map (algebraMap ℚ ℝ) •
          (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y)))) =
        fun x => F (((U • UpperHalfPlane.ofComplex (point x y) : ℍ) : ℂ)) := by
    funext x
    change f.1.1 (g.map (algebraMap ℚ ℝ) •
      (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))) =
      (translate (N + 1) A f).1.1
        (UpperHalfPlane.ofComplex ((U • UpperHalfPlane.ofComplex (point x y) : ℍ) : ℂ))
    simp only [translate_apply, UpperHalfPlane.ofComplex_apply]
    calc
      f.1.1 (g.map (algebraMap ℚ ℝ) •
          (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))) =
          f.1.1 ((g.map (algebraMap ℚ ℝ) * mapGL ℝ B) •
            UpperHalfPlane.ofComplex (point x y)) := by rw [mul_smul]
      _ = f.1.1 ((mapGL ℝ A * U) • UpperHalfPlane.ofComplex (point x y)) :=
        congrArg (fun M : GL (Fin 2) ℝ =>
          f.1.1 (M • UpperHalfPlane.ofComplex (point x y))) hfactor
      _ = f.1.1 (mapGL ℝ A • (U • UpperHalfPlane.ofComplex (point x y))) := by
        rw [mul_smul]
  rw [hleft]
  have htransport := deningerFourierCoeff_upperTriangular_pullback U hU hdet
    (div_ne_zero (by positivity) hscale) hy F hperiod n
  rw [hwidth] at htransport
  simpa only [F, maassCoefficient, coefficient, Function.comp_apply] using htransport

end

end GaloisForLFunctions.RHTower
