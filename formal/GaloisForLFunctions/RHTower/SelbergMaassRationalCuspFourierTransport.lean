import GaloisForLFunctions.RHTower.SelbergMaassAllCuspFourierTransport

/-!
# Fourier transport of a rational Maass pullback at every cusp

For every positive rational correspondence and every integral cusp scaling,
the literal Fourier integral of the rational pullback is a Fourier integral of
an integral translate of the original Maass source. The equality preserves the
exact scale, shift, height, and Fourier index. It is a summand-level identity;
combining the finite trace summands and proving their required sign orientation
remain separate arithmetic problems.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory
open _root_.RHTower
open Complex UpperHalfPlane SelbergMaassMean Matrix SpecialLinearGroup GeneralLinearGroup
open SelbergMaassCuspTransport
open scoped MatrixGroups

noncomputable section

/-- At an arbitrary integral cusp, one rational Maass pullback has the exact
Fourier window of an integral translate of the original source. -/
theorem rationalGL_pullback_cusp_fourier_windowed (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val) (B : SL2Z)
    {w y : ℝ} (hw : w ≠ 0) (hy : 0 < y) (n : ℤ) :
    ∃ A : SL2Z, ∃ U : GL (Fin 2) ℝ,
      U 1 0 = 0 ∧ 0 < U.det.val ∧
      deningerFourierCoeff w
          (fun x => f.1.1 (g.map (algebraMap ℚ ℝ) •
            (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y)))) n =
        deningerFourierCoeff (upperTriangularScale U * w)
          (fun x => (translate (N + 1) A f).1.1
            (UpperHalfPlane.ofComplex
              (point (x + upperTriangularShift U) (upperTriangularScale U * y)))) n := by
  obtain ⟨A, U, hU, hdet, hfactor⟩ := rationalGL_integral_cusp_factor g hg B
  refine ⟨A, U, hU, hdet, ?_⟩
  let F : ℂ → ℂ := fun z => (translate (N + 1) A f).1.1 (UpperHalfPlane.ofComplex z)
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
  simpa only [F] using
    deningerFourierCoeff_upperTriangular_windowed_pullback U hU hdet hw hy F n

end

end GaloisForLFunctions.RHTower
