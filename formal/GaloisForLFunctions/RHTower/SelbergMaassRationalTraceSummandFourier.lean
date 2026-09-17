import GaloisForLFunctions.RHTower.SelbergMaassPrincipalPositiveRationalLifts
import GaloisForLFunctions.RHTower.SelbergMaassRationalCuspFourierTransport

/-!
# Cusp Fourier windows of actual rational trace summands

Each literal quotient component of a finite rational principal trace is a
positive rational pullback of the original Maass source. Its Fourier window at
every integral cusp therefore has the exact integral-translate expression. The
result exposes all trace terms in source coordinates; it does not assert a
common modal phase or a sign orientation after summation.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory
open _root_.RHTower
open Complex UpperHalfPlane SelbergMaassMean Matrix SpecialLinearGroup GeneralLinearGroup
open SelbergMaassCuspTransport
open scoped MatrixGroups

noncomputable section

/-- A literal quotient-trace component is, at every integral cusp, an integral
translate of the source after one positive affine coordinate change. -/
theorem rationalPrincipalTrace_summand_cusp_affine (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val) (B : SL2Z)
    (q : principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    {y : ℝ} (hy : 0 < y) :
    ∃ A : SL2Z, ∃ U : GL (Fin 2) ℝ,
      U 1 0 = 0 ∧ 0 < U.det.val ∧ ∀ x : ℝ,
        maassTraceQuotientFunc
          (rationalMaassPullback N g hg lam
            (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f)).1 q
          (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y)) =
        (translate (N + 1) A f).1.1 (UpperHalfPlane.ofComplex
          (point (upperTriangularScale U * x + upperTriangularShift U)
            (upperTriangularScale U * y))) := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  induction q using Quotient.inductionOn with
  | h r =>
    obtain ⟨a, ha, hapos⟩ := principalCongruenceGL_hasPositiveRationalLifts N r⁻¹
    have hga : 0 < ((g * a).map (algebraMap ℚ ℝ)).det.val :=
      rationalGL_map_det_mul_pos g a hg hapos
    obtain ⟨A, U, hU, hdet, hfactor⟩ := rationalGL_integral_cusp_factor (g * a) hga B
    refine ⟨A, U, hU, hdet, ?_⟩
    intro x
    have hpoint : U • UpperHalfPlane.ofComplex (point x y) =
        UpperHalfPlane.ofComplex
          (point (upperTriangularScale U * x + upperTriangularShift U)
            (upperTriangularScale U * y)) := by
      apply UpperHalfPlane.ext
      rw [upperTriangular_smul_point U hU hdet x y hy]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos]
      simp [point, upperTriangular_scale_pos U hU hdet, hy]
    rw [maassTraceQuotientFunc_mk]
    change f.1.1 (g.map (algebraMap ℚ ℝ) •
      ((r⁻¹).val • (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y)))) =
      (translate (N + 1) A f).1.1 (UpperHalfPlane.ofComplex
        (point (upperTriangularScale U * x + upperTriangularShift U)
          (upperTriangularScale U * y)))
    simp only [translate_apply]
    calc
      f.1.1 (g.map (algebraMap ℚ ℝ) •
          ((r⁻¹).val • (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y)))) =
          f.1.1 ((g.map (algebraMap ℚ ℝ) * (r⁻¹).val) •
            (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))) := by
        rw [mul_smul]
      _ = f.1.1 ((g.map (algebraMap ℚ ℝ) * a.map (algebraMap ℚ ℝ)) •
          (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))) := by rw [ha]
      _ = f.1.1 ((g * a).map (algebraMap ℚ ℝ) •
          (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))) := by
        rw [← Matrix.GeneralLinearGroup.map_mul]
      _ = f.1.1 (((g * a).map (algebraMap ℚ ℝ) * mapGL ℝ B) •
          UpperHalfPlane.ofComplex (point x y)) := by
        rw [mul_smul]
      _ = f.1.1 ((mapGL ℝ A * U) • UpperHalfPlane.ofComplex (point x y)) :=
        congrArg (fun M : GL (Fin 2) ℝ =>
          f.1.1 (M • UpperHalfPlane.ofComplex (point x y))) hfactor
      _ = f.1.1 (mapGL ℝ A • (U • UpperHalfPlane.ofComplex (point x y))) := by
        rw [mul_smul]
      _ = f.1.1 (mapGL ℝ A • UpperHalfPlane.ofComplex
          (point (upperTriangularScale U * x + upperTriangularShift U)
            (upperTriangularScale U * y))) := by rw [hpoint]

theorem rationalPrincipalTrace_summand_cusp_fourier_windowed (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val) (B : SL2Z)
    (q : principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) {w y : ℝ} (hw : w ≠ 0) (hy : 0 < y) (n : ℤ) :
    ∃ A : SL2Z, ∃ U : GL (Fin 2) ℝ,
      U 1 0 = 0 ∧ 0 < U.det.val ∧
      deningerFourierCoeff w
          (fun x => maassTraceQuotientFunc
            (rationalMaassPullback N g hg lam
              (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f)).1 q
            (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y))) n =
        deningerFourierCoeff (upperTriangularScale U * w)
          (fun x => (translate (N + 1) A f).1.1
            (UpperHalfPlane.ofComplex
              (point (x + upperTriangularShift U) (upperTriangularScale U * y)))) n := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  induction q using Quotient.inductionOn with
  | h r =>
    obtain ⟨a, ha, hapos⟩ := principalCongruenceGL_hasPositiveRationalLifts N r⁻¹
    have hga : 0 < ((g * a).map (algebraMap ℚ ℝ)).det.val :=
      rationalGL_map_det_mul_pos g a hg hapos
    obtain ⟨A, U, hU, hdet, hfourier⟩ :=
      rationalGL_pullback_cusp_fourier_windowed N f (g * a) hga B hw hy n
    refine ⟨A, U, hU, hdet, ?_⟩
    rw [← hfourier]
    congr 2
    funext x
    rw [maassTraceQuotientFunc_mk]
    change f.1.1 (g.map (algebraMap ℚ ℝ) •
      ((r⁻¹).val • (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y)))) =
      f.1.1 ((g * a).map (algebraMap ℚ ℝ) •
        (mapGL ℝ B • UpperHalfPlane.ofComplex (point x y)))
    rw [← ha, ← mul_smul, ← Matrix.GeneralLinearGroup.map_mul]

end

end GaloisForLFunctions.RHTower
