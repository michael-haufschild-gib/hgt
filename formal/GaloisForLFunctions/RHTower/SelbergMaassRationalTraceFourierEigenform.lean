import GaloisForLFunctions.RHTower.SelbergMaassRationalTraceFourierAggregation
import GaloisForLFunctions.RHTower.SelbergMaassFourierModes

/-!
# Fourier coefficients of nonzero rational Maass traces

The raw rational trace has an exact finite translated-window Fourier formula.
This module transfers that formula to the bundled principal-level Maass
cusp eigenform whenever the trace is nonzero.  Thus the Hecke correspondence
and the source Fourier/phase machinery act on the same literal coefficient.
No orientation or positivity of the finite window sum is asserted.
-/

namespace GaloisForLFunctions.RHTower

open MeasureTheory
open _root_.RHTower
open Complex UpperHalfPlane SelbergMaassMean Matrix SpecialLinearGroup GeneralLinearGroup
open SelbergMaassCuspTransport SelbergMaassFourier
open scoped BigOperators MatrixGroups

noncomputable section

/-- A nonzero rational principal trace, reindexed as its actual Maass cusp
source, has the exact finite translated-window formula at the standard cusp. -/
theorem rationalPrincipalTrace_cusp_maassCoefficient_sum (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)
    (g : GL (Fin 2) ℚ) (hg : 0 < (g.map (algebraMap ℚ ℝ)).det.val)
    (F : GLMaassCuspEigenform (principalCongruenceGL N) lam)
    (hF : F.1.1 = rationalPrincipalTraceFunction N g hg lam
      (integralMaassCuspEigenformToGL (CongruenceSubgroup.Gamma (N + 1)) lam f))
    {y : ℝ} (hy : 0 < y) (n : ℤ) :
    letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
      rationalConjugateGroup_isFiniteRelIndex N g
    letI := Fintype.ofFinite (principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
    ∃ A : (principalCongruenceGL N ⧸
        ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) → SL2Z,
      ∃ U : (principalCongruenceGL N ⧸
        ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N))) → GL (Fin 2) ℝ,
        (∀ q, (U q).val 1 0 = 0 ∧ 0 < (U q).det.val) ∧
        maassCoefficient N
          (glIntegralMaassCuspEigenformToMaass (CongruenceSubgroup.Gamma (N + 1)) lam F) n y =
          ∑ q, deningerFourierCoeff (upperTriangularScale (U q) * (N + 1 : ℕ))
            (fun x => (translate (N + 1) (A q) f).1.1
              (UpperHalfPlane.ofComplex (point (x + upperTriangularShift (U q))
                (upperTriangularScale (U q) * y)))) n := by
  letI : (rationalConjugateGroup N g).IsFiniteRelIndex (principalCongruenceGL N) :=
    rationalConjugateGroup_isFiniteRelIndex N g
  letI := Fintype.ofFinite
    (principalCongruenceGL N ⧸
      ((rationalConjugateGroup N g).subgroupOf (principalCongruenceGL N)))
  obtain ⟨A, U, hU, hsum⟩ :=
    rationalPrincipalTrace_cusp_fourier_window_sum N f g hg (1 : SL2Z)
      (w := (N + 1 : ℕ)) (y := y) (by positivity) hy n
  refine ⟨A, U, hU, ?_⟩
  rw [maassCoefficient, coefficient]
  change deningerFourierCoeff (N + 1 : ℕ)
    (fun x => F.1.1 (UpperHalfPlane.ofComplex (point x y))) n = _
  rw [hF]
  simpa using hsum

end

end GaloisForLFunctions.RHTower
