import GaloisForLFunctions.HTGeometry.GammaPoleScaleSeparatedAffineHorizon
import GaloisForLFunctions.RHTower.GammaAffinePoleEnergyUniversalityLaw

/-!
# Gamma scale-separated affine order--energy universality

The scale-separated Gamma boundary and the moving-pole Gamma boundary use different coefficient
rings.  Constant-polynomial extension connects them: the degree-one scale horizon forces the
moving source onto its at-most-simple horizon, where local pole order and global approaching-line
energy blowup are equivalent at every branch.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions

noncomputable section

/-- Extend a complex-coefficient Gamma source to the moving-pole coefficient ring by constant
polynomials. -/
def constantMovingGammaSource {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial (Fin (n + 1)) (Polynomial ℂ) :=
  P.map (Polynomial.C : ℂ →+* Polynomial ℂ)

/-- **Scale/order/energy law.**  A complex Gamma source lying on the degree-one scale-separated
horizon extends to an at-most-simple moving source.  At every Gamma branch, exact simple order is
then equivalent to failure of every uniform approaching-line `L²` energy bound. -/
theorem gammaScaleSeparatedAffineHorizon_orderEnergyUniversality
    {n : ℕ} (P : MvPolynomial (Fin (n + 1)) ℂ)
    (hscale : (gammaScaleSeparatedSimplePoleProfileEval n P).natDegree ≤ 1) :
    GammaPoleProfileAtMostSimple n (constantMovingGammaSource P) ∧
      ∀ branch : ℕ,
        meromorphicOrderAt
            (fun x : ℂ => gammaPolyJetEval (n + 1)
              (-(branch : ℂ) + reciprocalGammaFactorialScale branch * x)
              (constantMovingGammaSource P)) 0 =
            ((-1 : ℤ) : WithTop ℤ) ↔
          ¬ ∃ C : ℝ, ∀ m : ℕ,
            (∫ t : ℝ, ‖RHTower.boundaryPoleApproachProfile 0
              (((MvPolynomial.pderiv (0 : Fin (n + 1))
                (constantMovingGammaSource P)).coeff 0).eval
                  (-(branch : ℂ))) m t‖ ^ 2) ≤ C := by
  rcases (gammaScaleSeparatedSimplePoleProfileEval_natDegree_le_one_iff_affine P).1 hscale with
    ⟨a, b, hP⟩
  have hprofile : GammaPoleProfileAtMostSimple n (constantMovingGammaSource P) := by
    apply (gammaPoleProfileAtMostSimple_iff_affine (constantMovingGammaSource P)).2
    refine ⟨Polynomial.C a, Polynomial.C b, ?_⟩
    simp [constantMovingGammaSource, hP]
  refine ⟨hprofile, fun branch => ?_⟩
  exact gammaPoleProfileAtMostSimple_simple_iff_boundaryEnergy_unbounded hprofile branch

end

end GaloisForLFunctions
