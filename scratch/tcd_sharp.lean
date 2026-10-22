import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthProjectiveRefinedParabolicClockCone
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFullReflectionEighthProjectiveDrift

open Complex Real

namespace HTGeometry

noncomputable section

/-- Real source-chart evaluation of projective `D1` drift. -/
def modularThetaSourcePositiveReflectedEighthProjectiveDriftReal
    (U B Q : ℝ) : ℝ :=
  let w : ModularThetaSourcePositiveState → ℂ
    | .U => U
    | .B => B
    | .Q => Q
  Q * (MvPolynomial.eval w
      (modularThetaSourcePositiveLie
        modularThetaSourcePositiveReflectedEighthPolynomial)).re -
    6 * (MvPolynomial.eval w
      modularThetaSourcePositiveReflectedEighthPolynomial).re *
      (MvPolynomial.eval w
        (modularThetaSourcePositiveVectorField .Q)).re

end

end HTGeometry

namespace RHTower

open HTGeometry

noncomputable section

theorem thetaCuspReflectedEighthSourceProjectiveDrift_eq_evalPolynomial
    (x : ℝ) :
    thetaCuspReflectedEighthSourceProjectiveDrift x =
      modularThetaSourcePositiveReflectedEighthProjectiveDriftReal
        (thetaCuspModularQuasimodularDrift x)
        (-(thetaCuspModularDrift x).re / 3)
        ((6 * (-(thetaCuspModularDrift x).re / 3) ^ 2 +
          thetaCuspModularGapAmplitude x - 6) / 16) := by
  let w : ModularThetaSourcePositiveState → ℂ
    | .U => thetaCuspModularQuasimodularDrift x
    | .B => -(thetaCuspModularDrift x).re / 3
    | .Q => (6 * (-(thetaCuspModularDrift x).re / 3) ^ 2 +
        thetaCuspModularGapAmplitude x - 6) / 16
  have hw : (fun i => thetaCuspModularSourcePositiveState i x) = w := by
    funext i
    cases i <;> rfl
  unfold thetaCuspReflectedEighthSourceProjectiveDrift
  dsimp only
  rw [hw]
  unfold modularThetaSourcePositiveReflectedEighthProjectiveDriftReal
  dsimp only [w]
  simp only [Complex.ofReal_re]

end

end RHTower
