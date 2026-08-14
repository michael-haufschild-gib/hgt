import GaloisForLFunctions.RHTower.FieldOneFiniteStageThetaEquation423

/-!
# Literal finite-stage theta core as an exact Euler expansion

This file closes the source-side weld between the literal semilocal theta
core and the coefficient-faithful finite Euler value.  It retains the full
signed-lattice factor, the half-density weight, every prime label, and every
Boolean exponent.
-/

open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

/-- The literal theta-core half-density is exactly twice the positive-sign
finite Euler expansion, with the archimedean half-density factor exposed.
No quotient, scalarization, or relabeling occurs. -/
theorem fieldOneFiniteStageThetaBruhatCore_logHalfDensity_eq_exponentEuler
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, f (-x) = f x)
    (k : FieldOneFiniteStageModuleOneClass S) (t : ℝ) :
    fieldOneFiniteStageBruhatLogHalfDensity S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) (k, t) =
      2 * (Real.exp (t / 2) : ℂ) *
        fieldOneFiniteStageThetaPositiveEulerValue S f (Real.exp t) := by
  classical
  unfold fieldOneFiniteStageThetaPositiveEulerValue
  rw [fieldOneFiniteStageBruhatLogHalfDensity,
    fieldOneFiniteStageThetaBruhatCore_logPeriodization_eq_two_mul_positiveCube
      S f hf k t]
  have hsum :
      (∑ n ∈ fieldOneFiniteStageSoninExponentCube S,
        fieldOneFiniteStageBruhatOrbit S
          (fieldOneFiniteStageThetaBruhatCoreLinearMap S f)
          (fieldOneFiniteStageBruhatLogRayIdele S
            (fun v =>
              (fieldOneFiniteStageAngularTorusRepresentative S k v).1) t)
          (fieldOneSignedSUnitOfBool S true n)) =
        ∑ n ∈ fieldOneFiniteStageSoninExponentCube S,
          f (Real.exp t *
              (((fieldOneSUnitProduct S n : ℚˣ) : ℚ) : ℝ)) *
            fieldOneFiniteStageSoninExponentCoefficient S n := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [fieldOneFiniteStageThetaBruhatCore_orbit_signed_true]
  rw [hsum]
  rw [← mul_assoc]
  change ((Real.exp (t / 2) : ℂ) * (2 : ℂ)) * _ =
    ((2 : ℂ) * (Real.exp (t / 2) : ℂ)) * _
  rw [mul_comm (Real.exp (t / 2) : ℂ) (2 : ℂ)]

end

end GaloisForLFunctions.RHTower
