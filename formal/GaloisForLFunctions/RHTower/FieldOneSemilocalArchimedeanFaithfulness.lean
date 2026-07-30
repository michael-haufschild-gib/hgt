import GaloisForLFunctions.RHTower.FieldOneFiniteAdeleIntegralBruhatTest

/-!
# Archimedean faithfulness of the semilocal Weyl tensor

Contracting a semilocal Weyl operator against the integral finite-adele
Bruhat test recovers its normalized archimedean Weyl multiplier.  Since the
archimedean multiplier is faithful, equality of semilocal operators forces
equality of their archimedean coordinates.

Consequently the rational diagonal action is faithful.  This is deliberately
weaker than full finite-adele self-duality: no claim that arbitrary finite
coordinates are separated is used or proved here.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open scoped TensorProduct

/-- Standard `2π` normalization does not destroy faithfulness of the
archimedean Weyl action. -/
theorem fieldOneSemilocalArchimedeanWeylMultiplier_injective :
    Function.Injective fieldOneSemilocalArchimedeanWeylMultiplier := by
  intro h k heq
  have hcontinuous :
      HTGeometry.FieldOneCore.fieldOneArchimedeanWeylMultiplier
          (2 * Real.pi * h) =
        HTGeometry.FieldOneCore.fieldOneArchimedeanWeylMultiplier
          (2 * Real.pi * k) := by
    apply ContinuousLinearMap.ext
    intro f
    exact DFunLike.congr_fun heq f
  have hscaled :
      2 * Real.pi * h = 2 * Real.pi * k :=
    HTGeometry.FieldOneCore.fieldOneArchimedeanWeylMultiplier_injective
      hcontinuous
  exact mul_left_cancel₀
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
    hscaled

/-- Equality of semilocal Weyl operators forces equality of archimedean
coordinates. -/
theorem fieldOneSemilocalBruhatWeylMultiplier_eq_imp_fst_eq
    {a b : ℝ × FieldOneFiniteAdele}
    (heq :
      fieldOneSemilocalBruhatWeylMultiplier a =
        fieldOneSemilocalBruhatWeylMultiplier b) :
    a.1 = b.1 := by
  apply fieldOneSemilocalArchimedeanWeylMultiplier_injective
  apply LinearMap.ext
  intro f
  have htensor :=
    congrArg
      (fun T :
          FieldOneSemilocalBruhatSchwartz →ₗ[ℂ]
            FieldOneSemilocalBruhatSchwartz =>
        T (f ⊗ₜ[ℂ] fieldOneFiniteAdeleIntegralBruhatTest))
      heq
  have hcontract :=
    congrArg fieldOneSemilocalContractFiniteZero htensor
  simpa only [
    fieldOneSemilocalBruhatWeylMultiplier_tmul,
    fieldOneSemilocalContractFiniteZero_tmul,
    fieldOneFiniteAdeleStandardWeylMultiplier_integralTest_zero,
    one_smul] using hcontract

/-- The canonical rational diagonal Weyl action on the semilocal algebraic
Bruhat--Schwartz tensor is faithful. -/
theorem fieldOneRationalDiagonalBruhatWeylMultiplier_injective :
    Function.Injective
      fieldOneRationalDiagonalBruhatWeylMultiplier := by
  intro q r heq
  have hreal :
      ((q : ℝ),
          algebraMap ℚ FieldOneFiniteAdele q).1 =
        ((r : ℝ),
          algebraMap ℚ FieldOneFiniteAdele r).1 := by
    apply fieldOneSemilocalBruhatWeylMultiplier_eq_imp_fst_eq
    simpa only [
      fieldOneRationalDiagonalBruhatWeylMultiplier,
      fieldOneRationalDiagonalSemilocalParameter] using! heq
  change (q : ℝ) = (r : ℝ) at hreal
  exact_mod_cast hreal

end

end GaloisForLFunctions.RHTower
