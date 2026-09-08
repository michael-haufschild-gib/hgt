import GaloisForLFunctions.RHTower.SelbergMaassCurrentTests
import GaloisForLFunctions.RHTower.SelbergMaassCurvatureMeasure

/-!
# Actual current and positive residual curvature functionals

Proved signed compact-test regulator limits define a real linear current
functional. Comparison with the original curvature limit makes its exact
difference from the full source functional positive. No density-limit
interchange, nodal-support conclusion, or quarter comparison is assumed.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergMaassCurrentFunctional
open SelbergMaassCurrentTests SelbergMaassContinuousCurvature SelbergMaassCurvatureMeasure
  SelbergMaassWeakCurvature SelbergMaassRegulatorMass SelbergUpperHalfPlaneCompactTests
  SelbergMaassCurrentCurvature
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The proved actual regulator limit of a compact upper-half-plane current test. -/
def currentValue (g : C_c(ℍ, ℝ)) : ℝ :=
  limUnder regulatorAtZero (fun e : Ioi (0 : ℝ) => testedCurrent N f e (zeroExtend g))

/-- Every literal compact test converges to the constructed current value. -/
theorem current_limit (g : C_c(ℍ, ℝ)) :
    Tendsto (fun e : Ioi (0 : ℝ) => testedCurrent N f e (zeroExtend g)) regulatorAtZero
      (𝓝 (currentValue N f g)) :=
  tendsto_nhds_limUnder (exists_testedCurrent_limit N f
    (zeroExtend_continuous g) (zeroExtend_compact g) (zeroExtend_support g))

/-- The actual compact-test current limit is additive. -/
theorem currentValue_add (g h : C_c(ℍ, ℝ)) :
    currentValue N f (g + h) = currentValue N f g + currentValue N f h := by
  have hl := current_limit N f (g + h)
  simp only [zeroExtend_add, testedCurrent_add N f
    (zeroExtend_continuous g) (zeroExtend_compact g) (zeroExtend_support g)
    (zeroExtend_continuous h) (zeroExtend_compact h) (zeroExtend_support h)] at hl
  exact tendsto_nhds_unique hl ((current_limit N f g).add (current_limit N f h))

/-- The actual compact-test current limit commutes with every real scalar. -/
theorem currentValue_smul (c : ℝ) (g : C_c(ℍ, ℝ)) :
    currentValue N f (c • g) = c * currentValue N f g := by
  have hl := current_limit N f (c • g)
  simp only [zeroExtend_smul, testedCurrent_const_mul] at hl
  exact tendsto_nhds_unique hl ((current_limit N f g).const_mul c)

/-- Original current limits define an actual linear compact-test functional. -/
def currentFunctional : C_c(ℍ, ℝ) →ₗ[ℝ] ℝ where
  toFun := currentValue N f
  map_add' := currentValue_add N f
  map_smul' c g := currentValue_smul N f c g

private theorem zeroExtend_nonneg {g : C_c(ℍ, ℝ)} (hg : 0 ≤ g) : ∀ z, 0 ≤ zeroExtend g z := by
  intro z
  by_cases hz : 0 < z.im
  · simp only [zeroExtend, if_pos hz]
    exact hg _
  · simp only [zeroExtend, if_neg hz, le_refl]

/-- The actual current functional is positive on nonnegative compact tests. -/
theorem currentValue_nonneg {g : C_c(ℍ, ℝ)} (hg : 0 ≤ g) : 0 ≤ currentValue N f g :=
  ge_of_tendsto (current_limit N f g)
    (Eventually.of_forall (testedCurrent_nonneg N f (zeroExtend_nonneg hg)))

/-- The current functional lies below the full original curvature functional on nonnegative tests. -/
theorem currentValue_le_curvature {g : C_c(ℍ, ℝ)} (hg : 0 ≤ g) :
    currentValue N f g ≤ continuousCurvature N f (zeroExtend g) :=
  le_of_tendsto (current_limit N f g) (Eventually.of_forall
    (testedCurrent_le_limit N f (zeroExtend_continuous g) (zeroExtend_compact g)
      (zeroExtend_support g) (zeroExtend_nonneg hg)))

/-- The positive current functional comes from the literal regulated source integrals. -/
def currentPositiveFunctional : C_c(ℍ, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (currentFunctional N f) (fun _ hg => currentValue_nonneg N f hg)

/-- The exact difference from full source curvature is a linear residual functional. -/
def residualFunctional : C_c(ℍ, ℝ) →ₗ[ℝ] ℝ := compactFunctional N f - currentFunctional N f

/-- The actual residual functional is positive, proved from the source comparison at all regulators. -/
def residualPositiveFunctional : C_c(ℍ, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (residualFunctional N f) (by
    intro g hg
    change 0 ≤ continuousCurvature N f (zeroExtend g) - currentValue N f g
    exact sub_nonneg.mpr (currentValue_le_curvature N f hg))

/-- The actual current and residual functionals sum exactly to the original full curvature value. -/
theorem functional_sum (g : C_c(ℍ, ℝ)) :
    currentPositiveFunctional N f g + residualPositiveFunctional N f g =
      continuousCurvature N f (zeroExtend g) := by
  change currentValue N f g + (continuousCurvature N f (zeroExtend g) - currentValue N f g) = _
  ring

end
end GaloisForLFunctions.RHTower.SelbergMaassCurrentFunctional
