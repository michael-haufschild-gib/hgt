import GaloisForLFunctions.RHTower.SoninPrimeArchCofinalMomentSection

/-!
# Target-free positive all-prime Sonin moment-weld frontier

The source-defined all-prime residual energy is trace class, self-adjoint, and positive for every
positive aperture.  No Xi receiver enters that construction.  The remaining source-to-source
weld is exactly one positive aperture section along which every intrinsic trace moment converges
to `normalizedPrimeArchMoment`.  This weld is equivalent to the existing finite moment-block
closure and is sufficient for RH.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Target-free positive all-prime Sonin operator family, stated without any Xi receiver. -/
def SoninTargetFreePositiveAllPrimeOperatorFamily : Prop :=
  ∀ a : ℝ, ∀ ha : 0 < a,
    ContinuousLinearMap.IsTraceClass (soninAllPrimeResidualEnergyOperator a ha) ∧
      ContinuousLinearMap.adjoint (soninAllPrimeResidualEnergyOperator a ha) =
        soninAllPrimeResidualEnergyOperator a ha ∧
      ∀ x : SoninAllPrimeL2,
        0 ≤ Complex.re (inner ℂ x (soninAllPrimeResidualEnergyOperator a ha x))

/-- Exact source-to-source weld: one positive aperture section makes every intrinsic trace moment
converge to the normalized prime--archimedean moment with the same index. -/
def SoninAllPrimeExactTraceMomentWeld : Prop :=
  ∃ aperture : ℕ → ℝ,
    (∀ j, 0 < aperture j) ∧
      ∀ r,
        Tendsto (fun j => soninAllPrimeEnergyMoment (aperture j) r) atTop
          (nhds (((normalizedPrimeArchMoment r : ℝ) : ℂ)))

/-- Positive all-prime Sonin energy exists unconditionally for every positive aperture. -/
theorem soninTargetFreePositiveAllPrimeOperatorFamily :
    SoninTargetFreePositiveAllPrimeOperatorFamily := by
  intro a ha
  exact ⟨soninAllPrimeResidualEnergyOperator_isTraceClass a ha,
    adjoint_soninAllPrimeResidualEnergyOperator a ha,
    soninAllPrimeResidualEnergyOperator_re_inner_nonneg a ha⟩

/-- The named weld is definitionally the existing single-section moment coupling. -/
theorem soninAllPrimeExactTraceMomentWeld_iff_singleMomentCoupling :
    SoninAllPrimeExactTraceMomentWeld ↔
      ∃ aperture : ℕ → ℝ, SoninPrimeArchSingleMomentCoupling aperture := by
  rfl

/-- Exact finite-block characterization: no additional compatibility remains beyond one
coordinatewise convergent positive aperture section. -/
theorem soninAllPrimeExactTraceMomentWeld_iff_finiteMomentClosure :
    SoninAllPrimeExactTraceMomentWeld ↔ SoninPrimeArchFiniteMomentClosure := by
  rw [soninAllPrimeExactTraceMomentWeld_iff_singleMomentCoupling]
  exact soninPrimeArchFiniteMomentClosure_iff_exists_singleMomentCoupling.symm

/-- Closed frontier theorem: positive source operator family is unconditional, and exact
all-moment convergence is sufficient to close RH. -/
theorem soninTargetFreePositiveAllPrimeOperator_and_exactTraceMomentWeldFrontier :
    SoninTargetFreePositiveAllPrimeOperatorFamily ∧
      (SoninAllPrimeExactTraceMomentWeld → RiemannHypothesis) := by
  refine ⟨soninTargetFreePositiveAllPrimeOperatorFamily, ?_⟩
  rw [soninAllPrimeExactTraceMomentWeld_iff_singleMomentCoupling]
  rintro ⟨aperture, hcoupling⟩
  exact riemannHypothesis_of_soninPrimeArchSingleMomentCoupling hcoupling

end

end RHTower
