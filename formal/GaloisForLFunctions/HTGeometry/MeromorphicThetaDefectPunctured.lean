import GaloisForLFunctions.HTGeometry.MeromorphicPuncturedRepresentation
import GaloisForLFunctions.HTGeometry.EllipticGammaMixedFace

/-!
# Punctured-local realization of the theta logarithmic-derivative defect

The global meromorphic-field theta defect is represented, on every punctured neighborhood,
by the literal difference of the two pointwise theta logarithmic derivatives.  Consequently
all constant-coefficient differential operators on the field element are represented by the
corresponding ordinary differentiated theta defect.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance thetaDefectPuncturedDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance thetaDefectPuncturedComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance thetaDefectPuncturedComplexAlgebraMero : Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance thetaDefectPuncturedDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- Entire cross numerator of the pointwise theta logarithmic-derivative defect. -/
def thetaLogDerivDefectNumeratorFun (h τ : ℂ) : ℂ → ℂ := fun z =>
  jacobiTheta₂' (z + h) τ * jacobiTheta₂ z τ -
    jacobiTheta₂ (z + h) τ * jacobiTheta₂' z τ

/-- Entire product denominator of the pointwise theta logarithmic-derivative defect. -/
def thetaLogDerivDefectDenominatorFun (h τ : ℂ) : ℂ → ℂ := fun z =>
  jacobiTheta₂ (z + h) τ * jacobiTheta₂ z τ

theorem thetaLogDerivDefectNumeratorFun_analytic
    (h τ : ℂ) (hτ : 0 < τ.im) :
    AnalyticOnNhd ℂ (thetaLogDerivDefectNumeratorFun h τ) Set.univ := by
  have hθ := jacobiTheta₂_analyticOnNhd_fst τ hτ
  have hθ' := jacobiTheta₂'_analyticOnNhd_fst τ hτ
  have hshift : AnalyticOnNhd ℂ (fun z : ℂ => z + h) Set.univ :=
    analyticOnNhd_id.add analyticOnNhd_const
  exact ((hθ'.comp hshift (Set.mapsTo_univ _ _)).mul hθ).sub
    ((hθ.comp hshift (Set.mapsTo_univ _ _)).mul hθ')

theorem thetaLogDerivDefectDenominatorFun_analytic
    (h τ : ℂ) (hτ : 0 < τ.im) :
    AnalyticOnNhd ℂ (thetaLogDerivDefectDenominatorFun h τ) Set.univ := by
  have hθ := jacobiTheta₂_analyticOnNhd_fst τ hτ
  have hshift : AnalyticOnNhd ℂ (fun z : ℂ => z + h) Set.univ :=
    analyticOnNhd_id.add analyticOnNhd_const
  exact (hθ.comp hshift (Set.mapsTo_univ _ _)).mul hθ

/-- The global theta defect has its literal pointwise theta-defect function as a
punctured-local representative at every point. -/
theorem hasPuncturedMeromorphicRep_thetaLogDerivDefectMero
    (h τ : ℂ) (hτ : 0 < τ.im) :
    HasPuncturedMeromorphicRep (thetaLogDerivDefectMero h τ hτ)
      (thetaLogDerivDefect h · τ) := by
  let p := thetaLogDerivDefectNumeratorFun h τ
  let q := thetaLogDerivDefectDenominatorFun h τ
  have hp := thetaLogDerivDefectNumeratorFun_analytic h τ hτ
  have hq := thetaLogDerivDefectDenominatorFun_analytic h τ hτ
  have hpRep : Germ.coeRingHom (𝓟 Set.univ) p =
      (thetaLogDerivDefectNumeratorAnalytic h τ hτ : Germ (𝓟 Set.univ) ℂ) := by
    rfl
  have hqRep : Germ.coeRingHom (𝓟 Set.univ) q =
      (thetaLogDerivDefectDenominatorAnalytic h τ hτ : Germ (𝓟 Set.univ) ℂ) := by
    rfl
  rw [thetaLogDerivDefectMero_eq_div]
  apply (hasPuncturedMeromorphicRep_fraction
    (thetaLogDerivDefectDenominatorAnalytic_ne_zero h τ hτ)
    hp hq hpRep hqRep).congr_fun
  intro z
  have hqne := analyticSubring_rep_eventually_ne_zero
    (thetaLogDerivDefectDenominatorAnalytic_ne_zero h τ hτ) hq hqRep z
  filter_upwards [hqne] with w hqw
  have hθ : jacobiTheta₂ (w + h) τ ≠ 0 ∧ jacobiTheta₂ w τ ≠ 0 := by
    simpa only [q, thetaLogDerivDefectDenominatorFun, mul_ne_zero_iff] using hqw
  have heval := univGermEval_thetaLogDerivDefect_div_eq hτ hθ.2 hθ.1
  change p w / q w = thetaLogDeriv (w + h) τ - thetaLogDeriv w τ
  simpa only [hpRep, hqRep] using! heval

/-- Applying any constant-coefficient operator to the theta defect is represented by the
ordinary differentiated theta-defect function on every punctured neighborhood. -/
theorem hasPuncturedMeromorphicRep_differentialOperatorApply_thetaLogDerivDefectMero
    (L : Polynomial ℂ) (h τ : ℂ) (hτ : 0 < τ.im) :
    HasPuncturedMeromorphicRep
      (differentialOperatorApply L (thetaLogDerivDefectMero h τ hτ))
      (constantCoeffDifferentialOperator L (thetaLogDerivDefect h · τ)) :=
  (hasPuncturedMeromorphicRep_thetaLogDerivDefectMero h τ hτ).differentialOperatorApply L

end

end GaloisForLFunctions
