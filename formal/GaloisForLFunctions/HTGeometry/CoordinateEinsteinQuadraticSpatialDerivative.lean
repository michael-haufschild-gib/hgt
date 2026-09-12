import GaloisForLFunctions.HTGeometry.CoordinateEinsteinComplexVariations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.ComplexCoordinateMetricTwoJet
noncomputable section
variable {d : ℕ}
local notation "JetSpace" => ComplexMetricTwoJetSpace d

local instance real_clm_continuousSMul {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] :
    ContinuousSMul ℝ (E →L[ℂ] F) := IsScalarTower.continuousSMul ℂ

private theorem clm_apply_real {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    {c : ℝ → E →L[ℂ] F} {c' : E →L[ℂ] F} {u : ℝ → E} {u' : E} {t : ℝ}
    (hc : HasDerivAt c c' t) (hu : HasDerivAt u u' t) :
    HasDerivAt (fun x => c x (u x)) (c' (u t)+c t u') t := by
  have he := (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := E) (F := F)).hasFDerivAt (c t,u t)
  have hh := (he.restrictScalars ℝ).comp_hasDerivAt t (HasDerivAt.prodMk hc hu)
  simpa [Function.comp_def,IsBoundedBilinearMap.deriv,add_comm] using hh

/-- Actual real-coordinate derivative of the original complex Einstein Hessian.
Both perturbation slots and the varying background jet are differentiated. -/
theorem secondVariation_hasDerivAt_real {q p : ℝ → JetSpace} {q' p' : JetSpace} {t : ℝ}
    (hq : HasDerivAt q q' t) (hp : HasDerivAt p p' t)
    (hdet : Matrix.det (q t).1 ≠ 0) (i j : Fin d) :
    HasDerivAt (fun x => secondVariation (q x) i j (p x) (p x))
      (thirdVariation (q t) i j q' (p t) (p t)+
        secondVariation (q t) i j p' (p t)+secondVariation (q t) i j (p t) p') t := by
  have hA := contDiffAt_einsteinComponent (n := 3) (q t) hdet i j
  have hD : HasFDerivAt (fun z => secondVariation z i j)
      (thirdVariation (q t) i j) (q t) :=
    (((hA.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
      (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hDr := HasFDerivAt.restrictScalars (𝕜' := ℂ) (E := JetSpace)
    (F := JetSpace →L[ℂ] JetSpace →L[ℂ] ℂ) ℝ hD
  have hB := hDr.comp_hasDerivAt t hq
  have h := clm_apply_real (clm_apply_real hB hp) hp
  convert! h using 1


/-- Hessian symmetry collects the two genuine perturbation-derivative terms. -/
theorem secondVariation_hasDerivAt_real_symmetric {q p : ℝ → JetSpace}
    {q' p' : JetSpace} {t : ℝ} (hq : HasDerivAt q q' t) (hp : HasDerivAt p p' t)
    (hdet : Matrix.det (q t).1 ≠ 0) (i j : Fin d) :
    HasDerivAt (fun x => secondVariation (q x) i j (p x) (p x))
      (thirdVariation (q t) i j (p t) (p t) q'+
        2*secondVariation (q t) i j (p t) p') t := by
  have h := secondVariation_hasDerivAt_real hq hp hdet i j
  rw [thirdVariation_symm_left (q t) hdet i j q' (p t) (p t),
    thirdVariation_symm_right (q t) hdet i j (p t) q' (p t),
    secondVariation_symm (q t) hdet i j p' (p t)] at h
  convert h using 1
  ring

end
end GaloisForLFunctions.HTGeometry.ComplexCoordinateMetricTwoJet
