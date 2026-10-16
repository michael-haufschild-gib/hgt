import GaloisForLFunctions.RHTower.PaperThetaNativeQuantileDomain
import GaloisForLFunctions.RHTower.ThetaQuantileArithmeticForm

/-! # Native inhomogeneous solving in the complete arithmetic domain

RN's whole BV resolvent produces literal compact AC solutions. CHMD's BV
admission places each real component in the full mass-and-jump graph; the
complete Gamma, prime-power, negative mass and polar expression is retained.
-/

noncomputable section
open MeasureTheory Set Filter Topology Zeta23

namespace RHTower.PaperThetaEndpoint
open CHMDDoobGraph

def nativeWeilGraph (f : ThetaNativeDomain) (L : ℂ →L[ℝ] ℝ) : SourceGraph :=
  bvLift (fun x => L (f x)) (L.lipschitz.comp_boundedVariationOn f.bv)

theorem nativeWeilGraph_source (f : ThetaNativeDomain) (L : ℂ →L[ℝ] ℝ) :
    (nativeWeilGraph f L).val.fst =ᵐ[massMeasure] (fun x => L (f x)) :=
  bvLift_source _ _

/-- Exact arithmetic value, with all signed terms and both polar moments. -/
theorem nativeWeilGraph_energy (f : ThetaNativeDomain) (L : ℂ →L[ℝ] ℝ) :
    sourceWeilEnergy (nativeWeilGraph f L) =
      phiDoobArchJumpEnergy (fun x => L (f x)) +
      (∑' n, ∫ x, phiDoobPrimeJump (fun y => L (f y)) n x) -
      phiDoobCoshMass (fun x => L (f x)^2) +
      2*phiDoobCoshMass (fun x => L (f x))^2 -
      2*phiDoobSinhMass (fun x => L (f x))^2 :=
  sourceWeilEnergy_bvLift _ _

/-- The singular coordinate change preserves the value of every forced solution. -/
theorem nativeWeilGraph_quantile (f : ThetaNativeDomain) (L : ℂ →L[ℝ] ℝ) :
    sourceWeilEnergy (nativeWeilGraph f L) =
      ThetaQuantileArithmetic.weilEnergy (fun t => L (nativeClosedQuantile f t)) := by
  rw [nativeWeilGraph, ← ThetaQuantileArithmetic.weilEnergy_pull]
  apply ThetaQuantileArithmetic.weilEnergy_congr
  intro t ht
  exact congrArg L (nativeClosedQuantile_interior f ht).symm

/-- These arithmetic values are limits of the original compact smooth Weil tests. -/
theorem nativeWeilGraph_compact_approximation (f : ThetaNativeDomain) (L : ℂ →L[ℝ] ℝ) :
    ∃ (v : ℕ → ℝ → ℝ) (hv : ∀ n, ContDiff ℝ 2 (v n))
      (hc : ∀ n, HasCompactSupport (v n)),
      Tendsto (fun n => compactLift (v n) (hv n) (hc n)) atTop (𝓝 (nativeWeilGraph f L)) ∧
      Tendsto (fun n =>
        (weilFullFunctional (fun k => (ArithmeticFunction.vonMangoldt k : ℝ))
          (EF.weilTest (fun x => (phiDoobTest (v n) x : ℂ))
            (fun x => (phiDoobTest (v n) x : ℂ)))).re)
        atTop (𝓝 (sourceWeilEnergy (nativeWeilGraph f L))) :=
  exists_compact_Weil_approximation _

/-- Arbitrary continuous BV forcing, actual compact AC solution, whole-domain uniqueness. -/
theorem nativeThetaImaginaryEquation_existsUnique_full_source
    (r : ℝˣ) (g : ThetaContinuousBV) :
    ∃! f : ThetaNativeDomain,
      (∀ x, thetaSpatialAction f x-(Complex.I*((r : ℝ) : ℂ))*f x = g x) ∧
      AbsolutelyContinuousOnInterval (nativeClosedQuantile f) 0 1 ∧
      (∀ L : ℂ →L[ℝ] ℝ,
        (nativeWeilGraph f L).val.fst =ᵐ[massMeasure] (fun x => L (f x)) ∧
        sourceWeilEnergy (nativeWeilGraph f L) =
          ThetaQuantileArithmetic.weilEnergy (fun t => L (nativeClosedQuantile f t))) := by
  obtain ⟨f, hf, hu⟩ := nativeThetaImaginaryEquation_existsUnique r g
  refine ⟨f, ⟨hf, absolutelyContinuousOnInterval_nativeClosedQuantile f,
    fun L => ⟨nativeWeilGraph_source f L, nativeWeilGraph_quantile f L⟩⟩, ?_⟩
  exact fun h hh => hu h hh.1

end RHTower.PaperThetaEndpoint
