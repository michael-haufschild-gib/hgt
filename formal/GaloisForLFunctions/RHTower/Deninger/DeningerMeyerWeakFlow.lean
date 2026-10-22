import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerStrongLogFlowDerivative
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# The original Meyer flow has its actual generator in the separated dual

The natural source and literal Poisson quotient are locally convex. Continuous
complex linear functionals separate their cohomology classes. The original
flow is continuous and every such functional reads its derivative as the
original generator, enabling scalar ODE uniqueness on actual source classes.
-/

open Filter Set Topology TopologicalSpace Complex

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

namespace DeningerMeyerNaturalTopology

scoped instance strongLogLocallyConvex : LocallyConvexSpace ℝ DeningerMeyerStrongLogTarget :=
  (deningerMeyerStrongLogSourceContinuousEquiv.toHomeomorph.isInducing.withSeminorms
    DeningerMeyerSource.withSeminorms).toLocallyConvexSpace

scoped instance cohomologyLocallyConvex : LocallyConvexSpace ℝ DeningerMeyerStrongLogCohomology := by
  let N := LinearMap.range deningerMeyerStrongLogSumLM
  have hb := (LocallyConvexSpace.convex_basis_zero ℝ DeningerMeyerStrongLogTarget).map N.mkQ
  have he := N.isOpenMap_mkQ.map_nhds_eq (x := 0) N.mkQL.continuous.continuousAt
  rw [map_zero] at he
  rw [he] at hb
  exact LocallyConvexSpace.ofBasisZero ℝ DeningerMeyerStrongLogCohomology _ _ hb
    fun s hs => hs.2.linear_image (N.mkQ.restrictScalars ℝ)

scoped instance cohomologySeparatingDual : SeparatingDual ℂ DeningerMeyerStrongLogCohomology where
  exists_ne_zero' u hu := by
    obtain ⟨f, hf⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := ℂ) hu
    exact ⟨f, fun h => by simp [h] at hf⟩

end DeningerMeyerNaturalTopology

theorem deningerMeyerStrongLogGenerator_flow (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogGenerator (deningerMeyerStrongLogFlow c g) =
      deningerMeyerStrongLogFlow c (deningerMeyerStrongLogGenerator g) := by
  apply Subtype.ext
  funext t
  change -deriv (fun x : ℝ => g.val (x - c)) t = -deriv g.val (t - c)
  rw [← iteratedDeriv_one, iteratedDeriv_comp_sub_const, iteratedDeriv_one]

theorem deningerMeyerCohomologyGenerator_flow (c : ℝ) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerCohomologyGenerator (deningerMeyerStrongLogCohomologyFlow c u) =
      deningerMeyerStrongLogCohomologyFlow c (deningerMeyerCohomologyGenerator u) := by
  induction u using Submodule.Quotient.induction_on with
  | _ g => simp only [deningerMeyerStrongLogCohomologyFlow_mk,
      deningerMeyerCohomologyGenerator_mk, deningerMeyerStrongLogGenerator_flow]

theorem deningerMeyerStrongLogCohomologyFlow_continuous (c : ℝ) :
    Continuous (deningerMeyerStrongLogCohomologyFlow c) := by
  apply (LinearMap.range deningerMeyerStrongLogSumLM).isQuotientMap_mkQ.continuous_iff.mpr
  exact continuous_quot_mk.comp (deningerMeyerStrongLogFlow_continuous c)

/-- Every continuous source functional differentiates the original source orbit. -/
theorem deningerMeyerStrongLogFlow_hasDerivAt_dual
    (f : DeningerMeyerStrongLogTarget →L[ℂ] ℂ)
    (g : DeningerMeyerStrongLogTarget) (c : ℝ) :
    HasDerivAt (fun t : ℝ => f (deningerMeyerStrongLogFlow t g))
      (f (deningerMeyerStrongLogFlow c (deningerMeyerStrongLogGenerator g))) c := by
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have ht := (f.continuous.tendsto _).comp
    (deningerMeyerStrongLogFlow_tendsto_slope (deningerMeyerStrongLogFlow c g))
  simpa only [Function.comp_def, map_smul, map_sub, smul_eq_mul, Complex.real_smul,
    deningerMeyerStrongLogFlow_add, add_comm c,
    deningerMeyerStrongLogGenerator_flow] using ht

/-- Weak differentiation holds on the literal quotient, with no extra dynamical premise. -/
theorem deningerMeyerStrongLogCohomologyFlow_hasDerivAt_dual
    (f : DeningerMeyerStrongLogCohomology →L[ℂ] ℂ)
    (u : DeningerMeyerStrongLogCohomology) (c : ℝ) :
    HasDerivAt (fun t : ℝ => f (deningerMeyerStrongLogCohomologyFlow t u))
      (f (deningerMeyerStrongLogCohomologyFlow c (deningerMeyerCohomologyGenerator u))) c := by
  induction u using Submodule.Quotient.induction_on with
  | _ g =>
    exact deningerMeyerStrongLogFlow_hasDerivAt_dual
      (f.comp (LinearMap.range deningerMeyerStrongLogSumLM).mkQL) g c

end
end RHTower
