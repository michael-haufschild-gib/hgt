import GaloisForLFunctions.HTGeometry.AnalyticPowerCoordinate
import GaloisForLFunctions.Bottcher.ConnectedRepellingRootDefect

open Polynomial Filter Topology Set
namespace GaloisForLFunctions.HTGeometry

/-- The actual polynomial germ has a power coordinate of exactly its algebraic root multiplicity. -/
theorem exists_polynomial_power_coordinate {P : ℂ[X]} (hP : P ≠ 0)
    {a : ℂ} (ha : P.IsRoot a) {U : Set ℂ} (hU : U ∈ 𝓝 a) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      a ∈ e.source ∧ e.source ⊆ U ∧ e a = 0 ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ z ∈ e.source, deriv e z ≠ 0) ∧
      ∀ z ∈ e.source, P.eval z = (e z) ^ P.rootMultiplicity a := by
  have han : AnalyticAt ℂ (fun z : ℂ => P.eval z) a := by
    simpa using (analyticAt_id : AnalyticAt ℂ (fun z : ℂ => z) a).aeval_polynomial P
  exact exists_analytic_power_coordinate han ((rootMultiplicity_pos hP).mpr ha)
    (Bottcher.analyticOrderAt_polynomial_eval_eq_rootMultiplicity hP a) hU

end GaloisForLFunctions.HTGeometry
