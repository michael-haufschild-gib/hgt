import GaloisForLFunctions.HTGeometry.PolynomialPowerCoordinate
import Mathlib.Topology.Algebra.Polynomial

open Polynomial Filter Topology Set Metric
namespace GaloisForLFunctions.HTGeometry

/-- Local power charts control every nearby root, with a common coordinate disk. -/
theorem exists_polynomial_fiber_power_charts (P : ℂ[X]) (c : ℂ) (hP : P - C c ≠ 0) :
    ∃ e : {a : ℂ // P.eval a = c} → OpenPartialHomeomorph ℂ ℂ,
      (∀ a, (a : ℂ) ∈ (e a).source ∧ e a a = 0 ∧
        AnalyticOnNhd ℂ (e a) (e a).source ∧
        AnalyticOnNhd ℂ (e a).symm (e a).target ∧
        (∀ z ∈ (e a).source, deriv (e a) z ≠ 0) ∧
        ∀ z ∈ (e a).source,
          P.eval z = c + (e a z) ^ (P - C c).rootMultiplicity (a : ℂ)) ∧
      ∃ η δ : ℝ, 0 < η ∧ 0 < δ ∧
        (∀ a, ball (0 : ℂ) η ⊆ (e a).target) ∧
        ∀ w ∈ ball c δ, ∀ z : ℂ, P.eval z = w → ∃ a, z ∈ (e a).source := by
  classical
  let A := {a : ℂ // P.eval a = c}
  have hfinite : {a : ℂ | P.eval a = c}.Finite := by
    simpa only [IsRoot, eval_sub, eval_C, sub_eq_zero] using
      (finite_setOf_isRoot hP)
  letI : Fintype A := hfinite.fintype
  have hcharts : ∀ a : A, ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (a : ℂ) ∈ e.source ∧ e a = 0 ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ z ∈ e.source, deriv e z ≠ 0) ∧
      ∀ z ∈ e.source, P.eval z = c + (e z) ^ (P - C c).rootMultiplicity (a : ℂ) := by
    intro a
    have ha : (P - C c).IsRoot a := by
      simpa only [IsRoot, eval_sub, eval_C, sub_eq_zero] using a.property
    obtain ⟨e, he, _, he0, hean, heinv, hed, hepow⟩ :=
      exists_polynomial_power_coordinate hP ha (U := univ) (by simp)
    refine ⟨e, he, he0, hean, heinv, hed, ?_⟩
    intro z hz
    have hp := hepow z hz
    simp only [eval_sub, eval_C] at hp
    exact (sub_eq_iff_eq_add.mp hp).trans (add_comm _ _)
  choose e hsource hzero han hinv hder hpow using hcharts
  have htarg : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ a : A, z ∈ (e a).target := by
    apply eventually_all.mpr
    intro a
    exact (e a).open_target.mem_nhds (hzero a ▸ (e a).map_source (hsource a))
  obtain ⟨η, hη, hηball⟩ := Metric.eventually_nhds_iff.mp htarg
  have hnear : ∀ᶠ w in 𝓝 c, ∀ z : ℂ, P.eval z = w → ∃ a : A, z ∈ (e a).source := by
    apply P.isClosedMap_eval.eventually_nhds_fiber c
    intro a ha
    let a' : A := ⟨a, ha⟩
    filter_upwards [(e a').open_source.mem_nhds (hsource a')] with z hz
    exact ⟨a', hz⟩
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨e, fun a => ⟨hsource a, hzero a, han a, hinv a, hder a, hpow a⟩,
    η, δ, hη, hδ, ?_, ?_⟩
  · intro a z hz
    exact hηball hz a
  · intro w hw z hz
    exact hδball hw z hz

end GaloisForLFunctions.HTGeometry
