import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalScalarLift

/-!
Exact test unfolding identifies the global distribution equation with the actual lifted scalar response.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section

/-- The original Hilbert pairing unfolds to the actual globally modular L² lift. -/
theorem PlanarChartTest.lift_pairing (g : PlanarChartTest) (u : Space) :
    inner ℂ (embedding g.toChartTest.energyTest) u =
      ∫ z : UpperHalfPlane, conj (g.field z)*globalLift u z := by
  rw [g.toChartTest.scalar_pairing]
  have he : (∫ z : UpperHalfPlane, conj (periodize g.toChartTest.field z)*u z ∂measure) =
      ∫ z : UpperHalfPlane, conj (periodize g.toChartTest.field z)*globalLift u z ∂measure := by
    apply integral_congr_ae
    filter_upwards [globalLift_ae_eq u] with z hz
    rw [hz]
  rw [he]
  simpa only [periodize,Complex.conj_tsum,PlanarChartTest.toChartTest,CompactChartTest.ofPlanar,
    PlanarChartTest.conjugate] using
    compact_test_modular_pairing_unfold g.conjugate.toChartTest (globalLift u)
      (globalLift_locallyIntegrable u) (globalLift_invariant u)

/-- The actual lifted response satisfies its full half-plane distributional equation. -/
theorem full_response_lifted_equation (q : XiZeroCopy) (minusBranch : Bool) (g : PlanarChartTest) :
    (∫ z : UpperHalfPlane, conj (g.laplaceTest.field z)*globalLift
      (embedding (weakResponse q minusBranch)) z) -
      parameter q minusBranch*(∫ z : UpperHalfPlane, conj (g.field z)*globalLift
        (embedding (weakResponse q minusBranch)) z) =
      ∫ z : UpperHalfPlane, conj (g.field z)*globalLift (forcingVector q minusBranch) z := by
  have he := full_response_global_distribution_equation q minusBranch g
  rwa [PlanarChartTest.laplaceVector,g.laplaceTest.lift_pairing,g.lift_pairing,g.lift_pairing] at he

private theorem PlanarChartTest.derivative_conjugate (g : PlanarChartTest) (v : ℂ) :
    (g.conjugate.derivative v).field = (g.derivative v).conjugate.field := by
  funext z
  exact g.conjugate_deriv v z

/-- Complex conjugation commutes with the literal hyperbolic test Laplacian. -/
theorem PlanarChartTest.laplace_conjugate (g : PlanarChartTest) (z : ℂ) :
    g.conjugate.laplaceTest.field z = conj (g.laplaceTest.field z) := by
  have hd (v : ℂ) :
      fderiv ℝ (g.conjugate.derivative v).field z v =
        conj (fderiv ℝ (g.derivative v).field z v) := by
    rw [g.derivative_conjugate]
    exact (g.derivative v).conjugate_deriv v z
  change (∑ i : Fin 2, (z.im : ℂ)^(2 : ℕ)*fderiv ℝ (g.conjugate.derivative (direction i)).field z (direction i)) =
    conj (∑ i : Fin 2, (z.im : ℂ)^(2 : ℕ)*fderiv ℝ (g.derivative (direction i)).field z (direction i))
  simp only [hd,map_sum,map_mul,map_pow,Complex.conj_ofReal]

/-- The full lifted response equation with ordinary, unconjugated test functions. -/
theorem full_response_lifted_test_equation (q : XiZeroCopy) (minusBranch : Bool) (g : PlanarChartTest) :
    (∫ z : UpperHalfPlane, g.laplaceTest.field z*globalLift
      (embedding (weakResponse q minusBranch)) z) -
      parameter q minusBranch*(∫ z : UpperHalfPlane, g.field z*globalLift
        (embedding (weakResponse q minusBranch)) z) =
      ∫ z : UpperHalfPlane, g.field z*globalLift (forcingVector q minusBranch) z := by
  have he := full_response_lifted_equation q minusBranch g.conjugate
  simp_rw [g.laplace_conjugate] at he
  simpa only [PlanarChartTest.conjugate,map_star,starRingEnd_apply,star_star] using he

end
end RHTower.D4BMModularCore
