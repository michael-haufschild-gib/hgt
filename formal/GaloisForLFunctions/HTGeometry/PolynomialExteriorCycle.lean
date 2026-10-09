import GaloisForLFunctions.HTGeometry.PolynomialExteriorRootLift
import GaloisForLFunctions.HTGeometry.PrimitiveCoordinateCycle
import Mathlib.RingTheory.RootsOfUnity.Complex

open Polynomial Set Topology
open scoped unitInterval
namespace GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
noncomputable section

/-- Actual exterior monodromy admits an injective primitive-root coordinate on its whole fiber. -/
theorem PolynomialExteriorPowerChart.primitive_coordinate {n : ℕ} {v : Parameter n}
    (D : PolynomialExteriorPowerChart v) :
    ∃ u : RootFiber v (0 + ((D.radius ^ (n + 2))⁻¹ : ℝ)) → ℂ,
      Function.Injective u ∧ (∀ z, u z ≠ 0) ∧
      (∀ a b, u a ^ (n + 2) = u b ^ (n + 2)) ∧
      ∀ z, u (rootLoopTransport v (positiveCirclePath 0 (D.radius ^ (n + 2))⁻¹)
          D.circle_avoid z) =
        (Complex.exp (2 * Real.pi * Complex.I / ((n + 2 : ℕ) : ℂ)))⁻¹ * u z := by
  let R := (D.radius ^ (n + 2))⁻¹
  have hz : ∀ z : RootFiber v (0 + (R : ℂ)),
      (additivePolynomial v).eval (z : ℂ) = positiveCirclePath 0 R 0 :=
    fun z => z.property.trans (positiveCirclePath 0 R).source.symm
  have hpow : ∀ z : RootFiber v (0 + (R : ℂ)),
      D.chart (z : ℂ)⁻¹ ^ (n + 2) = (R : ℂ)⁻¹ := by
    intro z
    have hout := D.roots_outside 0 z (hz z)
    simpa only [inv_inv, z.property, zero_add] using
      D.reciprocal_power (z : ℂ)⁻¹ hout.2 (inv_ne_zero hout.1)
  refine ⟨fun z => D.chart (z : ℂ)⁻¹, ?_, ?_, ?_, D.rootLoop_coordinate⟩
  · intro a b hab
    apply Subtype.ext
    apply inv_injective
    exact D.chart.injOn (D.roots_outside 0 a (hz a)).2
      (D.roots_outside 0 b (hz b)).2 hab
  · exact fun z => D.coordinate_ne_zero (hz z)
  · exact fun a b => (hpow a).trans (hpow b).symm

/-- A positive exterior circle is one full cycle on the actual polynomial root fiber. -/
theorem PolynomialExteriorPowerChart.rootLoop_isCycleOn {n : ℕ} {v : Parameter n}
    (D : PolynomialExteriorPowerChart v) :
    (rootLoopTransport v (positiveCirclePath 0 (D.radius ^ (n + 2))⁻¹)
      D.circle_avoid).IsCycleOn univ := by
  obtain ⟨u, hu, hzero, hpow, hstep⟩ := D.primitive_coordinate
  exact isCycleOn_of_primitive_coordinate _ u hu hzero (by omega : 0 < n + 2)
    (Complex.isPrimitiveRoot_exp (n + 2) (by omega)).inv hpow hstep

/-- The actual exterior fiber has exactly degree-many sheets, derived from its coordinate orbit. -/
theorem PolynomialExteriorPowerChart.natCard_rootFiber {n : ℕ} {v : Parameter n}
    (D : PolynomialExteriorPowerChart v) :
    Nat.card (RootFiber v (0 + ((D.radius ^ (n + 2))⁻¹ : ℝ))) = n + 2 := by
  obtain ⟨u, hu, hzero, hpow, hstep⟩ := D.primitive_coordinate
  obtain ⟨z, hz⟩ := IsAlgClosed.eval_surjective
    (p := additivePolynomial v) (by rw [natDegree_additivePolynomial]; omega)
    (0 + (((D.radius ^ (n + 2))⁻¹ : ℝ) : ℂ))
  exact natCard_eq_of_primitive_coordinate _ u hu hzero (by omega : 0 < n + 2)
    (Complex.isPrimitiveRoot_exp (n + 2) (by omega)).inv hpow hstep ⟨z, hz⟩

end
end GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap
