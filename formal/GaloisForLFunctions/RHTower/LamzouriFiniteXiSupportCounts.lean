import GaloisForLFunctions.HilbertMetric.LamzouriFiniteMultiplicity
import GaloisForLFunctions.RHTower.RiemannVonMangoldt

/-!
# Lamzouri bounds for finite completed-zeta divisor packets

The completed-zeta corpus exposes the genuine analytic multiplicity of every
divisor support point.  This module applies the finite diagonal inequalities
to arbitrary finite support packets and to the canonical positive-height
windows used by the Riemann--von Mangoldt development.
-/

open Finset
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Total analytic multiplicity carried by a finite Xi-divisor packet. -/
def xiFiniteSupportMultiplicityMass (S : Finset XiDivisorSupport) : ℝ :=
  finiteMultiplicityMass S xiSupportMultiplicity

/-- Diagonal collision energy of a finite Xi-divisor packet. -/
def xiFiniteSupportCollisionMass (S : Finset XiDivisorSupport) : ℝ :=
  finiteMultiplicityCollisionMass S xiSupportMultiplicity

/-- Points of a finite Xi-divisor packet having analytic multiplicity one. -/
def xiFiniteSimpleSupport (S : Finset XiDivisorSupport) : Finset XiDivisorSupport :=
  finiteSimpleMultiplicitySupport S xiSupportMultiplicity

/-- Montgomery--Lamzouri simple-point inequality for every finite Xi packet. -/
theorem xiFiniteSimpleSupport_lower (S : Finset XiDivisorSupport) :
    2 * xiFiniteSupportMultiplicityMass S - xiFiniteSupportCollisionMass S ≤
      ((xiFiniteSimpleSupport S).card : ℝ) := by
  exact finiteSimpleMultiplicitySupport_lower S xiSupportMultiplicity

/-- Lamzouri's distinct-point inequality for every finite Xi packet. -/
theorem xiFiniteDistinctSupport_lower (S : Finset XiDivisorSupport) :
    (3 / 2 : ℝ) * xiFiniteSupportMultiplicityMass S -
        (1 / 2 : ℝ) * xiFiniteSupportCollisionMass S ≤ (S.card : ℝ) := by
  have h := finitePositiveMultiplicitySupport_lower S xiSupportMultiplicity
  have hs : finitePositiveMultiplicitySupport S xiSupportMultiplicity = S := by
    unfold finitePositiveMultiplicitySupport
    rw [Finset.filter_eq_self]
    intro rho _
    exact xiSupportMultiplicity_pos rho
  simpa only [xiFiniteSupportMultiplicityMass, xiFiniteSupportCollisionMass, hs] using h

/-- Analytic multiplicity mass never exceeds its diagonal collision energy. -/
theorem xiFiniteSupportMass_le_collisionMass (S : Finset XiDivisorSupport) :
    xiFiniteSupportMultiplicityMass S ≤ xiFiniteSupportCollisionMass S := by
  exact finiteMultiplicityMass_le_collisionMass S xiSupportMultiplicity

/-- Total analytic multiplicity in the canonical positive-height Xi window. -/
def xiPositiveWindowMultiplicityMass (T : ℝ) : ℝ :=
  xiFiniteSupportMultiplicityMass (xiSupportsPos T)

/-- Diagonal collision energy in the canonical positive-height Xi window. -/
def xiPositiveWindowCollisionMass (T : ℝ) : ℝ :=
  xiFiniteSupportCollisionMass (xiSupportsPos T)

/-- Simple divisor support in the canonical positive-height Xi window. -/
def xiPositiveWindowSimpleSupport (T : ℝ) : Finset XiDivisorSupport :=
  xiFiniteSimpleSupport (xiSupportsPos T)

theorem xiPositiveWindowSimpleSupport_lower (T : ℝ) :
    2 * xiPositiveWindowMultiplicityMass T - xiPositiveWindowCollisionMass T ≤
      ((xiPositiveWindowSimpleSupport T).card : ℝ) := by
  exact xiFiniteSimpleSupport_lower (xiSupportsPos T)

theorem xiPositiveWindowDistinctSupport_lower (T : ℝ) :
    (3 / 2 : ℝ) * xiPositiveWindowMultiplicityMass T -
        (1 / 2 : ℝ) * xiPositiveWindowCollisionMass T ≤
      ((xiSupportsPos T).card : ℝ) := by
  exact xiFiniteDistinctSupport_lower (xiSupportsPos T)

theorem xiPositiveWindowMass_le_collisionMass (T : ℝ) :
    xiPositiveWindowMultiplicityMass T ≤ xiPositiveWindowCollisionMass T := by
  exact xiFiniteSupportMass_le_collisionMass (xiSupportsPos T)

end

end RHTower
