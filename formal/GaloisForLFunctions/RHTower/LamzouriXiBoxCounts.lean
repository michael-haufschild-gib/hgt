import GaloisForLFunctions.HilbertMetric.LamzouriFiniteMultiplicity
import GaloisForLFunctions.RHTower.XiHeightAdaptiveLinearQuadraticCensusCollision

/-!
# Lamzouri bounds for finite right-half Xi boxes

The height-adaptive Xi development already names the linear census `sum m`
and quadratic census `sum m^2` on each finite box.  This module identifies
those with the generic multiplicity mass and collision energy, then transports
Lamzouri's simple-point and distinct-point inequalities to the box census.
-/

open Finset
open scoped BigOperators

namespace RHTower

open GaloisForLFunctions.HilbertMetric

noncomputable section

/-- Xi points in the finite box having analytic multiplicity one. -/
def xiBoxSimpleSupport (T : ℝ) : Finset ℂ :=
  finiteSimpleMultiplicitySupport (boxFinset T)
    (fun z => (analyticOrderAt xi z).toNat)

theorem xiBoxMultiplicityMass_eq (T : ℝ) :
    finiteMultiplicityMass (boxFinset T)
        (fun z => (analyticOrderAt xi z).toNat) = (boxOrderSum T : ℕ) := by
  unfold finiteMultiplicityMass boxOrderSum
  norm_cast

theorem xiBoxCollisionMass_eq (T : ℝ) :
    finiteMultiplicityCollisionMass (boxFinset T)
        (fun z => (analyticOrderAt xi z).toNat) = (boxSquareOrderSum T : ℕ) := by
  unfold finiteMultiplicityCollisionMass boxSquareOrderSum
  norm_cast

/-- Simple Xi support is controlled by the linear and quadratic box censuses. -/
theorem xiBoxSimpleSupport_lower (T : ℝ) :
    2 * (boxOrderSum T : ℕ) - (boxSquareOrderSum T : ℕ) ≤
      ((xiBoxSimpleSupport T).card : ℝ) := by
  have h := finiteSimpleMultiplicitySupport_lower (boxFinset T)
    (fun z => (analyticOrderAt xi z).toNat)
  rw [xiBoxMultiplicityMass_eq, xiBoxCollisionMass_eq] at h
  exact h

/-- Distinct Xi support is controlled by the same two box censuses. -/
theorem xiBoxDistinctSupport_lower (T : ℝ) :
    (3 / 2 : ℝ) * (boxOrderSum T : ℕ) -
        (1 / 2 : ℝ) * (boxSquareOrderSum T : ℕ) ≤
      ((boxFinset T).card : ℝ) := by
  have h := finitePositiveMultiplicitySupport_lower (boxFinset T)
    (fun z => (analyticOrderAt xi z).toNat)
  have hs : finitePositiveMultiplicitySupport (boxFinset T)
      (fun z => (analyticOrderAt xi z).toNat) = boxFinset T := by
    unfold finitePositiveMultiplicitySupport
    rw [Finset.filter_eq_self]
    intro z hz
    exact Nat.pos_of_ne_zero (xi_order_toNat_ne_zero (mem_boxFinset.mp hz).2)
  rw [hs, xiBoxMultiplicityMass_eq, xiBoxCollisionMass_eq] at h
  exact h

end

end RHTower
