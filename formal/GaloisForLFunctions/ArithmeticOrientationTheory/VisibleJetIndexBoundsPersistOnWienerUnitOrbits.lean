import GaloisForLFunctions.ArithmeticOrientationTheory.AnIndexFormulaForTheActualReceiver
import GaloisForLFunctions.ArithmeticOrientationTheory.VisibleInteriorAndBoundaryPolesBoundThePaidIndex

/-!
# Visible jet index bounds persist on Wiener unit orbits

Equality of paid ideals under Wiener unit convolution transports the
combined interior-multiplicity and boundary-value lower bound, in
particular from the damped Möbius source to the damped Liouville source.
-/

noncomputable section
set_option autoImplicit false
open Finset

namespace GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt TransHorizonIncidenceMechanics BezoutValuationIncidence

/-- Wiener-unit transport preserves the combined interior-jet and boundary-value index bound. -/
theorem sum_visible_orders_add_boundary_card_le_paid_unitOrbit_index
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|)
    (horbit : WienerUnitOrbit (pmPowerDampedRealWeight ε) c)
    (Z B : Finset ℂ) (hZ : ∀ ρ ∈ Z, 1 / 2 + ε < ρ.re ∧ ρ.re < 1)
    (hB : ∀ ρ ∈ B, ρ.re = 1 / 2 + ε ∧
      analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ)
    (m : Z → ℕ) (hm : ∀ ρ : Z, (m ρ : ℕ∞) ≤ visibleTranslatedZetaOrder ε ρ) :
    (((∑ ρ : Z, m ρ) + B.card : ℕ) : Cardinal) ≤
      Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ paidIdeal c hc) := by
  rw [← paidIdeal_eq_of_wienerUnitOrbit (summable_abs_moebius_div hε) hc horbit]
  exact sum_visible_orders_add_boundary_card_le_paid_index hε hε2 Z B hZ hB m hm

/-- The damped Liouville paid quotient retains all visible Möbius interior multiplicities
and distinct critical-boundary obstructions. -/
theorem sum_visible_orders_add_boundary_card_le_paid_liouville_index
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (Z B : Finset ℂ) (hZ : ∀ ρ ∈ Z, 1 / 2 + ε < ρ.re ∧ ρ.re < 1)
    (hB : ∀ ρ ∈ B, ρ.re = 1 / 2 + ε ∧
      analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ)
    (m : Z → ℕ) (hm : ∀ ρ : Z, (m ρ : ℕ∞) ≤ visibleTranslatedZetaOrder ε ρ) :
    (((∑ ρ : Z, m ρ) + B.card : ℕ) : Cardinal) ≤
      Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
        paidIdeal (dampedSignWeight RHTower.liouvilleR ε) (summable_abs_dampedLiouville_div hε)) :=
  sum_visible_orders_add_boundary_card_le_paid_unitOrbit_index hε hε2
    (summable_abs_dampedLiouville_div hε) (wienerUnitOrbit_moebius_liouville hε)
    Z B hZ hB m hm

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.sum_visible_orders_add_boundary_card_le_paid_unitOrbit_index
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.sum_visible_orders_add_boundary_card_le_paid_liouville_index
end
