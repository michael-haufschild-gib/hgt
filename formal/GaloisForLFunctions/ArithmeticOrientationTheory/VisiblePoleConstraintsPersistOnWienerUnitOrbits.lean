import GaloisForLFunctions.ArithmeticOrientationTheory.PaidKernelsCoverVisibleTranslatedZeroOrders
import GaloisForLFunctions.ArithmeticOrientationTheory.CriticalBoundaryPolesObstructPaidKernels
import GaloisForLFunctions.ArithmeticOrientationTheory.AnIndexFormulaForTheActualReceiver

/-!
# Visible pole constraints persist on Wiener unit orbits

Wiener units preserve the actual paid ideal and its obstruction hull. The
interior jet constraints and critical-boundary obstruction therefore hold
throughout the Möbius unit orbit, including the damped Liouville source.
-/

section

noncomputable section
set_option autoImplicit false
open Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory
open TransHorizonIncidenceMechanics WienerAlgebraAt BezoutValuationIncidence

/-- Every source in the actual Möbius Wiener-unit orbit has the same visible interior jet constraints. -/
theorem paid_unitOrbit_kernel_jets_vanish_below_visible_order
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|)
    (horbit : WienerUnitOrbit (pmPowerDampedRealWeight ε) c)
    (k : WienerAlgebraAt (1 / 2)) (hk : k ∈ paidIdeal c hc)
    {ρ : ℂ} (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1)
    {N : ℕ} (hN : (N : ℕ∞) ≤ visibleTranslatedZetaOrder ε ρ) :
    ∀ i < N, iteratedDeriv i (LSeries (⇑k.toFn)) (ρ - ε) = 0 := by
  apply paid_kernel_jets_vanish_below_visible_order hε hε2 k ?_ hρ hρ1 hN
  rw [paidIdeal_eq_of_wienerUnitOrbit (summable_abs_moebius_div hε) hc horbit]
  exact hk

/-- The actual Möbius unit orbit retains all visible critical-boundary obstruction points. -/
theorem mem_obstructionHull_unitOrbit_of_critical_boundary_order_loss
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {c : ℕ → ℝ} (hc : Summable fun d : ℕ => |c d / d|)
    (horbit : WienerUnitOrbit (pmPowerDampedRealWeight ε) c)
    {ρ : ℂ} (hρ : ρ.re = 1 / 2 + ε)
    (hloss : analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ) :
    halfPlanePoint (1 / 2) (ρ - ε) (by simp only [sub_re, ofReal_re, hρ]; linarith) ∈
      obstructionHull c hc := by
  rw [← obstructionHull_eq_of_wienerUnitOrbit (summable_abs_moebius_div hε) hc horbit]
  exact mem_obstructionHull_moebius_of_critical_boundary_order_loss hε hε2 hρ hloss

/-- Paid Liouville kernels obey all interior jet conditions imposed by visible translated zeta order. -/
theorem paid_liouville_kernel_jets_vanish_below_visible_order
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (k : WienerAlgebraAt (1 / 2))
    (hk : k ∈ paidIdeal (dampedSignWeight RHTower.liouvilleR ε) (summable_abs_dampedLiouville_div hε))
    {ρ : ℂ} (hρ : 1 / 2 + ε < ρ.re) (hρ1 : ρ.re < 1)
    {N : ℕ} (hN : (N : ℕ∞) ≤ visibleTranslatedZetaOrder ε ρ) :
    ∀ i < N, iteratedDeriv i (LSeries (⇑k.toFn)) (ρ - ε) = 0 :=
  paid_unitOrbit_kernel_jets_vanish_below_visible_order hε hε2
    (summable_abs_dampedLiouville_div hε) (wienerUnitOrbit_moebius_liouville hε)
    k hk hρ hρ1 hN

/-- Liouville shares the Möbius critical-boundary obstruction, including partial zero cancellation. -/
theorem mem_obstructionHull_liouville_of_critical_boundary_order_loss
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {ρ : ℂ} (hρ : ρ.re = 1 / 2 + ε)
    (hloss : analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ) :
    halfPlanePoint (1 / 2) (ρ - ε) (by simp only [sub_re, ofReal_re, hρ]; linarith) ∈
      obstructionHull (dampedSignWeight RHTower.liouvilleR ε) (summable_abs_dampedLiouville_div hε) :=
  mem_obstructionHull_unitOrbit_of_critical_boundary_order_loss hε hε2
    (summable_abs_dampedLiouville_div hε) (wienerUnitOrbit_moebius_liouville hε) hρ hloss

/-- A visible critical-boundary pole excludes payment of the actual Liouville receiver. -/
theorem not_receiverBounded_liouville_of_critical_boundary_order_loss
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {ρ : ℂ} (hρ : ρ.re = 1 / 2 + ε)
    (hloss : analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ) :
    ¬ ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε) :=
  (obstructionHull_nonempty_iff _ _).1
    ⟨_, mem_obstructionHull_liouville_of_critical_boundary_order_loss hε hε2 hρ hloss⟩

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.paid_liouville_kernel_jets_vanish_below_visible_order
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.not_receiverBounded_liouville_of_critical_boundary_order_loss
end
end
