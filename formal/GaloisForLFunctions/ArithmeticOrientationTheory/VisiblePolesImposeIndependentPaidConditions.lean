import GaloisForLFunctions.ArithmeticOrientationTheory.TheMoebiusReceiverCountsItsOffLineZeros
import GaloisForLFunctions.ArithmeticOrientationTheory.PaidKernelsCoverVisibleTranslatedZeroOrders
import GaloisForLFunctions.ArithmeticOrientationTheory.CriticalBoundaryPolesObstructPaidKernels

/-!
# Visible poles impose independent paid conditions

Distinct closed-half-plane points define separated Wiener characters.
Each visible translated pole therefore contributes one independent
condition on the paid ideal, including critical-boundary poles.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology Complex

namespace GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt TransHorizonIncidenceMechanics BezoutValuationIncidence

/-- Distinct points of the closed critical half-plane give distinct Wiener characters. -/
theorem halfPlane_characters_separated {s t : ℂ}
    (hs : (1 / 2 : ℝ) ≤ s.re) (ht : (1 / 2 : ℝ) ≤ t.re) (hne : s ≠ t) :
    ∃ a : WienerAlgebraAt (1 / 2),
      WienerAlgebraAt.bohrCharacter (1 / 2) (halfPlanePoint (1 / 2) s hs) a ≠
        WienerAlgebraAt.bohrCharacter (1 / 2) (halfPlanePoint (1 / 2) t ht) a := by
  have hval (n : ℕ) (hn : n ≠ 0) (z : ℂ) (hz : (1 / 2 : ℝ) ≤ z.re) :
      WienerAlgebraAt.bohrCharacter (1 / 2) (halfPlanePoint (1 / 2) z hz) (pointMass n) =
        (halfPlanePoint (1 / 2) z hz).ω n / (n : ℂ) ^ ((1 / 2 : ℝ) : ℂ) := by
    rw [bohrCharacter_apply, toFn_pointMass, bohrEval_pointMass hn]
  have hn0 (n : ℕ) (hn : n ≠ 0) : (n : ℂ) ^ ((1 / 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h => hn (by exact_mod_cast h.1)
  by_contra hall
  push Not at hall
  have h2 := hall (pointMass 2)
  have h3 := hall (pointMass 3)
  rw [hval 2 two_ne_zero, hval 2 two_ne_zero, div_left_inj' (hn0 2 two_ne_zero)] at h2
  rw [hval 3 three_ne_zero, hval 3 three_ne_zero, div_left_inj' (hn0 3 three_ne_zero)] at h3
  exact hne (eq_of_halfPlanePoint_two_three hs ht h2 h3)

/-- Every positive visible order contributes a paid-ideal obstruction, including the boundary. -/
theorem mem_obstructionHull_moebius_of_closed_halfPlane_order_loss
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {ρ : ℂ}
    (hρ : 1 / 2 + ε ≤ ρ.re) (hρ1 : ρ.re < 1)
    (hloss : analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ) :
    halfPlanePoint (1 / 2) (ρ - ε) (by simp only [sub_re, ofReal_re]; linarith only [hρ]) ∈
      obstructionHull (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε) := by
  rcases hρ.eq_or_lt with h | h
  · exact mem_obstructionHull_moebius_of_critical_boundary_order_loss hε hε2 h.symm hloss
  · exact mem_obstructionHull_moebius_of_strict_order_loss hε hε2 h hρ1 hloss

/-- Visible interior and critical-boundary poles jointly bound the actual paid quotient index. -/
theorem card_le_rank_quotient_paidIdeal_moebius_visible
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (Z : Finset ℂ) (hZ : ∀ ρ ∈ Z,
      1 / 2 + ε ≤ ρ.re ∧ ρ.re < 1 ∧
        analyticOrderAt riemannZeta (ρ - ε) < analyticOrderAt riemannZeta ρ) :
    (Z.card : Cardinal) ≤ Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸
      paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) := by
  classical
  have hre (ρ : Z) : (1 / 2 : ℝ) ≤ ((ρ : ℂ) - ε).re := by
    have h := (hZ ρ ρ.property).1
    simp only [sub_re, ofReal_re]
    linarith only [h]
  let χ (ρ : Z) : WienerAlgebraAt (1 / 2) →ₐ[ℂ] ℂ :=
    WienerAlgebraAt.bohrCharacter (1 / 2) (halfPlanePoint (1 / 2) ((ρ : ℂ) - ε) (hre ρ))
  have hsep (ρ ρ' : Z) (hne : ρ ≠ ρ') : ∃ a, χ ρ a ≠ χ ρ' a :=
    halfPlane_characters_separated (hre ρ) (hre ρ')
      (fun h => hne (Subtype.ext (sub_left_inj.mp h)))
  have h := card_le_rank_quotient_of_separated χ hsep
    (paidIdeal (pmPowerDampedRealWeight ε) (summable_abs_moebius_div hε)) (fun k hk ρ => by
      obtain ⟨h1, h2, h3⟩ := hZ ρ ρ.property
      exact mem_obstructionHull_moebius_of_closed_halfPlane_order_loss hε hε2 h1 h2 h3 k hk)
  simpa only [Fintype.card_coe] using h

end GaloisForLFunctions.ArithmeticOrientationTheory

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.halfPlane_characters_separated
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.mem_obstructionHull_moebius_of_closed_halfPlane_order_loss
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.card_le_rank_quotient_paidIdeal_moebius_visible
end
