import GaloisForLFunctions.RHTower.CentralReciprocalMoments

/-!
# Functional-equation folding in the reciprocal-square coordinate

The centered reciprocal coordinate `-((rho - 1/2)⁻¹)^2` identifies the functional-equation
pair `rho` and `1-rho`.  The completed xi divisor has equal analytic order at those two points,
so the folded atom carries twice the original multiplicity.  Conjugation gives the second atom
of an off-axis quartet, again with doubled multiplicity, while a critical-line pair folds to the
positive real atom `gamma⁻²`.
-/

open Complex MeromorphicOn

namespace RHTower

noncomputable section

/-- The functional-equation pair has one reciprocal atom, equal analytic orders, and even total
multiplicity. -/
theorem xiReciprocalFold_pair (rho : ℂ) :
    xiCentralReciprocalSquare (1 - rho) = xiCentralReciprocalSquare rho ∧
      analyticOrderAt xi (1 - rho) = analyticOrderAt xi rho ∧
      (analyticOrderAt xi rho).toNat + (analyticOrderAt xi (1 - rho)).toNat =
        2 * (analyticOrderAt xi rho).toNat := by
  refine ⟨xiCentralReciprocalSquare_one_sub rho, xi_orderAt_one_sub rho, ?_⟩
  rw [xi_orderAt_one_sub]
  omega

/-- The four xi symmetries fold to a conjugate pair of reciprocal atoms and preserve the original
analytic order at every member of the quartet. -/
theorem xiReciprocalFold_quartet (rho : ℂ) :
    xiCentralReciprocalSquare (1 - rho) = xiCentralReciprocalSquare rho ∧
      xiCentralReciprocalSquare ((starRingEnd ℂ) rho) =
        (starRingEnd ℂ) (xiCentralReciprocalSquare rho) ∧
      xiCentralReciprocalSquare (1 - (starRingEnd ℂ) rho) =
        (starRingEnd ℂ) (xiCentralReciprocalSquare rho) ∧
      analyticOrderAt xi (1 - rho) = analyticOrderAt xi rho ∧
      analyticOrderAt xi ((starRingEnd ℂ) rho) = analyticOrderAt xi rho ∧
      analyticOrderAt xi (1 - (starRingEnd ℂ) rho) = analyticOrderAt xi rho := by
  refine ⟨xiCentralReciprocalSquare_one_sub rho,
    xiCentralReciprocalSquare_conj rho, ?_, xi_orderAt_one_sub rho,
    xi_orderAt_conj rho, ?_⟩
  · rw [xiCentralReciprocalSquare_one_sub, xiCentralReciprocalSquare_conj]
  · rw [xi_orderAt_one_sub, xi_orderAt_conj]

/-- Each functional-equation pair inside a quartet contributes twice the original xi
multiplicity. -/
theorem xiReciprocalFold_quartet_weights (rho : ℂ) :
    (analyticOrderAt xi rho).toNat + (analyticOrderAt xi (1 - rho)).toNat =
        2 * (analyticOrderAt xi rho).toNat ∧
      (analyticOrderAt xi ((starRingEnd ℂ) rho)).toNat +
          (analyticOrderAt xi (1 - (starRingEnd ℂ) rho)).toNat =
        2 * (analyticOrderAt xi rho).toNat := by
  constructor
  · rw [xi_orderAt_one_sub]
    omega
  · rw [xi_orderAt_conj, xi_orderAt_one_sub, xi_orderAt_conj]
    omega

/-- A point `1/2 + i*gamma` maps to the positive real reciprocal atom `gamma⁻²`. -/
theorem xiCentralReciprocalSquare_criticalLine (gamma : ℝ) :
    xiCentralReciprocalSquare (1 / 2 + (gamma : ℂ) * I) =
      ((gamma⁻¹ ^ 2 : ℝ) : ℂ) := by
  simp only [xiCentralReciprocalSquare]
  rw [show (1 / 2 + (gamma : ℂ) * I) - 1 / 2 = (gamma : ℂ) * I by ring]
  rw [mul_inv_rev, inv_I]
  push_cast
  ring_nf
  rw [I_sq]
  ring

/-- The critical-line functional-equation pair folds to `gamma⁻²` with twice its xi
multiplicity. -/
theorem xiReciprocalFold_criticalLine_pair (gamma : ℝ) :
    xiCentralReciprocalSquare (1 - (1 / 2 + (gamma : ℂ) * I)) =
        ((gamma⁻¹ ^ 2 : ℝ) : ℂ) ∧
      analyticOrderAt xi (1 - (1 / 2 + (gamma : ℂ) * I)) =
        analyticOrderAt xi (1 / 2 + (gamma : ℂ) * I) ∧
      (analyticOrderAt xi (1 / 2 + (gamma : ℂ) * I)).toNat +
          (analyticOrderAt xi (1 - (1 / 2 + (gamma : ℂ) * I))).toNat =
        2 * (analyticOrderAt xi (1 / 2 + (gamma : ℂ) * I)).toNat := by
  refine ⟨?_, xi_orderAt_one_sub _, ?_⟩
  · rw [xiCentralReciprocalSquare_one_sub,
      xiCentralReciprocalSquare_criticalLine]
  · rw [xi_orderAt_one_sub]
    omega

end


end RHTower
