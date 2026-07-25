import GaloisForLFunctions.RHTower.XiHedenmalmNumericalSectorCollision
import GaloisForLFunctions.RHTower.TwinFactorization

/-!
# Exact right-half Jordan-normal ladder closure

Right-half local Jordan normality is a genuine simplicity condition only when a right-half Xi
divisor point exists.  Under RH that locus is empty, so the condition is automatic.  Combining
this converse with the existing Jordan-normality--ladder collision classifies the pair exactly:
any positive divisor rung together with right-half local normality is equivalent to RH.
-/

namespace RHTower

/-- At every positive rung, the multiplicity ladder paired with right-half local Hedenmalm Jordan
normality is exactly RH. -/
theorem rhLadder_and_xiRightHalfLocalJordanNormal_iff_riemannHypothesis
    {k : ℕ} (hk : 1 ≤ k) :
    (RHLadder k ∧ XiRightHalfLocalJordanNormal) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨hladder, hnormal⟩
    exact riemannHypothesis_of_rhLadder_of_rightHalfLocalJordanNormal
      hk hladder hnormal
  · intro hRH
    exact ⟨(rh_iff_forall_ladder.mp hRH) k,
      xiRightHalfLocalJordanNormal_of_riemannHypothesis hRH⟩

/-- First-rung form of the exact Jordan-normality collision. -/
theorem rhLadder_one_and_xiRightHalfLocalJordanNormal_iff_riemannHypothesis :
    (RHLadder 1 ∧ XiRightHalfLocalJordanNormal) ↔ RiemannHypothesis :=
  rhLadder_and_xiRightHalfLocalJordanNormal_iff_riemannHypothesis le_rfl

/-- The divisor-balanced twin factorization paired with right-half local Hedenmalm normality is
an exact RH criterion.  Neither factor alone controls both multiplicity parity and simplicity. -/
theorem twinFactorization_and_xiRightHalfLocalJordanNormal_iff_riemannHypothesis :
    (TwinFactorization ∧ XiRightHalfLocalJordanNormal) ↔ RiemannHypothesis := by
  rw [← rhLadder_one_iff_twinFactorization]
  exact rhLadder_one_and_xiRightHalfLocalJordanNormal_iff_riemannHypothesis

end RHTower
