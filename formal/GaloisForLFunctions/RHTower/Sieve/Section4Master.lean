import GaloisForLFunctions.RHTower.Sieve.Section4BlockMaster
import GaloisForLFunctions.RHTower.Sieve.Section4Assembly

/-!
# The §4 mean-square bound at the expiry height

The single entry point for the parameter substitution: the mean square of the jointly weighted
Möbius polynomial over a symmetric window, in terms of the per-step bounds of
`Sieve/Section4BlockMaster` and the short ladder's defect.

This is the quantity `β₀` of `Sieve/JointBudgetMaster.jointOmegaBudget_le`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The §4 mean square of the joint polynomial, over the short ladder.** -/
theorem integral_normSq_jointOmegaPoly_le_master {P Q : Finset ℕ} {B₀ : ℕ} {RP ηP W : ℝ}
    (hRP : 0 < RP) (hηP : 0 ≤ ηP) {LP : ℕ} (hLP : 1 ≤ LP)
    (hPprime : ∀ p ∈ P, p.Prime) (hQprime : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q)
    (hPrange : ∀ p ∈ P, RP < (p : ℝ) ∧ (p : ℝ) ≤ RP * (1 + ηP) ^ LP)
    (u : ℕ → ℝ) (hu : ∀ j ∈ Finset.range LP, 0 < u j) (J : ℕ → ℝ) (Dshort : ℝ)
    (hJ : ∀ j ∈ Finset.range LP,
      (∫ w in Set.Icc (-W) W,
          ‖primeBlockPoly (geomBlock P RP (1 + ηP) j) w‖ ^ 2
            * ‖omegaWeightedMoebiusPoly Q (geomCofactorBlockAt 1 B₀ RP ηP j) w‖ ^ 2) ≤ J j)
    (hDshort : (∫ w in Set.Icc (-W) W,
        ‖jointLadderProductDefect P Q 1 B₀ RP ηP LP w‖ ^ 2) ≤ Dshort) :
    (∫ w in Set.Icc (-W) W, ‖jointOmegaPoly P Q (Finset.Icc 1 B₀) w‖ ^ 2)
      ≤ 2 * ((∑ j ∈ Finset.range LP, 1 / u j) * ∑ j ∈ Finset.range LP, u j * J j)
        + 2 * Dshort := by
  classical
  have hbase := integral_normSq_jointOmegaPoly_le (P := P) (Q := Q) (A₀ := 1) (B₀ := B₀)
    (W := W) hRP hηP hLP hPprime hQprime hPQ hPrange u hu J hJ
  linarith [hbase, mul_le_mul_of_nonneg_left hDshort (by norm_num : (0 : ℝ) ≤ 2)]

end

end RHTower.Sieve
