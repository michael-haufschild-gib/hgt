import GaloisForLFunctions.RHTower.Sieve.Section4QSide
import GaloisForLFunctions.RHTower.Sieve.LadderProductDefect

/-!
# The long ladder's defect over a part of the window

`Sieve/Section4BlockMaster.section4_block_master` asks for the same bound `Dfct` on the long
ladder's defect over two different parts of the window — the disc and the exceptional subset of the
annulus.  Both are contained in the window, and the integrand is a continuous nonnegative function,
so the closed bound of `Sieve/LadderProductDefect` over the whole window serves for both.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The long ladder's defect over any part of the window.** -/
theorem setIntegral_normSq_ladderProductDefect_le_closed_on {P : Finset ℕ} {A₀ B₀ : ℕ}
    (hA : 0 < A₀) {Q η W : ℝ} (hQ : 1 < Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ))
    {S : Set ℝ} (hSs : S ⊆ Set.Icc (-W) W) :
    (∫ w in S, ‖ladderProductDefect P A₀ B₀ Q η L w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
          * (Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q
            * ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
                * (((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
                  + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ (2 : ℕ))) := by
  classical
  have hcont : Continuous fun w : ℝ => ‖ladderProductDefect P A₀ B₀ Q η L w‖ ^ (2 : ℕ) :=
    ((continuous_ladderProductDefect' P A₀ B₀ Q η L).norm).pow 2
  have hmono : (∫ w in S, ‖ladderProductDefect P A₀ B₀ Q η L w‖ ^ (2 : ℕ))
      ≤ ∫ w in Set.Icc (-W) W, ‖ladderProductDefect P A₀ B₀ Q η L w‖ ^ (2 : ℕ) := by
    refine MeasureTheory.setIntegral_mono_set
      (hcont.integrableOn_Icc (a := -W) (b := W)) ?_ (Filter.Eventually.of_forall hSs)
    exact Filter.Eventually.of_forall fun w => by positivity
  exact hmono.trans
    (integral_normSq_ladderProductDefect_le_closed hA hQ hη hW hPprime hPge)

end

end RHTower.Sieve
