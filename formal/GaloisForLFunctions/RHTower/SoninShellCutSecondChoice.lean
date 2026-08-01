import GaloisForLFunctions.RHTower.SoninShellCutKappaFull

/-!
# One cut serving every obligation of the second choice

With the product fixed, the remaining requirements all improve as the cut refines: the outer slack
term falls with the half-width, and the coupling's largeness conditions are thresholds passed by a
scale growing linearly in the number of annuli.

So a single cut satisfies them together, and it can be taken as fine as one likes — which is what
supplies the count.
-/

noncomputable section

set_option maxHeartbeats 400000

namespace RHTower

open Filter
open scoped Topology

/-- **Every second-choice obligation is eventual in the cut.** -/
theorem eventually_soninShellCut_second_choice
    (a b c q κ D : ℝ) (hbc : b < c) (ha : 0 < a) (hq : 0 < q) (hκ : 0 < κ)
    {target : ℝ} (htarget : 0 < target) :
    ∀ᶠ N : ℕ in atTop,
      (0 < N ∧ 1 < soninShellCutScale b c N κ ∧
          b < soninShellCutScale b c N κ * q ∧ c ≤ soninShellCutScale b c N κ * a) ∧
        D * (soninRefTailSup 0 *
          Real.sqrt (soninShellCutWidth b c N * b / ∫ y : ℝ, soninUnitBumpSq y)) < target :=
  (eventually_soninShellCutScale_conditions a b c q κ hbc ha hq hκ).and
    (eventually_outerSlack_le b c D htarget)

/-- **A cut satisfying every second-choice obligation, as fine as desired.** -/
theorem exists_soninShellCut_second_choice
    (a b c q κ D : ℝ) (hbc : b < c) (ha : 0 < a) (hq : 0 < q) (hκ : 0 < κ)
    {target : ℝ} (htarget : 0 < target) (M : ℕ) :
    ∃ N : ℕ, M ≤ N ∧ 0 < N ∧ 1 < soninShellCutScale b c N κ ∧
      b < soninShellCutScale b c N κ * q ∧ c ≤ soninShellCutScale b c N κ * a ∧
      D * (soninRefTailSup 0 *
        Real.sqrt (soninShellCutWidth b c N * b / ∫ y : ℝ, soninUnitBumpSq y)) < target := by
  obtain ⟨N, hM, ⟨hN, hscale, hcarrier, hap⟩, houter⟩ :=
    ((eventually_ge_atTop M).and
      (eventually_soninShellCut_second_choice a b c q κ D hbc ha hq hκ htarget)).exists
  exact ⟨N, hM, hN, hscale, hcarrier, hap, houter⟩

end RHTower
