import GaloisForLFunctions.RHTower.SoninSublinearCompletionFails

/-!
# What a completion would have to do

Read against the schedule, the failure of every sublinear completion says something about any
completion that could succeed: its contribution cannot divide by the scale to zero.  A completion
restoring the floor at every schedule must therefore grow at least linearly in the scale along some
sequence of scales.

That is the sharpened form of the remaining question — no longer "is there a completion?" but "is
there an admissible one growing that fast?".
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- **A completion restoring the floor cannot be sublinear.**  If the floor survives at every
schedule of the shell cut, the completion's contribution does not divide by the scale to zero. -/
theorem not_sublinear_of_forall_bddBelow (N₀ : ℕ) (hN₀ : 1 ≤ N₀)
    (a b c q : ℝ) (hbc : b < c) (ha : 0 < a) (hab : a < b) (hb : 0 < b) (haq : a < q)
    (hqb : 2 * q ≤ b) (f : ℝ → ℝ)
    (hfloor : ∀ (κ : ℝ) (Nstart : ℕ) (hp : ∀ i : ℕ, 1 < soninShellCutScale b c (Nstart + i) κ),
      ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c
          (fun i => soninShellCutScale b c (Nstart + i) κ) hp
          (fun i => f (soninShellCutScale b c (Nstart + i) κ))) :
    ¬ Tendsto (fun r : ℝ => f r / r) atTop (𝓝 0) := by
  intro hsub
  obtain ⟨κ, Nstart, hp, hfail⟩ :=
    not_bddBelow_soninCompletedPacketValueVar_of_sublinear N₀ hN₀ a b c q hbc ha hab hb haq hqb
      f hsub
  exact hfail (hfloor κ Nstart hp)

end RHTower
