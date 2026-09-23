import GaloisForLFunctions.RHTower.QuarterGramEntry
import GaloisForLFunctions.RHTower.BaezDuarteDistance

/-!
# A uniform bound on all Báez-Duarte distances

Every bound so far has been for one section.  Monotonicity upgrades the best single-generator bound to the
whole sequence: the discrete section of length `N` contains the modulus `4` as soon as `N ≥ 4`, so its distance
is at most the one-generator distance at `1/4`.

**`bdDistDiscrete_sq_le_quarter` — `d_N² ≤ 1 − (log 2)²/(4·((3log 2)/8 − π/32))` for every `N ≥ 4`.**

This is the first statement in the development that constrains the *entire* sequence `d_N` rather than a single
section, and it is unconditional.  It is also the strongest such statement this machinery can give: by
`SingleGeneratorUseless` no single modulus does better than `O((log m)²/m)`, and any bound uniform in `N` that
stayed away from `0` for *all* `N` would contradict nothing — but improving it towards `0` needs the collective
estimate that remains open, since a *uniform* bound tending to `0` would be `d_N → 0`, i.e. the Riemann
hypothesis.

The complementary direction is `ArithmeticEvaluationObstruction.dist_floor_of_forall_dvd`, which gives a
positive floor for each section (at `n₀ = N !`, in the step-vector formulation of `StepFunctionCarrier`).  So
each `d_N` is strictly positive while the whole sequence is bounded above by the constant here, and the open
question is exactly whether the infimum is `0`.
-/

open Finset

noncomputable section

namespace RHTower

/-- **A uniform bound on the whole sequence of Báez-Duarte distances.** -/
theorem bdDistDiscrete_sq_le_quarter {N : ℕ} (hN : 4 ≤ N) :
    bdDistDiscrete N ^ (2 : ℕ)
      ≤ 1 - Real.log 2 ^ (2 : ℕ) / (4 * (3 * Real.log 2 / 8 - Real.pi / 32)) := by
  have hmem : (3 : ℕ) ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have hsub : Set.range (fun _ : Fin 1 => bdGen (1 / (4 : ℝ)))
      ⊆ Set.range (fun i : {x // x ∈ Finset.range N} => bdGen (bdDiscrete i)) := by
    rintro _ ⟨_, rfl⟩
    refine ⟨⟨3, hmem⟩, ?_⟩
    have h4 : bdDiscrete 3 = 1 / (4 : ℝ) := by
      rw [bdDiscrete]
      norm_num
    show bdGen (bdDiscrete 3) = bdGen (1 / (4 : ℝ))
    rw [h4]
  have hmono : bdDistDiscrete N ≤ bdDist (fun _ : Fin 1 => 1 / (4 : ℝ)) := by
    rw [bdDistDiscrete, bdDistFinset]
    exact bdDist_mono _ _ hsub
  have hnn : 0 ≤ bdDistDiscrete N := bdDist_nonneg _
  have hbound := bdDist_sq_le_quarter_bound
  nlinarith [hmono, hnn, hbound, bdDist_nonneg (fun _ : Fin 1 => 1 / (4 : ℝ))]

end RHTower

end
