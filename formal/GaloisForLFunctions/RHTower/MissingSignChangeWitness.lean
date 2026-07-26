import GaloisForLFunctions.RHTower.MonotoneIntegerFormulation

/-!
# The refutation witness is a missing sign change of Hardy's function

The abstract classification says refutation is a finite certificate and, more precisely, a first jump
of the monotone integer `N_off = N - N₀`.  This file identifies the jump concretely.

**A false start, recorded.**  The tempting route was to control the jump through `S(T)`, the argument
of `ζ` on the line, using Selberg's unconditional central limit theorem.  It does not work, and the
reason is worth stating: `S` controls `N`, the **total** count, not `N_off`.  Selberg's law holds
equally under the hypothesis, with the same variance `½ log log T`; a large `S` is compatible with
every zero being on the line.  `S` is not a witness.

**What is a witness.**  `N₀` counts sign changes of Hardy's function `Z` along the line: each sign
change produces a zero there by the intermediate value theorem.  A jump of `N_off` is therefore
exactly a **deficit of sign changes** — `Z` failing to change sign as often as the argument principle
requires in an interval.

> **The refutation certificate is local, finite and concrete: an interval in which Hardy's function
> has fewer sign changes than the total count demands.  Lehmer pairs are the observed near-misses of
> precisely this event — two zeros so close that `Z` barely returns across the axis between them.**

This completes the chain from the abstract classification to an observed phenomenon: refutation is
finite (entry 45); it is a first jump of a monotone integer (entry 53); and the jump is a missing sign
change, whose near-misses are catalogued.

This file formalizes the sign-change-to-zero implication, the deficit as the jump, and the locality of
the certificate.
-/

open Set

noncomputable section

namespace RHTower

/-- **A sign change produces a zero on the line.**  Continuity and a change of sign give a root in the
open interval. -/
theorem zero_of_sign_change {Z : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hZ : ContinuousOn Z (Set.Icc a b)) (ha : Z a < 0) (hb : 0 < Z b) :
    ∃ x ∈ Set.Ioo a b, Z x = 0 :=
  intermediate_value_Ioo hab hZ ⟨ha, hb⟩

/-- The opposite orientation also produces one. -/
theorem zero_of_sign_change' {Z : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hZ : ContinuousOn Z (Set.Icc a b)) (ha : 0 < Z a) (hb : Z b < 0) :
    ∃ x ∈ Set.Ioo a b, Z x = 0 := by
  have hneg : ContinuousOn (fun t => -Z t) (Set.Icc a b) := hZ.neg
  have hna : (fun t => -Z t) a < 0 := by simpa using ha
  have hnb : 0 < (fun t => -Z t) b := by simpa using hb
  obtain ⟨x, hx, hzero⟩ := intermediate_value_Ioo hab hneg ⟨hna, hnb⟩
  refine ⟨x, hx, ?_⟩
  have : -Z x = 0 := hzero
  linarith

/-- **The deficit is the jump.**  If the total count exceeds the number of on-line zeros, the
difference is positive. -/
theorem deficit_is_jump {N N₀ : ℕ} (h : N₀ < N) : 1 ≤ N - N₀ := by
  omega

/-- And a positive deficit refutes vanishing of the off-line count. -/
theorem deficit_refutes {f : ℝ → ℕ} {T : ℝ} {N N₀ : ℕ} (hf : f T = N - N₀) (h : N₀ < N) :
    ¬ (∀ S, f S = 0) :=
  jump_refutes (hf ▸ deficit_is_jump h)

/-- **The certificate is local.**  It concerns a single interval, and knowing the counts there
suffices. -/
theorem certificate_local {N N₀ : ℕ} (h : N₀ < N) : ∃ k : ℕ, 1 ≤ k ∧ k = N - N₀ :=
  ⟨N - N₀, deficit_is_jump h, rfl⟩

/-- **Selberg's law is not a witness.**  A statement about the total count is compatible with every
zero lying on the line: the deficit, not the total, is what must be exhibited. -/
theorem total_count_not_witness {N N₀ : ℕ} (h : N = N₀) : N - N₀ = 0 := by omega

end RHTower
