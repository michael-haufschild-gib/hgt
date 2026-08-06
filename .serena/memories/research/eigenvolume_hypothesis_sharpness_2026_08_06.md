# All three side conditions of the horizon theorem are sharp (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **35**.
Continues [[research/topform_to_function_bridge_2026_08_06]].

## `EigenvolumeHypothesisSharpness.lean`

`eigenvolumeOrder_eq_neg_one_of_someRamified` has three side conditions beyond the local order law:
`hF` (surjective divisor map), `hfin` (finite support), `hram` (ramification on every recurrent
cycle).  All three are now known to be **necessary**:

- `hfin` — already had `exists_infiniteSupport_order_ne_neg_one`
  (in `EigenvolumeRamificationSystem.lean`).
- **`exists_unramified_order_ne_neg_one`** (new) — `α = Unit`, `F = id`, `e ≡ 1`, `c ≡ 5`.
  The law reads `5 + 1 = 1 * (5 + 1)`.  So **without ramification any constant order works**.
- **`exists_nonsurjective_order_ne_neg_one`** (new) — `α = ℕ`, `F = Nat.succ`,
  `c 0 = 1` else `0`, `e 0 = 2` else `1`.  `hone`, `hlaw`, `hfin` hold, and `hram` is **vacuous**
  because `Nat.succ` has no periodic points (`Nat.succ_iterate` + `omega`), yet `c 0 = 1 ≠ −1`.

Consequence: **Step 4's appeal to expansion is not an artefact of the proof** — the conclusion
genuinely fails without it.

## Lean notes

- `Nat.succ_iterate : Nat.succ^[n] m = m + n` is the clean way to show the successor map has no
  periodic points.
- For `{y | (if y = 0 then 1 else 0) ≠ 0}.Finite`, go through
  `Set.Finite.subset (Set.finite_singleton 0)` and derive `y ≠ 0` from the membership negation with
  `simpa using hne` — `simp [hne]` alone leaves the goal.

## Remaining for Theorem A

1. Different exponent `e − 1` for a general tame extension.
2. Sheaf of differentials on a scheme (for `K_X = f^*K_X + R_f`).
3. Step 4's `e > 1`: `N¹` + int-amplification (now known to be unavoidable, see above).
4. Corollary B: MMP.
