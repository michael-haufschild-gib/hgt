# Local zero count of the Xi divisor, and the Laguerre margin as a disk detector

- **ID:** xi-window-count
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Statement:** `#{ρ : |Im ρ − t| ≤ w} ≤ 8(1+w²)(C + log(|t|+4))`, and the first Laguerre margin of
  `Ξ` is strictly positive at every height whose unit ordinate window contains only on-line copies.

## Goal

Two things the corpus lacked, both needed to make the Laguerre lane quantitative.

1. **A count.** `RHTower.lorentzMass_le_log` bounds the Lorentzian mass
   `Σ_ρ 1/(1 + (t − γ)²) ≤ 8(C + log(|t| + 4))`, but nothing bounded the *number* of divisor copies
   in an ordinate window, and nothing asserted that such a window is finite.
2. **A disk criterion for the Laguerre margin.** `RHTower.laguerre_XiC_eq_tsum_inv_sq` is the exact
   identity `ΞC'² − ΞC·ΞC'' = ΞC²·Σ_q (z − a_q)⁻²`, and `two_div_sq_le_of_laguerre_nonneg` reads off
   the contribution `−2/δ²` of one conjugate pair at its own centre.  Neither gives the general
   atom, nor a sufficient condition for the margin to be positive.

## What is proved

`formal/GaloisForLFunctions/RHTower/XiWindowZeroCount.lean`:

* `xiOrdinateWindow w t = {q | |Im ρ_q − t| ≤ w}`;
* `lorentzMassTerm_ge_of_mem_xiOrdinateWindow` — a window copy carries at least `1/(1+w²)` of the
  mass;
* `finite_xiOrdinateWindow (w t) : (xiOrdinateWindow w t).Finite` — a conclusion, not a hypothesis:
  an infinite window contains finite subsets of every cardinality, and each already exceeds the
  total mass;
* `ncard_xiOrdinateWindow_mul_le`, `ncard_xiOrdinateWindow_le_log (w t)`:
  `#(window) ≤ 8(1+w²)(C + log(|t|+4))`, with `ncard_xiOrdinateWindow_one_le_log` the unit-window
  form `≤ 16(C + log(|t|+4))`.

`formal/GaloisForLFunctions/RHTower/XiLaguerreWindowPositivity.lean`:

* `laguerre_Xi_eq_tsum_inv_sq` — the corpus identity restricted to the real axis, in the `Xi` /
  `deriv Xi` form the rest of the Laguerre lane uses;
* `re_inv_sq_sub_xiSpectralPoint_eq` — the exact atom
  `((t − γ_q)² − δ_q²)/((t − γ_q)² + δ_q²)²`, where `a_q = γ_q − i δ_q`, `γ_q = Im ρ_q`,
  `δ_q = Re ρ_q − 1/2`.  The atom is positive exactly when `t` lies outside the open disk of radius
  `|δ_q|` around `γ_q`: the same disks that obstruct the Hadamard receiver `Re (ξ'/ξ) ≥ 0`;
* `laguerre_Xi_pos_of_window_onLine` — if every copy with `|t − γ_q| < 1/2` is on the critical line
  and `Ξ(t) ≠ 0`, then `L₁(t) > 0`.  A *local* converse: the Laguerre inequality at one height needs
  RH only inside one unit window;
* `laguerre_Xi_nonneg_of_window_onLine` — the non-strict form drops `Ξ(t) ≠ 0`, because at a zero of
  `Ξ` the margin collapses to `(Ξ'(t))²`;
* `laguerre_Xi_nonneg_of_offLine_floor` — the mechanism: an off-line height floor `H` gives
  `L₁(t) ≥ 0` on `|t| + 1/2 ≤ H`.  Any improvement of the floor widens the interval for free;
* `laguerre_Xi_pos_of_abs_le_four` — unconditional, from `four_half_lt_abs_im_of_xiZeroCopy`;
* `laguerre_Xi_nonneg_of_abs_le_criticalBand` — unconditional `L₁(t) ≥ 0` for `|t| ≤ 58/5`, from
  `not_exists_xiZeroCopy_offLine_of_im_sq_lt_2365_over_16`.

## Reading

The first Laguerre inequality and the Hadamard receiver have **the same obstruction disks**
`|t − γ| < |β − 1/2|`.  The margin is the first-order trace of `Re (ξ'/ξ) ≥ 0` at the critical line:
`Re (ξ'/ξ)(1/2 + it) = 0` identically, and the `σ`-derivative there is `L₁(t)/Ξ(t)²`.  So the
corpus's repulsion law and the window law above are complementary halves of one disk detector, and
the Laguerre lane inherits exactly the local obstruction of CANNOT-323.

## Next

With the count in hand the repulsion sum of `two_div_sq_le_of_laguerre_nonneg` splits: the part with
`|γ₀ − γ| ≥ 1` is at most `2·lorentzMass ≪ log γ₀`, and the near part is at most
`#(unit window) · d⁻²` where `d` is the distance from `1/2 + iγ₀` to the nearest other spectral
point.  That turns the repulsion law into `δ₀ ≫ d/√(log γ₀)`: an explicit price for the Laguerre
route, i.e. proving `L₁ ≥ 0` unconditionally is at least as hard as a zero-free neighbourhood of the
critical line of width proportional to the local zero spacing.

## Log
- 2026-09-24 — created; zero count built, Laguerre window module building.
- 2026-09-24 — correction: an earlier draft of the divisor-sum identity duplicated
  `RHTower/XiLaguerreZeroSumIdentity.lean` and was deleted.  The search that missed it was a
  truncated `rg -l` file list; the reliable check is `grep <prefix> RHTower.lean`, which lists every
  module by name.

## Quantitative separation (built)

`formal/GaloisForLFunctions/RHTower/XiLaguerreSeparation.lean`, axiom-clean:

```text
laguerre_offLine_separation :
  δ ≠ 0 → 0 < d → q₁ ≠ q₂ →
  xiSpectralPoint q₁ = γ − δi → xiSpectralPoint q₂ = γ + δi → XiC γ ≠ 0 →
  (∀ q ≠ q₁, q₂, d ≤ ‖γ − xiSpectralPoint q‖) →
  0 ≤ (ΞC'(γ)² − ΞC(γ)ΞC''(γ)).re →
  2/δ² ≤ 16 (C + log(|γ| + 4)) (1 + 1/d²)
```

The proof splits the corpus's unestimated repulsion sum with the new count: copies with
`|Im ρ − γ| > 1` are dominated by twice their Lorentzian mass term (total `≤ 2·lorentzMass γ`), and
the copies with `|Im ρ − γ| ≤ 1` number at most `16(C + log(|γ| + 4))`, each costing at most `d⁻²`.

**Reading.** Wherever the first Laguerre inequality holds, an off-line zero sits at distance
`≫ d/√(log γ)` from the critical line, `d` the local zero separation.  Proving `L₁ ≥ 0`
unconditionally is therefore at least as hard as a zero-free neighbourhood of the critical line of
that width — which is open.  The Laguerre lane is priced, not free.

## Correction — relation to the corpus's existing zero counts (2026-09-24)

An earlier draft of this card claimed the corpus had no zero count. That is wrong. The corpus owns:

* `RHTower/ZetaLocalZeroCount.lean` — `N(t+1) − N(t) ≪ log t`, by Jensen on the disc of radius
  `1.95` around `2 + it`;
* `RHTower/RiemannVonMangoldt.lean`, `RHTower/XiZeroCountRVMRemainder.lean` — the full count with
  logarithmic remainder `|N(T) − (T/2π) log(T/2πe) − 7/8| ≤ C log T`;
* `RHTower/XiZeroCountLocalCeiling.lean` — the sharp window ceiling `exists_card_window_le`
  (`#F ≤ (H/2π) log(t+H) + 2C log(t+H)` for any `Finset XiZeroCopy` with ordinates in `(t, t+H]`),
  `card_le_xiZeroCount_sub`, and a block-length law;
* `RHTower/PrimeLagLandauWeights.card_absWindow_le` — copies with `|γ| ∈ [k, k+1)` number at most
  `80 log(180(k+2)) + K₀`.

What `XiWindowZeroCount` adds is therefore narrow and should be described as such:

1. `finite_xiOrdinateWindow` — finiteness of the window as a *set*. The corpus bounds the
   cardinality of a `Finset` one already holds; it does not produce the finiteness.
2. A **threshold-free** explicit bound valid at every real height, of either sign. The corpus
   ceiling is an existential over `C, T₀` and applies only for `t ≥ T₀ ≥ 4`.

Both are what `laguerre_offLine_separation` needs, since it must apply at an arbitrary off-line
ordinate with no threshold hypothesis. The corpus ceiling is sharper in the constant and should be
used wherever a threshold is acceptable.
