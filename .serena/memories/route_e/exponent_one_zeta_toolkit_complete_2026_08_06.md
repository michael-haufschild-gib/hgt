# The exponent-1 zeta toolkit is complete and corpus-owned

All unconditional (`[propext, Classical.choice, Quot.sound]`). Card:
`docs/drafts/pipeline/3-formalized/zero-free-region-exponent-one.md`.

| statement | name | module |
|---|---|---|
| zero-free region, width `1/(10000 log\|γ\|)` | `exists_zero_free_region_explicit` | `ZeroFreeRegionKappaOne.lean` |
| … the same shape from height `9` (tiny constant) | `exists_zero_free_region_from_nine` | `ZeroFreeRegionFromNine.lean` |
| zero count **on `Re ρ ≥ 3/5`**, `O(log\|γ\|)` | `exists_wide_zero_count` | `ZetaZeroCountWide.lean` |
| `‖ζ'/ζ‖ ≤ C log²\|γ\|` on width `1/(40000 log\|γ\|)` | `exists_logDeriv_zeta_bound_explicit` | `ZetaLogDerivRegionBound.lean` |
| … the same from height `10` | `exists_logDeriv_zeta_bound_from_ten` | same |
| `‖ζ‖ ≥ c / log²\|γ\|` on `\|σ-1\| ≤ log^{-2}\|γ\|` | `exists_zeta_lower_strip` | `ZetaLowerStripMultiplicative.lean` |

Every one is strictly sharper than the vendored `PNTPlus` counterpart (`ZetaZeroFree` `log^{-9}`;
`LogDerivZetaBnd` `log^9`; `ZetaLowerBnd` `log^{-7}` on width `log^{-9}`). This supersedes the
"corpus and PNTPlus both own only κ = 9" line in `mem:zero-free-region-exponent-is-the-mr-wall`.

## Two corrections made after the fact — read before quoting the toolkit

1. **`exists_zero_count_bound` (narrow disc) is vacuous** and was wrongly reported as the classical
   `N(t+1)-N(t) = O(log t)`. See `mem:route_e/zero_count_narrow_disc_is_vacuous_2026_08_06`. The
   wide version above is the sound one, and it covers only `Re ρ ≥ 3/5` — not the critical strip.
2. **Constants were hidden behind `∃` even though the proofs computed them.** All now exposed (the
   table above). A statement whose constant is existential is true, unusable downstream, and
   incomparable with the literature — e.g. it was impossible to say how the region compares with
   arXiv:2603.21490's `1/(4.896 log t)` from `t ≥ 3`. **Expose any constant the proof produces.**

## Three structural facts

1. **The mean-value route is capped at κ = 9 by itself**, independently of the region's width
   (`mem:route_e/zero_free_kappa9_is_structural_2026_08_06`). The exit is Landau's lemma.
2. **Landau's lemma needs no zero counting** — split the zeros, remove only those in the half-disc,
   and the boundary comparison is termwise (`mem:route_e/landau_lemma_proved_2026_08_06`).
3. **The `1/ζ` transport must start at `σ₁ = 1 + log^{-2}`**: the cost is
   `‖ζ'/ζ‖ × length = C log² × 2 log^{-2} = 2C`, constant. At `log^{-1}` it becomes `2C log|γ|`
   (`mem:route_e/inv_zeta_width_ceiling_2026_08_06`).

**Corollary of (3) worth knowing:** the `1/ζ` strip cannot be re-derived from the corpus's explicit
κ=9 region — a disc of radius `3/L²` fits inside a region of width `c₉/L⁹` only if `L⁷ < c₉/2`,
false for `L ≥ 3`. So that result is intrinsically tied to the κ=1 region and inherits its
astronomical threshold (`≈ exp(50000)` with the explicit constants).

## Elaboration discipline

A `have`-chain of ~30 steps inside one theorem exceeds the heartbeat budget, failing with `linarith`
errors *and* `whnf`/`isDefEq` timeouts that look unrelated. The same content as **top-level lemmas
with explicit hypotheses** compiles in seconds. Every module above is written that way; do not
re-inline.

## `linarith` and division

`linarith` treats `a / X` as an atom when `X` is not a numeral: it does not relate `1/L^2` to
`2/L^2`, nor `3/δ` to `3*(1/δ)`. Insert `have : (2:ℝ)/L^2 = 2*(1/L^2) := by ring` first. Hit three
times in this build.

## What this does NOT give

- Not `1/ζ ≪ log t` on the κ=1 region (see the ceiling memory).
- Not Littlewood's `c loglog t/log t` region: shrinking the Landau radius costs what it gains.
- Route E's corridor still wants κ < 1, so it remains blocked on a different mechanism.
