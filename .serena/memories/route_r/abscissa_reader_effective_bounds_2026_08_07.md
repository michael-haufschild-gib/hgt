# Abscissa reader: effective single-height bounds (2026-08-07)

Extends `mem:route_r/analytic_abscissa_reader_formalized_2026_08_07`. Same module
`RHTower/HarmonicResidueAbscissaReader.lean`, `lake build` green (3178 jobs), axioms
`[propext, Classical.choice, Quot.sound]`. All off the Route R cone.

## Deviation bound (single `s > 1`, no asymptotics)

`norm_primeAbscissaSeries_div_sub_residue_le` — with `L(s) = -log(s-1)` and `M = ∑_p ‖a - c/p‖`:

  `‖A(s)/L(s) - c‖ ≤ (‖c‖·|P(s) - L(s)| + M) / L(s)`.

Proof: split `A/L - c = c(P-L)/L + R/L`, then the uniform remainder bound
`norm_primeAbscissaRemainder_le`. Both right-hand ingredients are explicit corpus objects —
`|P(s) - L(s)| → |primeLogDefect 1|` by `tendsto_primeZeta_add_log_sub`.

## Height bound at a unit residue

`abscissaLog_le_of_norm_div_le` — if `‖c‖ = 1` and `‖A(s)/L(s)‖ ≤ r` with `r < 1` then

  `L(s) ≤ (|P(s) - L(s)| + M) / (1 - r)`.

A sub-quantum reading bounds `L(s)`, hence bounds `s` away from the abscissa. This is the analytic
counterpart of the profile-side `abs_le_of_norm_stageAverage_le`, under the correspondence
`height u = s-1 ↔ 1/log(depth)` recorded in the card addendum. Contrapositive: past an explicit
height a unit residue cannot read below the quantum — the third-pass bounded-depth no-go in analytic
language, now with an explicit constant.

## Why this shape

A producer cannot act on a limit; it needs a bound at a height it can actually reach. Both theorems
hold at one `s`, and neither mentions the Route R first-wall field, so they apply to any producer
field with a unit residue.

## Lean notes

- `div_le_div_of_nonneg_right (h : a ≤ b) (hc : 0 ≤ c) : a/c ≤ b/c` — takes `0 ≤ c`, not `0 < c`.
- The reverse triangle step is `norm_sub_le x (x - c)` plus `simpa`; there was no need for a named
  reverse-triangle lemma.
- `push_cast; field_simp; ring` handled the complex identity `A/L - c = (c(P-L) + R)/L`.
