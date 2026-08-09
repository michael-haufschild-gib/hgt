# The Gram diagonal reduces to two scalars, and there the elementary method stops

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## Where this sits

`nyman-beurling-carrier-no-hardy-space.md` reduced the Riemann hypothesis, in Lean and unconditionally, to a
statement about `bdGram` — the Gram matrix of the Báez-Duarte generators — and nothing else. This card takes
the elementary part of `bdGram` as far as the technique goes and draws the boundary with a theorem rather
than a remark.

## What is proved

`RHTower/BaezDuarteGramReduction.lean`.

Expanding the diagonal square gives three tail integrals. Two collapse under the same dilation-and-split
identity that evaluated the target pairing:

* `integral_Ioc_fractSqInvSq` — `∫_θ^1 {v}²v^{-2}dv = 1 − θ`, because `{v}²v^{-2} = 1` on `(θ,1)`;
* `integral_Ioi_one_fractSq_dilate` — **`∫₁^∞ {θv}²v^{-2}dv = θ(1−θ) + θ·fractSqConst`**, where
  `fractSqConst = ∫₁^∞ {v}²v^{-2}dv`.

The third does not collapse: `fractCrossTail θ = ∫₁^∞ {θv}{v}v^{-2}dv` mixes two incommensurable dilations
and no substitution separates them. Result:

**`bdGram_self_eq` — `bdGram θ θ = θ(1−θ) + θ(1+θ)·fractSqConst − 2θ·fractCrossTail θ`.**

Also proved, and free from the earlier formulas: `explained_mass_le_one` — for *every* solution of a
Báez-Duarte normal system, `−∑ᵢ cᵢθᵢ log θᵢ ≤ 1`. This is `d² ≥ 0` plus the unit target, and it is an
unconditional constraint on the Gram systems that does not mention the zeros.

## The boundary, stated plainly

The diagonal is elementary modulo exactly two scalars:

1. `fractSqConst`, a single constant. It is a Stirling-type quantity (its interval-by-interval expansion is
   `∑ₙ [1 + n/(n+1) − 2n log(1+1/n)]`, convergent like `∑1/(3n²)`, whose closed form carries `log 2π`);
2. `fractCrossTail θ`, a function of `θ`. For rational `θ` this is the Vasyunin/cotangent-sum object.

Neither is reachable by dilation-and-split, which is the only technique that has worked in this lane —
every other computation here (`inner_bdGen_bdTarget`, the detector norms, the dilate transforms, the two
square terms above) fell to it, and these two provably do not, because the cross term has no single scaling
that normalises both fractional parts at once. Getting them needs new machinery: Mellin–Plancherel on a
half-line (mathlib has Fourier–Plancherel, but the transfer plus the boundary limit is a substantial build)
or the lattice/cotangent computation from scratch (mathlib has no Dedekind or cotangent sums).

That is the whole remaining gap between this corpus and a Lean proof of the Riemann hypothesis via this
route — one constant and one function, both classical, neither cheap.

## Addendum (same day): the first scalar has an exact series

`RHTower/FractSqConstSeries.lean` evaluates `fractSqConst` exactly, by the only route the tail integral
allows — cut the ray at the integers, where the fractional part is linear, and integrate each cell in closed
form:

* `iUnion_tailCell`, `pairwise_disjoint_tailCell` — `(1,∞)` is the disjoint union of the cells
  `(n+1, n+2]`;
* `fract_eq_sub_of_mem_tailCell` — on a cell, `{v} = v − (n+1)`;
* `integral_tailCell_fractSqInvSq` — one cell contributes
  `1 + (n+1)/(n+2) − 2(n+1)·log((n+2)/(n+1))`, from `∫1`, `∫v⁻¹ = log((a+1)/a)` and `∫v⁻² = 1/a − 1/(a+1)`;
* **`hasSum_fractSqConst`** — `HasSum (fun n => 1 + (n+1)/(n+2) − 2(n+1)·log((n+2)/(n+1))) fractSqConst`,
  via `MeasureTheory.hasSum_integral_iUnion`.

The terms are `∼ 1/(3n²)`, so this is a rapidly convergent explicit series: the constant is now an
elementary object rather than an unevaluated integral. Its closed form is still the Stirling-type quantity
carrying `log 2π`, and that step — summing the series — is not done here.

So of the two scalars, the first now has an exact elementary series and the second (`fractCrossTail`, the
cotangent object) remains untouched. The cell-cutting technique used here is exactly what the cross term
would need too, but there the cells of `{θv}` and `{v}` interleave incommensurably, which is the same
obstruction stated in the main text.
