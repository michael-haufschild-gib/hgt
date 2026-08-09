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
