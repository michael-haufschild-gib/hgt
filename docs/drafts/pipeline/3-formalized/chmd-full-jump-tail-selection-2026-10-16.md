# CHMD: full-source arithmetic tail selection

Date: 2026-10-16. Route: CHMD. Positive survivor of the spatial-order conjecture.
Paper proof: dependency-closed. Both leaf builds and final plain Lean audits passed.

## Statement

Write Θ for `thetaCuspFullSource = riemannKernelReal`, ω for `archLevyDensity`,
and aₙ for the original `vonMangoldtAtom n` (zero for n < 2). The original Doob
mass density is Θ(x) cosh(x/2). Dividing the original forward edge densities by
this mass gives, for x < b, the complete upward rate

R(x,b) = [∫_{t>b−x} ω(t) Θ(x+t) dt
          + Σₙ 1_{b≤x+log n} aₙ Θ(x+log n)] / cosh(x/2).

The archimedean endpoint may equally be included: it has zero Lebesgue mass.
The arithmetic endpoint is included. For x ≥ 1, the archimedean integrand is
integrable and the complete prime series is summable. Backward source edges
cannot reach b when x < b.

For every integer m ≥ 2,

cosh(x/2) R(x,x+log m) / Θ(x+log m) → aₘ as x → +∞.

For every fixed 0 < h < log m − log(m−1),

cosh(x/2) R(x+h,x+log m) / Θ(x+log m) → 0.

Thus the complete source tail recovers each original arithmetic atom; its
archimedean part and all later arithmetic atoms vanish in this normalization.
Whenever aₘ > 0, eventually R(x+h,x+log m) < R(x,x+log m). With m = 2 and
h = log 2 / 2 this gives an unconditional witness with 1 ≤ x < x+h < x+log 2.

## Paper proof

Let K = `thetaEnvelopeUpper / thetaEnvelopeLower` > 0. The existing theta
envelope theorems give Θ(u+t)/Θ(u) ≤ K exp(−2t) for u ≥ 1 and t ≥ 0.
The existing strict translate-ratio theorem gives Θ(x+v)/Θ(x+u) → 0 if u < v.

Set Pₘ(x) = Σ_{n≥m} aₙ Θ(x+log n). The normalized n = m term equals aₘ;
each n > m term tends to zero. For x ≥ 1 and n ≥ m ≥ 2,

0 ≤ aₙ Θ(x+log n)/Θ(x+log m)
  ≤ K m² |Λ(n)|/n².

Indeed, exp(−2(log n−log m)) = m²/n², and aₙ = Λ(n)/√n ≤ |Λ(n)|.
The corpus proves summability of |Λ(n)|/n². Dominated convergence for the
whole countable series therefore proves Pₘ(x)/Θ(x+log m) → aₘ and proves
summability of the unnormalized series throughout x ≥ 1. No finite-prime
truncation enters the result.

For s > 0 set A(s,x) = ∫_{t>s} ω(t) Θ(x+t) dt. For t > s and x+s ≥ 1,

0 ≤ ω(t) Θ(x+t)/Θ(x+s) ≤ K ω(t).

The corpus proves ω integrable on (s,∞), and the strict translate-ratio
theorem gives pointwise convergence to zero for every t > s. Dominated
convergence for the full integral proves A(s,x)/Θ(x+s) → 0. The same
domination proves integrability where used.

For 0 ≤ h < log m−log(m−1), the condition
x+log m ≤ x+h+log n is equivalent to m ≤ n for every n ≥ 2. The n = 0,1
terms vanish independently. Hence the exact rate numerator at state x+h
and threshold x+log m is A(log m−h,x+h) + Pₘ(x+h).

For h = 0, the two preceding limits give the first tail law. For h > 0,

Pₘ(x+h)/Θ(x+log m)
 = [Pₘ(x+h)/Θ(x+h+log m)] [Θ(x+h+log m)/Θ(x+log m)] → aₘ·0.

The archimedean endpoint is unchanged, since
(x+h)+(log m−h) = x+log m, so its normalized contribution also tends to
zero. The remaining factor cosh(x/2)/cosh((x+h)/2) lies in (0,1] for
x ≥ 0. Squeezing gives the second tail law. If aₘ > 0, compare the two
normalized rates with aₘ/2 and cancel the common positive normalization.
At m = 2, a₂ = log 2 / √2 > 0, completing the unconditional witness.

## Lean artifacts

- `formal/GaloisForLFunctions/RHTower/CHMDPrimeTailSelection.lean`:
  `primeTail_selects_first`, `primeTail_advanced_vanishes`, `archTail_vanishes`;
  supporting summability and integrability.
- `formal/GaloisForLFunctions/RHTower/CHMDJumpTailOrderObstruction.lean`:
  literal graph-density rate, closed-endpoint identity, convergence of both
  source components, both normalized rate laws, `exists_rate_order_reversal`
  and `not_upper_rate_monotone`.

## Scope

This closes the literal spatial-order shortcut and exposes an arithmetic
tail-selection invariant. It does not construct a jump semigroup, prove a
negative quadratic direction, establish the primitive spectral gap, or prove RH.
CHMD's primitive-sector cosh domination remains open.

## Validation

Both `lake --old build` leaf builds passed. Final plain `lake env lean` audits
of both leaves passed with empty output. A separate mathlib-name probe passed.
Both leaves are wired exactly once into `RHTower.lean`; scoped whitespace checks
passed. All 40 declarations passed a `/tmp` axiom audit with only `propext`,
`Classical.choice`, and `Quot.sound`. `scripts/formal_tools.py index` passed;
global formal lint exited 1 solely because the concurrent, unrelated module
`GaloisForLFunctions.RHTower.PaperThetaCutMeyerCurrent` is unreachable from its
theorem-area umbrella. No CHMD lint error was reported. All 13 owned scratch files were removed and
their absence verified; all owned processes reached terminal exit. No unrelated
module was modified.
