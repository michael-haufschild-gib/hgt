# SQB: horizontal theta weight as signed radial quadrature

Status: formalized and audited, with 22 public declarations. RH and normalized full-native Xi occurrence remain unproved.

## Exact result

Let `f = SelbergThetaNativeSource.positiveProfile` and let `J` be the fixed horizontal weight in `SelbergThetaCommonForcingPairing`. Define

    g(u) = integral_R f(1/(u^2+v^2)) dv,
    B = integral_0^infinity g(u) du,
    L = sum_{d>=1} mu(d)/d^2,
    Q(t) = t sum_{k>=1} g(kt) - B.

`SelbergThetaHorizontalArithmetic` proves, for every `y>0`,

    J(y) = f(y) + sqrt(y) sum_{c>=1} phi(c)/c g(c sqrt(y)),
    J(y) - L B = f(y) + sum_{d>=1} mu(d)/d^2 Q(d sqrt(y)).

These are identities for the original positive source and its complete native horizontal mean. Every primitive row, reduced residue, integer translate, and denominator is retained. The complex-valued implementation uses the literal complexification of `f`.

The actual projection has a uniform bound on `u>0`, an inverse-cube bound on `u>0`, and finite absolute mass on the positive half-line. Every lattice sum converges absolutely. The complete two-index Möbius source is dominated by a constant times `d^-4 k^-3`; the centered outer remainder also converges absolutely. No rearrangement depends on an unproved cancellation bound or a totalized divergent sum.

## Corpus joins

The proof combines the complete row/reduced-residue reindexing and translation mean used in `SelbergThetaDilationRows`, the actual all-power bounds of `SelbergThetaNativeSource`, the totient–Möbius normalization in `Sieve/TotientMoebiusNormalisation`, and mathlib's `sigmaAntidiagonalEquivProd`. Applicability is checked in the finished source, including its absolute-convergence obligations.

Broad OR searches supplied quadrature, variation, and summatory candidates. The inspected deep search was partial: 5,821 semantic vectors against 1,302,242 expected, with 22,630 stale source files. It was not an exhaustive search or evidence that no stronger ingredient exists. Generic compact-support BV envelopes do not yet apply directly to this noncompact projection.

## Remaining mathematical target

The native Gram needs the actual mean subtraction `M/V`, whereas this module isolates `LB`. Their expected identification needs an explicit radial-mass and native-volume proof. Separately, the signed remainder must be estimated strongly enough to orient the source pairing or force normalized native residuals to vanish. No such implication or estimate is claimed here.

A concrete analytical candidate for the next source estimate is bounded variation of the literal projection. Reflection gives `G(r)=r^-1 Phi(log r)` and `G'(r)=r^-2(Phi'(log r)-Phi(log r))`; hence

    integral_0^infinity r |G'(r)| dr = integral_R |Phi'(x)-Phi(x)| dx.

The right side is finite by the existing Schwartz source and derivative. Integrating the horizontal derivative of the radial field over the half-plane suggests `Var(g) <= 2 integral |Phi'-Phi|`. Source-specific admission and the variation theorem remain to be formalized. Its elementary unsigned consequence alone has not been shown sufficient for the native RH chain; the full signed expression is retained for a stronger comparison.

## Validation

- Scratch and final source passed `lake env lean` without diagnostics.
- `lake build GaloisForLFunctions.RHTower.SelbergThetaHorizontalArithmetic --old --no-build` identified only the new leaf as out of date.
- `lake build GaloisForLFunctions.RHTower.SelbergThetaHorizontalArithmetic --old` passed, building only that leaf; other jobs were cached replays.
- `/tmp/sqb40_axioms.lean` checked all 22 public declarations: only `propext`, `Classical.choice`, and `Quot.sound` occur.
- `scripts/formal_tools.py index` registered all 22 public declarations; `scripts/formal_tools.py lint` passed.
- The module is imported once in `RHTower.lean`; whitespace checks passed.

No numerical experiments, computed certificates, full build, umbrella build, frontier-map edit, commit, or push were performed.
