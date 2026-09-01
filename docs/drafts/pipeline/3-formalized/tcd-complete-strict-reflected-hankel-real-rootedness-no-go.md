# TCD complete strict reflected-Hankel real-rootedness no-go

- **ID:** tcd-complete-strict-reflected-hankel-real-rootedness-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · TCD cofinal landing
- **Statement:** Positive real entire source + exact reflected jets + positive-definite Hankel matrices at every real center and finite rank does not imply real-rootedness.

## Goal

Kill `finite D1 → cofinal strict reflected-Hankel positivity → real-rootedness → RH` before further finite-sign work.

## Gates

- [x] Corpus-derived RH chain and counterexample
- [x] Dependency-closed proof
- [x] Lean theorem, targeted build, axioms audit
- [ ] Publication-ready

## Proof

Set `F(z)=exp(z²/4)(cosh z+cosh 2z)`. It is entire, positive on `ℝ`, and still vanishes at `iπ/3`. The reflected product is the old positive five-frequency cosh mixture multiplied by `exp(x²/2)exp(t²/2)`. For each frequency `a`, even jets of `exp(t²/2)cosh(at)` are moments of the square of a shifted `N(a,1)` variable. That measure has infinite support, so every finite Hankel matrix is positive definite. Positive finite sums and the positive center factor preserve positive definiteness.

## No-go closure

- **Exact killing theorem:** `completeStrictReflectedHankel_realRootedness_noGo`.
- **Strongest positive survivor:** `gaussianDressedTwoCoshReflectedMoment_posDef` gives exact all-center/all-rank strict reflected-Hankel geometry from shifted-Gaussian square laws.
- **New insight:** complete strict Hankel data encode an infinite-support moment representation, not zero-divisor location. TCD needs independent theta–Xi/source–divisor incidence.
- **Status:** `RHTower/TCDCompleteStrictReflectedHankelRealRootednessNoGo.lean`; targeted build passes; standard axioms only. Literature search through 2026-09 found no exact statement. Closest criterion, Cardon's extended Laguerre inequalities, assumes the Laguerre–Pólya Gaussian sign `exp(-bz²)`, `b≥0`, and tests different signed jets: <https://arxiv.org/abs/0911.1122>.
