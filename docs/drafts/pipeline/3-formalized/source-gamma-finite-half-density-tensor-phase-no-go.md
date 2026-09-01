# Finite half-density tensor-phase source-naturality no-go

- **ID:** HD-PH
- **Stage:** 3-formalized
- **Type:** PROVED ROUTE-CLASS NO-GO
- **Corpus basis:** literal `bilateralHalfDensityCharacter`; positive archimedean anchoring in `PrimeGammaTwoThreeSourceNaturalReporter`; `two_prime_log_indep`; `xiDivisorSupport_one_lt_abs_im`.

## Chain

`finite physical half-density tensor character -> positive-arch source-natural Gamma ghost -> shared HB/FZZ-P/PW-B/RBH endpoint -> RH`.

## Result

After exact radial normalization, degree-`n` physical phase at prime `p` is `exp(-i n Im(rho) log p)`. For every `n>0`, positive real archimedean anchoring at both `p=2,3` forces both phases to equal `1`. Integral independence of `log 2, log 3` then forces `Im(rho)=0`, impossible for actual Xi divisor support.

Hence no positive finite tensor degree—including radial-exact degree `4`—can realize source/Gamma naturality even pointwise. Survivor must be non-tensorial, prime-coupled, or carry a nontrivial archimedean phase outside the positive shared-ghost interface.

Closed Lean theorem: `RHTower.sharedWardFiniteHalfDensityTensorPhaseRouteKilled` in `SourceGammaFiniteHalfDensityTensorPhaseNoGo.lean`. Targeted build passed; axioms are only `propext`, `Classical.choice`, `Quot.sound`. Corpus and literature search through 2026-08 found no matching theorem.

## Gates

- [x] Corpus search and exact proof chain
- [x] Paper proof
- [x] Lean proof
- [x] Targeted build/axiom/umbrella audit
