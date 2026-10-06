# BAG: actual prime-band pair prefixes and harmonic gaps

2026-10-06,21az. Lean proves a single C>0 and threshold, independent of
D, such that every natural D satisfies

    sum_{1≤d≤D} P_N(d) ≤ C D N/log²N,
    sum_{1≤d≤D} P_N(d)/d ≤ C N(1+log D)/log²N,

where P_N(d) counts actual primes r,r+d in the original sharp band (N,2N].
No prime-correlation premise appears. Zero cutoffs are included.

## Proof

The literal primeProfileBand equals bigPrimeSet(floor N,floor 2N).
Source-read `Sieve/GenericMarkerAnalytic.lean:308` gives the complete
averaged pair sieve at this integer base, uniformly in D, with full
remainder 2D(floor N)^(3/4). Eventually log(floor N)≥log N/2 and
2N^(3/4)≤N/log²N. Thus the same C works for all D. This uses the existing
sieve specialization; it does not improve a numerical constant.

Finite Abel summation keeps the endpoint at D+1. Every reciprocal-weight
difference is nonnegative, so cumulative bound A_k≤αk compares the whole
weighted sum with the constant sequence α. Its harmonic sum is at most
1+log D. Both signs of a gap can later be treated by reindexing the lower
prime; the present theorem counts positive gaps exactly.

## Validation

`ChiCubicHyperbolicPrimePairs.lean`,157 lines. Public API:

- 21: `chiCubicPrimeGapCount`.
- 30: `exists_chiCubicPrimeGapCount_prefix_bound`.
- 142: `exists_chiCubicPrimeGapCount_harmonic_bound`.

Final foreground leaf15991, `lake --old env lean` with explicit olean,
exit0 and empty output: `/tmp/bag-hyperbolic-prime-pairs-02az.log`.
Imported axiom/API62847 exit0: all three declarations use only propext,
Classical.choice and Quot.sound. Log:
`/tmp/bag-hyperbolic-prime-pairs-axioms-21az.log`. API probe42241 passed.
Wired once. Index12773 exit0; all three public API rows checked.
Authoritative lint60402 exited1:367 large-file warnings and twenty unrelated
unreachable modules; no finding names this BAG leaf. Global lint is not clean.
Log: `/tmp/bag-hyperbolic-prime-pairs-lint-21az.log`. No full build, new axiom, admission,
heartbeat override, numerical experiment, subagent, commit or push.

This closes the arithmetic prefix producer required to pay the small-gap
part of the actual continuous hyperbolic integral. Its integral assembly,
ordering hole and band-edge estimates still require Lean proofs. Actual
phase-preserving freezing and exact complete-period cancellation subsequently
passed: `bag-hyperbolic-prime-period-freezing.md`. The same prefix producer
also pays the whole ordering-hole budget on paper via its first gap moment;
exact integral and gap-reindexing assembly remains. Full cubic/tail cancellation and RH
remain open.
