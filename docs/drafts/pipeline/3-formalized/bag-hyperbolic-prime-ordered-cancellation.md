# BAG: complete ordered hyperbolic prime cancellation

2026-10-06,22az. Lean proves, for EVERY natural M,

    (log²N/N) * |chiCubicHyperbolicPrimePacket(N,M)| -> 0.

This is the ORIGINAL sharp prime sum on p≠r, |p-r|<|q-r|,
|(p-r)(q-r)|<=Mr. Every V/W factor, phase, physical reciprocal and sharp
band endpoint remains. There is no arithmetic or cancellation premise.
The transpose ordered sector and equal-gap ties are the remaining finite
completion for the full fixed-radius packet; the full cubic tail remains
a separate hard problem.

## New source mechanism

Write d=|p-r|>0,R=Mr/d. In a complete cell, exact frozen periods and
phase-preserving freezing give C M²/(d²logN)+4pi d/(NlogN).
For a truncated cell, some e=1 or2 satisfies |r-eN|<=R. The literal
physical window W is smooth and vanishes at BOTH endpoints1,2. Every
actual integration point has |x-r|<=R and

    |px/(rN)-e| <= 2(d+R)/N,   px/(rN) in[0,4].

Retain W in the amplitude norm. Its source Lipschitz bound pays the
entire truncated cell by32pi L M²/(d²logN)+16pi L M/(NlogN).
Since the integer gap is at least1, a SINGLE source constant C bounds
EVERY actual pair integral by

    C(M+1)² [1/(d²logN) + d/(NlogN)].

No per-anchor short-interval prime estimate is required. The actual
cumulative prime-pair sieve, finite Abel summation and telescoping give
one constant A and threshold valid for EVERY natural D:

    sum_{d<=D} P_N(d)/d² <= A N/log²N,
    sum_{d<=D} d P_N(d) <= A D² N/log²N.

Reindex both gap orientations exactly. Inactive cells are zero; every
active pair has d<=floor(sqrt(2MN)). Summing the displayed bounds proves
the ENTIRE sum of pair-integral NORMS is O_M(N/log³N). Consequently the
literal continuous kernel cancels at the cubic scale. The already proved
actual ordered-prime-packet-to-integral transfer completes the theorem.
This removes the earlier small-gap/edge double limiting argument.

## Lean and audits

- `ChiCubicHyperbolicPrimeEdges.lean:110`,229 lines:
  `exists_chiCubicHyperbolicPrimePairIntegral_all_bound`.
  Final foreground43417 exit0, empty04az log.
- `ChiCubicHyperbolicPrimeMoments.lean:88`,121 lines:
  `exists_chiCubicPrimeGapCount_moment_bounds`.
  Final foreground18316 exit0, empty03az log.
- `ChiCubicHyperbolicPrimeCancellation.lean`,185 lines:
  complete mass definition20, actual bound56, mass limit129, kernel
  limit149, ORIGINAL ordered-packet limit165.
  Final foreground85493 exit0, empty03az log.

All final leaf audits used `lake --old env lean <leaf> -o <olean>`, one
owned foreground process at a time. All three leaves wired once. Imported
axiom audit98243 exit0: all seven public declarations use only propext,
Classical.choice and Quot.sound. Index85131 passed; all seven public API
rows checked. Final authoritative lint11134 exit1:367 large-file warnings
and18 unrelated unreachable modules, no owned BAG finding. Global lint
is not clean. Log `/tmp/bag-hyperbolic-prime-cancellation-lint-22az.log`.
Logs retain
the full commands and failures under `/tmp/bag-hyperbolic-prime-*.log`;
axiom log `/tmp/bag-hyperbolic-cancellation-axioms-22az.log`.
No new axioms, admissions, heartbeat overrides, numerical experiments,
subagents, commits, pushes, full builds or umbrella builds.

This closes the ordered fixed-radius packet. It does not prove the full
cubic/complement, growing moments/cofactors, common-height self-return or RH.
The active RH goal remains open.

23az completion: the transpose and EVERY equal-gap tie are now proved
in Lean. See bag-hyperbolic-prime-full-cancellation.md for the exact full
fixed-radius theorem and audits. The full complementary tail remains open.
