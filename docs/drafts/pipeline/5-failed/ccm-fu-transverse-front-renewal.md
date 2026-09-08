# CCM-FU: transverse cost of advancing the prime front

- Stage: 5-failed — sign candidate numerically falsified; exact positive survivor formalized.
- Full objective: actual signed source → renewable reserve → exhaustive selection → uniform O(M) Abel bound → RH.
- Frontier map: read only.

## Frozen question

Write T(M,P)=Q(M,P)−F(M,P,empty)^2−F(M,P,{2})^2.
The existing source helpers act in these two receiving coordinates.
To advance the unbounded quotient front, test whether inserting the
smallest remaining prime other than two always has nonpositive T gain
when P contains all primes below fifteen except two and leaves the helper
windows unused. This sign claim is a candidate, not a theorem or RH proof.
Its motivation is that it would let the prime front advance without
spending the transverse energy removed by two-coordinate helpers.

The independent derived target is exact separation: every child-inactive
two-coordinate helper block subtracts its copied-square reserve from T;
for a different available prime q≠2, that helper block leaves the T gain
of inserting q exactly unchanged. The source identity, if proved, means
head balancing cannot improve the sign tested here. It gives an exact
accounting rule whether the candidate sign survives or fails.

## Frozen experiment

Only on the supplied RunPod host. Four independent cutoff jobs at
M=512, 2048, 8192, 32768, with 64 deterministic states per cutoff.
Prime 17 is retained and is the smallest remaining prime other than 2.
Every state includes {3,5,7,11,13}; additional processed primes are chosen
from 19≤p≤floor(M/15), preserving all source windows above M/15.
Include empty and complete extra cores, initial segments, alternating
cores, and seeded Bernoulli cores of densities 1/4,1/2,3/4.

Measure the exact-source floating-point transverse change for prime 17,
its two receiving fibres, the complete energy, and all paired terms that
produce the change. The channel formula is the corpus's literal quotient
block sum of the prime-free divisor defect. No saved low-cutoff state
screen is extended or reused: this tests a different projected energy
and an unbounded-quotient front, including birth of triple supports beyond
17*19*23.

A change above 1e−10 times max(1,Q_empty) flags a violation. Audit the
smallest-cutoff flagged state independently at 80 decimal digits with
the original time-sum formula; do not admit numerical results to Lean.
If no violation appears, retain the candidate as unproved; do not infer
an all-state sign law. If one appears, extract its signed paired mechanism
and retain the exact separation law as the positive survivor.

Primary screen: four workers, numerical-library threads one, internal
90-second deadline and external 100-second limit. No enlargement, repeated
range scan or automatic tuning. Audit separately bounded 90 seconds.
Download source, output and hashes; remove all owned remote files/workers.

## Outcome and strongest positive survivor

The frozen screen of 256 states found positive prime 17 transverse gains in
43/64 states at 2048, 29/64 at 8192, and 9/64 at 32768; all 64 at 512 had negative
gain. The first flagged state is the fixed core itself, with no additional
processed primes. Its independently reconstructed 80-digit gain is
288.2644197923681488135... at M=2048. The original head and {2} coordinate
are already small. Full measurements, paired terms, original-time-sum
audit and provenance are in the [computation record](../2-fully-proven/computations/ccm-fu-transverse-front-2026-09-08/README.md).

Negative status: high-precision numerical falsification only; not a
symbolic interval proof and not a Lean counterexample. This does not
exclude another next-prime choice, a cumulative transverse budget, or
special cofinal cutoff families. No larger or repeated screen is planned.

Positive survivor: the [exact transverse reserve commutation theorem](../3-formalized/ccm-fu-transverse-reserve-commutation.md)
proves that every admissible two-coordinate helper block subtracts a fixed
copied-square reserve from the complementary energy. It leaves every
subsequent transverse energy increment unchanged, for an arbitrary
additional finite prime core excluding two and the helpers. The exact
paired-cost formula identifies all terms that still require a budget.
This is stronger than one-step commutation and uses no numerical result.
Its paper proof is dependency-closed and its six Lean theorems are checked.

The serious salvage pass therefore retains exact separation and cumulative
cost accounting. The original universal nonpositive-step claim is not
weakened and relabelled as the main conjecture. RH remains open.
