# Arithmetic Counting Positivity

- **ID:** ACP-FOUNDATIONS
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../../../../docs/reports/review-2810/obstacles-summary.md, sections 2.7–2.8
- **Statement:** Develop independent arithmetic counts producing selective positivity, including all five mechanisms and structural questions in the source report.

## Goal

Own folder and umbrella `formal/GaloisForLFunctions/ArithmeticCountingPositivity`;
foundational README; significant unconditional Lean contributions; full research
scope preserved until the stated mechanisms and questions are resolved. Do not
use `hgtl7`. No numerical experiments or trusted computation proofs.

## Gates

- [x] 0 → 1: source report read; mathematical scope and countermodel battery specified.
- [ ] 1 → 2: dependency-closed paper proofs for individual contributions.
- [ ] 2 → 3: corresponding Lean theorems, foreground `lake --old env lean` audits,
  transitive `#print axioms` checks, umbrella wiring.
- [ ] Complete programme: selective overlap; arithmetic Herglotz; integer-side
  auxiliary counting; finite-rank renormalization; exact inertia counting;
  five structural questions answered; all calibrations and exhaustion proved.

## Approach

Start from exact arithmetic incidence counts, track the signed correlation they
retain, and audit parity twisting before any global positivity claim. Search the
corpus for the sharp walk gap, counting constructions and previously proved
obstructions. Give every new inequality an explicit scope and positive survivor.

## Current evidence

Foundational README and four-module first contribution written. The uniform
squared-correlation transfer, its sharp geometric projection bound, exact
prime-parity pairing, bounded boundary error, exact harmonic density and
positive prime-two gap are proved. Every submaximal threshold admits a
nontrivial completely multiplicative prime flip with untwisted polar matching
but a negative test for the literal complete Weil functional.

All 28 theorem axiom audits passed with only `propext`, `Classical.choice`,
and `Quot.sound`. All four canonical check logs have no diagnostics; the fourth
finished successfully. The final check caught a singleton-sum
simplification in the prime-three example, now fixed and rechecked.

The next bridge is the harmonic Ramanujan coordinate of prime parity:
an exact Mobius divisor identity and bounded decimation error imply that all
nontrivial conductors coprime to the flipped prime have zero limiting
correlation. Its closed proof is in
`../3-formalized/arithmetic-counting-prime-parity-ramanujan.md`. All seven
theorems in `PrimeParityRamanujanCoordinates.lean` now pass the kernel and
transitive axiom audit. Its olean was written because the next harmonic
normalization module imports it. The canonical final source check also passed.

The valuation-box branch has formalized the maximal-gap theorem for primes
at least 11 in `LargePrimeFlipsAttainTheMaximalGap.lean`; its paper card is
`../3-formalized/arithmetic-counting-maximal-gap-rigidity.md`. The user
confirmed this as the intended endpoint and rejected the redundant independent
endpoint for primes at least 41. That draft and its separate two-mode helper
have been removed. Preserve the other researcher's valuation-box work.

The retained independent contribution is the exact bridge from parity counts
to squared coordinates on actual prime eigenlines. It is now formalized in
`HarmonicParitySpectralCoordinates.lean`: all 14 public theorems pass the
transitive axiom audit, and the canonical installed-source check exited zero
without diagnostics. Its paper and durable audit are in
`../3-formalized/arithmetic-counting-harmonic-spectral-coordinates.md` and
the adjacent audit file. This closes six own leaves, with 49 public theorems.

The arbitrary finite-prime count is also formalized:
`FinitePrimeFlipsHavePositiveHarmonicDensity.lean` proves the product density,
the exact insertion recurrence, bounded error, limit and paid gap. Its six
public theorems and final canonical source check passed. Its first required
olean built for the exhaustion leaf. There are now seven closed own leaves
and 55 audited public theorems. The subsequent exhaustion leaf has also
passed all five axiom audits and its final canonical source check, closing
eight own leaves and 60 public theorems.

Existing worktree contains other researchers' changes; preserve them. The source report
is being updated concurrently: its inertia/mollifier proposal has changed into
a displacement-sensitive census question. Recheck current text and the relevant
counterexample before choosing that branch.

## Open obligations

All producer mechanisms remain open. An RH-equivalent or quasi-RH-equivalent
estimate is not an available input. Do not close this card merely because a
finite arithmetic construction or README is finished.

## Verification handoff

- Fourteen own leaves are installed, individually checked, axiom-audited and
  wired into `ArithmeticCountingPositivity.lean`, with 100 public theorems.
  That umbrella is imported by `MainTheorems.lean`; no umbrella was compiled.
- Eleven own stage-three cards and adjacent `-audit.txt` files preserve proofs,
  exact commands, installed-source hashes and actual transitive axiom output:
  `arithmetic-counting-pole-angle`, `arithmetic-counting-prime-parity-ramanujan`,
  `arithmetic-counting-harmonic-spectral-coordinates`,
  `arithmetic-counting-finite-prime-density`,
  `arithmetic-counting-finite-flip-exhaustion`, and
  `arithmetic-counting-small-prime-gap-boundary`, and
  `arithmetic-counting-parity-spectral-mass`, and
  `arithmetic-counting-cofinite-flip-exhaustion`, and
  `arithmetic-counting-parity-secular-data`, and
  `arithmetic-counting-finite-secular-criterion`, and
  `arithmetic-counting-parity-resolvent-limit`.
  Every final source check exited zero without diagnostics. All 100 audits
  use only `propext`, `Classical.choice`, `Quot.sound`.
- The small-prime leaf proves every gap is at most `p log(p)/(p+3)`,
  excludes maximality for primes below eleven, and combines with the
  independent large-prime theorem to prove maximal-gap attainment iff
  `11 <= p`. Its scratch check 49297 and canonical check 78204 both exited
  zero. Its paper is now in stage three and its durable audit is saved.
- Preserve the other researcher's `LargePrimeFlipsAttainTheMaximalGap.lean`
  and its stage-three card. Its existing olean was imported, not rebuilt.
  The combined cutoff equivalence passed its own transitive axiom audit.
  The user rejected the redundant prime-41 endpoint; do not recreate it.
- Own required oleans exist for the angle, sparse-flip, parity-pairing,
  Ramanujan-count, spectral-coordinate and finite-density leaves. The
  spectral-coordinate build 55169 exited zero with no diagnostics. No
  olean was needed for the small-prime upper-bound leaf.
- The spectral mass paper is formalized in
  `../3-formalized/arithmetic-counting-parity-spectral-mass.md`.
  The exact finite Ramanujan profile equals parity outside `p^K | n`,
  and equals `c_p(-1)^K` on that fibre. Its normalized squared error is
  `((1+c_p^2) H_floor(N/p^K)-2c_p S_p(floor(N/p^K)))/(p^K H_N)`.
  Therefore it is at most `4p/(p+1)^2 * p^(-K)` uniformly over positive
  horizons, and converges to that bound as the horizon grows. The proof
  uses the existing multiplier trichotomy and exact divisibility counts.
- The parity-tower scratch passed check 19175 with all eight
  transitive axiom audits standard, including exact coefficient mass and
  its limit one. The installed leaf is
  `PrimeParityIsExhaustedByItsRamanujanTower.lean`. Its canonical source
  check 25706 exited zero without diagnostics. The umbrella and README
  are wired, the durable audit is saved and the paper is in stage three.
  Its scratch and logs are cleaned. Its first required olean subsequently
  passed build 66596 for the secular-data leaf.
- The cofinite paper is `../3-formalized/arithmetic-counting-cofinite-flip-exhaustion.md`.
  It proves the explicit bound `|S_(Liouville * finiteFlip F)(N)| <= 2/c_F`,
  the resulting harmonic squared-distance limit two, and greatest gap
  exactly zero from the existing bounded-correlation criterion. The
  finite-exhaustion olean build 25795 passed. Scratch formalization
  `/tmp/acp-cofinite-exhaustion-check.lean` passed check 9093, with all
  twelve transitive axiom audits standard. The installed leaf is
  `CofinitePrimeFlipsHaveZeroGap.lean`, wired into the umbrella and README.
  Its final source check 93963 exited zero without diagnostics. The
  durable audit is saved, its paper promoted, and scratch/logs cleaned.
  This closes eleven own leaves and 83 audited public theorems.
- The exact-gap target now has a dependency-complete stage-two paper:
  `../2-fully-proven/arithmetic-counting-small-prime-secular-gap.md`.
  It identifies the greatest gap for every prime as the minimum of the
  secular root and `2 log 2`, and for primes below eleven as the root itself.
  Its eight-endpoint Lean draft remains unverified.
- `TheParityTowerHasAUniqueSecularRoot.lean` has five audited public endpoints:
  exact tower energy, coefficient squares, unit mass, unique root and strict
  two-mode upper bound. Scratch 71369 and canonical 68241 passed; its first
  required olean build 41368 passed. Stage-three paper and durable evidence
  are `arithmetic-counting-parity-secular-data` and its adjacent audit.
- `FiniteReciprocalMassControlsTheHyperplane.lean` has six audited public
  endpoints: diagonal iff, reciprocal tail bound, negative witness,
  distinguished-index iff, Hermitian iff and eventual packet-limit principle.
  Scratch 7621, canonical 76613 and first required olean 42625 passed.
  Stage-three paper and evidence are `arithmetic-counting-finite-secular-criterion`.
  Both leaves are wired into the umbrella/README; their scratch/logs are cleaned.
- `TheParityTowerDeterminesTheFiniteResolvent.lean` has six audited public
  endpoints: explicit Möbius coefficient, actual eigenline sequences at
  horizons N+1, unique ground spectral count, strict energy monotonicity,
  first-excitation lower bound, and convergence of the entire actual finite
  resolvent to the parity secular series. Its private packet lemma controls
  every omitted eigenline by omitted squared mass divided by a denominator gap.
  Scratch check 99113 and canonical check 10211 passed with standard axioms
  and no warnings. Stage-three paper and durable evidence are
  `arithmetic-counting-parity-resolvent-limit`. Umbrella/README are wired,
  and scratch/check logs cleaned. The coefficient calculation reuses
  `TransHorizonIncidenceMechanics.mul_moebius_apply_prime_pow`.
  Its first required olean build 60848 passed with no diagnostics; durable
  evidence is saved and its log cleaned. The first required small-prime
  boundary olean build is running in session 5632, log
  `/tmp/acp-small-prime-boundary-olean.log`. Resume before another Lean
  command, then check the final exact-gap draft. Both dependencies were
  confirmed missing before their first builds.
- The eight-endpoint final draft is `/tmp/acp-exact-parity-gap-check.lean`.
  It proves greatest gap `min (2 log 2) (primeParitySecularRoot p)`, classifies
  every real gap, locates the root below the ceiling iff p<11, gives the
  exact small-prime greatest gap, makes the two-mode upper bound strict,
  and states the normalized root equation as
  `HasSum (4/(phi(p^(k+1))*(D_(k+1)-alpha))) (1/alpha)`.
  The sign isometry, finite resolvent iff, root signs, endpoint attainment,
  and necessary upper bound are all written but unverified. Two imports
  require the new resolvent olean and small-prime boundary olean. The third
  bounded-variation source import has an existing olean; never rebuild it.
  The rewritten paper is now in stage two; the old stage-one target and
  temporary paper were removed after promotion. Do not claim these final
  eight endpoints pass yet.
- The next finite-set generalization is recorded as a conjecture in
  `../0-backlog/arithmetic-counting-finite-prime-secular-gap.md`. It targets
  the explicit smooth-conductor weights `c_F^2 4^omega(m)/phi(m)` and an
  exact finite-set root. It has neither a closed paper proof nor Lean proof;
  finish the current eight-endpoint single-prime audit first.
- The newer source report was fully reread in chunks. It now emphasizes
  arithmetic Krein--Langer theory, coalescent pair counts, index-carrying
  completion and structural precision, alongside selective transfer and
  integer-side auxiliary counts. Other researchers own the HKT and full
  separated-Weil spectral branches. The original counting programme stays
  active; finite-count and prime-spectrum results do not finish it.
