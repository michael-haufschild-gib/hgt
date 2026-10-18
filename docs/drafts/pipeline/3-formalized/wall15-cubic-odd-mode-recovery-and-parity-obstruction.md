# Cubic odd-mode recovery and the parity obstruction

- **ID:** wall15-cubic-odd-mode-recovery-and-parity-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); all 32 public exports audited
- **Wall:** 15, support versus orientation; field research only.
- **Parent:** `wall15-affine-sieve-correlation-phase-components.md`.
- **Statement:** Translation triple data recover every signed odd-order Selberg coordinate, but even-mode examples preserve all affine quadratic data and annihilate every odd-order translation moment while retaining different absolute amplitudes.

## Why this is the next question

The parent package identifies exactly the sign information lost by affine quadratic observations: one sign per component of the nonzero divisibility graph. A useful next result must introduce measurements that change those signs observably. Repeating another quadratic normalization cannot do that.

Use the actual finite divisor response `s_c`, cutoff `N`, period `P=N!`, and existing coordinates `Y_c(q)`. Define the literal translation triple average

`T_c(h,k)=P⁻¹∑(0≤n<P)s_c(n)s_c(n+h)s_c(n+k)`.

## Conjecture loop

**C1 [PROVED; LEAN]: exact double-Fourier readout.** With the unnormalized transform on `Z/PZ`,

`DFT_(h,k) T_c(r,s)=P² Y_c(ord r)Y_c(ord s)Y_c(ord(r+s))`.

Proof: independently reindex the two translation variables. Their two transforms give the product of two source transforms; the base variable supplies the third transform at `−r−s`. The parent arithmetic Fourier bridge supplies each coordinate. All signs and normalizations are checked on the actual finite average.

**C2 [PROVED; LEAN]: unconditional signed recovery at odd modes.** At any odd `q≤N`, choose `r=s=P/q`. Since multiplication by 2 preserves order `q`, C1 reads `P²Y_c(q)³`. Over real weights equality of cubes determines the signed coordinate. Thus equal complete triple data force equality of every odd-order coordinate, including the mean mode. No nonvanishing or connected-support premise is needed. The exact cubic readout and recovery are formalized on the existing arithmetic objects.

**C3 [PROVED; LEAN]: all odd orders still miss a concrete even sector.** The two profiles supported at incomparable modes 6 and 10, with coordinate values `(1,1)` and `(1,−1)`, at every cutoff `N+10`, have identical observations for every affine slope and translation.

Write the literal responses as

`g_±(n)=(2·1_(2∣n)−1)[(3·1_(3∣n)−1) ± (5·1_(5∣n)−1)]`.

Distributivity gives actual weights on divisors `{1,2,3,5,6,10}`. Both satisfy `g(n+15)=−g(n)` and have period 30. Translation of the base variable by 15 therefore negates every odd-order translated product while preserving its complete-period average, forcing that average to zero. The certificate covers every odd length and every natural lag vector; its cyclic-group version covers arbitrary integer lag residues.

Yet `g_+(0)=6` and `|g_−(n)|≤5` for every `n`, inherited from the explicit odd-prime pair. Hence even the joint family of all affine quadratic observations and all odd-order translation observations cannot recover absolute origin amplitude. The shift used here is 15, **not `P/2`**: factorial periods have extra powers of 2, so `P/2` need not negate these sources.

## Result and scope

- The checked literal triple identity and signed odd-mode decoder remove the parent ambiguity on all odd modes.
- The strongest positive survivor is the full triangular-product classification and exact signed odd-mode reconstruction, with a concrete arithmetic parity sector where all odd orders vanish.
- Do not claim full source reconstruction, optimal even observation order, a stability estimate, or Wall 15 closure. The mixed even-order hierarchy remains a separate question.
- A dependency-closed paper proof must precede promotion; formalize the exact survivor before retiring a stronger full-recovery conjecture.

## Dependency-closed paper proof and stronger positive survivor [PROVED HERE]

Write `F(r)=∑n s(n)χ(-nr)` on `Z/PZ`, with `χ` the standard additive character. Reindexing the two lag variables by `u=n+h`, `v=n+k` gives

`∑h,k T(h,k)χ(-hr-ks)=P⁻¹ F(r)F(s)F(-r-s)`.

The checked parent divisor transform is `F(r)=P Y(ord r)`. Additive order is unchanged by negation, so the expression is `P² Y(ord r)Y(ord s)Y(ord(r+s))`, proving C1 with its exact normalization. Since the ordinary finite DFT is invertible, applying injectivity in each lag proves the stronger full classification: **two triple-data functions agree exactly when every displayed triangular coordinate product agrees**. This is an additional exact positive survivor, to be formalized rather than merely recorded as a proof sketch.

For an odd positive `q≤N`, `q∣P`; the residue `r=P/q` has exact additive order `q`. Because `gcd(q,2)=1`, `r+r` also has order `q`. The diagonal double transform is therefore exactly `P²Y(q)³`. Cancel nonzero `P²`; real cubes are injective, so equal triple data imply equal signed coordinates at every odd mode, including `q=1`. This proves C2 with no assumptions on other coordinates.

For C3, explicitly set
`w_t(1)=1+t`, `w_t(2)=-2(1+t)`, `w_t(3)=-3`, `w_t(5)=-5t`, `w_t(6)=6`, `w_t(10)=10t`, and all other coefficients zero. At cutoff `N+10`, its multiples coordinates are `Y(6)=1`, `Y(10)=t`, all others zero: the sums at 1, 2, 3 and 5 cancel, and no divisor outside `{1,2,3,5,6,10}` receives a term. Since neither 6 nor 10 divides the other, changing `t=1` to `t=-1` preserves every comparable product, hence every affine quadratic datum by the parent theorem.

The literal divisor response factors as
`s_(w_t)(n)=(2·1_(2∣n)-1)[(3·1_(3∣n)-1)+t(5·1_(5∣n)-1)]`.
Translation by 15 preserves divisibility by 3 and 5 and exchanges the two parity classes, so it negates this response. Every supported modulus divides both 30 and `(N+10)!`; therefore this law also holds on the actual factorial residue group. For any odd length `m=2j+1` and any lag vector on that group, shifting the base variable by 15 negates the product of its `m` source values. This shift is a permutation, so the complete-period sum equals its own negative and is zero. Natural lag representatives give the literal integer sums; arbitrary integer lags reduce to the same residue lags. The proof uses no enumeration of a period.

At the origin, `s_(w_1)(0)=6`. For `t=-1`, the bracket is `3·1_(3∣n)-5·1_(5∣n)`, whose four symbolic cases are `0,3,-5,-2`; the parity factor has absolute value 1. Hence `|s_(w_-1)(n)|≤5` everywhere. The joint family of all affine quadratic observations and all odd translation moments cannot determine absolute origin response, even up to translated sign. Its strongest positive survivors are the exact triangular-product classification and signed odd-mode readout, not the negation alone.

These dependency-closed paper arguments now have exact Lean certificates for the actual finite averages, real casts, coordinate profile and all-length odd-moment cancellation. No minimal even observation order or global phase reconstruction is claimed.

## Persistent plan and write scope

1. [complete] Reread current objective, both field READMEs and Wall 15; verify unchanged parent sources; refresh the bounded corpus frontier and prove C1–C3 on paper.
2. [complete] Fourier/triple, parity-lift, and actual-real-object leaves implemented and checked. APIs verified in `/tmp`; one owned foreground Lean process at a time.
3. [complete] All three final named original-source checks passed without diagnostics. All public signatures, definition bodies and axioms audited; no-go survivor audited; umbrella wiring, index/discovery/lint, protected hashes, memory and scratch cleanup verified.

`update_plan` is unavailable; this card is the durable tracker. Owned write scope: this card and its stage move, new field leaves, their umbrella imports, generated index, the specific failed-route and next-conjecture cards, incoming links on the two predecessor cards, and task-specific memory. Concurrent research leaves/cards/ledgers and all three protected files remain untouched.

## Exact Lean certificate

- [SieveTripleFourier.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/SieveTripleFourier.lean): 10 public exports; final original-source check passed without diagnostics (`/tmp/bsu-cubic-fourier-final-r1.log`, exit 0). Covers double-transform injectivity, exact triple spectrum, complete triangular-product classification, odd-order diagonal cubic readout and all-length anti-period cancellation.
- [ParityLiftedSieveMoments.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/ParityLiftedSieveMoments.lean): 6 public exports; final original-source check passed without diagnostics (`/tmp/bsu-cubic-parity-final-r1.log`, exit 0). Covers the exact 6/10 coordinate profile, complete affine indistinguishability, literal parity factorization and vanishing of every odd translated moment.
- [CubicSievePhaseRecovery.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/CubicSievePhaseRecovery.lean): 16 public exports on the existing real objects. First original-source check passed with one unused-binder warning; after removing that binder, the final named check passed with no diagnostics (`/tmp/bsu-cubic-main-r2.log`, exit 0). It imports the existing actual sieve definitions and checked bridges; no copied proxy definitions occur in production.

All 32 public signatures and axiom closures passed `/tmp/bsu_cubic_public_audit.lean`, exit 0, no warnings (`/tmp/bsu-cubic-public-audit-r1.log`). They comprise 25 theorems and 7 definitions; every axiom closure uses only `propext`, `Classical.choice`, `Quot.sound`. All 7 exported definition bodies and 3 underlying actual definitions (`sieveSeq`, `selbergMultiplesCoord`, `AffineSieve.affineMoment`) were printed and inspected against current source. Full manifest: `/tmp/bsu-cubic-phase-manifest.json`; process/source evidence: `/tmp/bsu-cubic-phase-session.json`. No final checked source changed. The main check used the prior verified isolated dependency workspace and compiled the absolute original source with `lake --old env lean -j 1 --root=/Users/michael/Documents/code/hgt/formal`; only four owned supporting artifacts were copied into that cache, and two owned main artifacts copied back, with byte verification. All three imports occur exactly once; no umbrella build ran.

Key actual-object theorems in `GaloisForLFunctions.BiScaleUncertainty.SieveMoments`: `doubleDFT_tripleMoment`, `tripleMoment_eq_iff_triangles`, `tripleMoment_odd_mode_readout`, `tripleMoment_recovers_odd_coordinates`, `coordinate_parityReal`, `translatedMoment_parityReal_zero`, `exists_same_affine_odd_data_distinct_absolute_origin`, and `no_absolute_origin_decoder_from_affine_and_odd`. The negative statement uses the entire dependent family of all odd lengths and lag vectors together with the entire affine-data function.

Scoped lexical discovery inspected all 44 declarations (13/14/17 by leaf), including exactly all 32 public exports, with no pagination gap. Evidence: `/tmp/bsu-cubic-discovery-{fourier,parity,main}.json`. Both field README hashes and the wall-ledger hash match this turn's initial snapshot; all three remained read-only. Initial lint found only two stale generated files during concurrent work. After refreshing the generated index, final `scripts/formal_tools.py lint --check-generated` **passed**, exit 0 (`/tmp/bsu-cubic-lint-r2.log`); 381 existing large-file warnings remain, with no errors or proof-debt findings. The final index refresh also exited 0 (`/tmp/bsu-cubic-index-r2.log`).

All owned processes are terminal. Three obsolete prototype `.lean` files were moved without overwrite into `/tmp/bsu-cubic-phase-archive-20261018/`; final audit source, logs, manifests, reproduction scripts and verified dependency workspace remain. Incoming links on both predecessor cards were updated for the stage move. No checked Lean source changed during this closure work.

Cross-session memory saved as `biscale/wall15-cubic-recovery-and-parity-obstruction`. This package is complete; Wall 15 and the all-walls goal remain open.

The rejected full-recovery route is recorded with its exact positive survivor in [the failed-route card](../5-failed/wall15-full-recovery-from-affine-and-odd-moments.md). Wall 15 remains open.

The [sixth-moment recovery follow-up](../3-formalized/wall15-sixth-moment-recovery-in-the-even-prime-pair-sector.md) is now separately formalized: sharp degree-six recovery for the two-mode sector, with 20 audited exports. Wall 15 remains open.

## Corpus evidence and constraints

Search: `sieve triple correlation odd mode signed recovery parity`, scoped to BiScaleUncertainty. It returned no lexical hit and 20 candidates plus 20 source arguments, all inventories inspected. No direct triple-sieve recovery result appeared. Coverage snapshot is older than the current generation; semantic coverage is unmeasured. Evidence: `/tmp/bsu-affine-cubic-frontier.json`. This is a bounded internal audit, not an external novelty claim. Recheck the frontier before starting implementation.

Refreshed searches: `/tmp/bsu-cubic-frontier-r1.json` (same BiScale query), `/tmp/bvi-cubic-frontier-r1.json` (`sieve higher correlation parity sign recovery`), and `/tmp/bsu-cubic-fourier-deep-r1.json` (`finite cyclic triple correlation Fourier odd additive order cube`). All 20 candidate and 20 source-argument inventories per search were inspected. The deep search was partial; its single proposed ingredient set concerned cyclic norm quotients and does not supply this theorem. All coverage reports are older snapshots, semantic coverage unmeasured, background refresh incomplete. No absence or external novelty claim. Existing affine source hashes match their completed certificate.

The broadened lexical query `bispectrum tripleCorrelation --any` found one existing theorem, `thirdMoment_eq_resonance` in `RHTower.ThirdMomentResonance`; its statement and proof were inspected. It identifies a single continuum third moment with a sum of additive resonances. The present statement instead concerns the full two-lag finite divisor-sieve data, exact Selberg-coordinate recovery, and an all-odd-order arithmetic counterexample. That older generic resonance fact is acknowledged, not counted again or developed into an RH route. The concurrent BVI gcd-orbit module proves ordinary periods, not the required anti-periodic odd-moment classification.

Use the actual `sieveSeq` and `selbergMultiplesCoord` objects; no abstract analytic premises, numerical experiments, added axioms, hgtl7, RH work, umbrella builds, or heartbeat increases. Preserve concurrent BVI work and the read-only field READMEs/wall ledger.

## Gates

- [x] 0 → 1: refreshed frontier and full applicability audit.
- [x] 1 → 2: dependency-closed paper proof of the exact positive survivor and obstruction.
- [x] 2 → 3: all final named leaves and public signatures/axioms checked; wiring and discovery verified. Repository lint status recorded separately.
- [ ] 3 → 4: publication audit.

## Log

- 2026-10-18: proposed during the parent package's final actual-object check. No theorem on this card has yet been counted or certified in Lean.
- 2026-10-18: previous goal turn classified Progress. Selected Wall 15 again because exact phase-component obstruction supplies a concrete next mechanism. Full paper derivation above adds complete triangular-product classification to the original odd-mode recovery target. Formal certificate in progress; Wall 15 remains open.
- 2026-10-18: **Progress**. Stage 3 certificate complete: 32 public exports audited; all final named checks and repository lint passed. Full recovery from affine plus all odd moments retired with its strongest positive survivor formalized. Sixth-moment follow-up queued as a conjecture. Wall 15 remains open.
- 2026-10-18: all three final original-source checks passed without diagnostics; all 32 public signatures and standard-axiom closures audited, plus all 10 definition bodies. C1–C3 and the stronger full triple-data classification formalized. Turn outcome: **Progress**; Wall 15 open, research goal active.
