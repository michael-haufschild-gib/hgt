# Wall 15: sharp sixth-moment recovery (2026-10-18)

Classification: Progress. Wall 15 and the all-walls goal remain open. Follow-up to `mem:biscale/wall15-cubic-recovery-and-parity-obstruction`.
No RH research, numerical experiments, period enumeration, unproved analytic premises, added axioms, heartbeat changes, umbrella/full builds, subagents, commits or pushes. Preserve concurrent workers' records/counters.

## Exact result on actual divisor sieves
At cutoff N+10 define actual weights
c_(a,b)(1)=a+b, c(2)=-2(a+b), c(3)=-3a, c(5)=-5b, c(6)=6a, c(10)=10b, zero elsewhere.
Production definition evenPairReal is the literal linear combination a*parityReal 0+b*(parityReal 1-parityReal 0). evenPairReal_one identifies a=1 with the prior family.
Existing multiples coordinates are exactly Y6=a,Y10=b, zero elsewhere.
Actual response is parity(n)*(a R3(n)+b R5(n)), with parity(n)=1 if 2 divides n and -1 otherwise, and Rp(n)=p*1_(p|n)-1.

Complete affine quadratic data are equal iff a²=c² and b²=d².
Every odd translated moment vanishes for every a,b and every lag vector, by anti-period 15.
Every translated quartic moment is invariant under b -> -b, for every four-lag vector. Likewise degree two; all moments of degree <=5 are invariant. No numerical period enumeration: exact CRT factorization kills the lone centered prime factor in every sign-sensitive quartic term.
The general even translated-moment bridge is exact: a product of lag parity signs times the normalized sum over ZMod 3 × ZMod 5.
The literal zero-lag sixth moment is
22a^6 + 360a^4b^2 + 480a^3b^3 + 1560a^2b^4 + 820b^6.
Its sign-flip difference is 960a^3b^3.
Affine data plus this ONE sixth moment determine (a,b) up to ONE common sign, including all zero cases. This is the exact iff evenPair_recovery_iff, not an assumed spectral interface.
Explicit weights (1,1) and (1,-1) have all affine and all through-five translated data equal, while their sixth moments differ by 960. Degree six is sharp for this sector and observation family. The same pair is also invisible to the entire odd hierarchy.

## Certificate
New sources in formal/GaloisForLFunctions/BiScaleUncertainty:
- EvenPrimePairMomentCalculus.lean: 7 public exports, 12 declarations.
- SixthSievePhaseRecovery.lean: 13 public exports, 16 declarations.
Namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.
Total 20 public exports = 18 theorems and 2 definitions; complete discovery covers all 28 declarations.

Final ORIGINAL named-source checks passed exit 0, no diagnostics, via lake --old env lean -j 1:
- /tmp/bsu-sixth-calculus-final-r2.log
- /tmp/bsu-sixth-main-final-r1.log
Compiled absolute original sources with --root=/Users/michael/Documents/code/hgt/formal from the prior verified /tmp/bsu-two-lag-workspace. Toolchain and original-source symlink rechecked; eight predecessor .olean/.ilean bytes matched root. Four owned new artifacts copied back with byte checks. No source changed after final checks.
Both imports wired exactly once in formal/GaloisForLFunctions/BiScaleUncertainty.lean.
All 20 public signatures and axiom closures audited by /tmp/bsu_sixth_public_audit.lean:
 /tmp/bsu-sixth-public-audit-r1.log, exit 0, no diagnostics.
All closures use only propext, Classical.choice, Quot.sound.
All seven definition bodies inspected: new residueRow/evenPairReal and existing translatedMoment, parityReal, sieveSeq, selbergMultiplesCoord, AffineSieve.affineMoment. They are the literal arithmetic objects.
Source hashes, inventories, axiom closures, artifacts, links and gate evidence:
 /tmp/bsu-sixth-phase-manifest.json
 /tmp/bsu-sixth-phase-session.json
Scoped lexical discovery: /tmp/bsu-sixth-discovery-{calculus,main}.json, all 28 declarations / all 20 exports, no pagination gap.

IMPORTANT FINAL REPOSITORY GATE:
Index r2 PASSED exit 0 (/tmp/bsu-sixth-index-r2.log).
Lint --check-generated r2 FAILED exit 1 (/tmp/bsu-sixth-lint-r2.log) with one unrelated error:
owned module unreachable from RHTower umbrella:
 GaloisForLFunctions.RHTower.GammaThetaFullSupportCreation.
381 existing size warnings; no owned wiring or proof-debt errors.
Initial lint had six unrelated wiring errors; concurrent wiring changed, justifying one rerun, which left the one above. Do not claim repository lint passed. Do not edit the unrelated RH module or its umbrella to bypass this; current goal excludes RH work.
All owned Lean/search/index/lint handles terminal.

## Durable records and cleanup
- Stage 3: docs/drafts/pipeline/3-formalized/wall15-sixth-moment-recovery-in-the-even-prime-pair-sector.md
- Failed through-five route with strongest positive survivor:
 docs/drafts/pipeline/5-failed/wall15-recovery-from-affine-and-through-five-moments.md
- Next conjecture:
 docs/drafts/pipeline/0-backlog/wall15-sixth-order-recovery-for-finite-odd-prime-mode-families.md
Both direct predecessor cards and next-card parent links updated.
Three obsolete Lean prototypes moved without overwrite to /tmp/bsu-sixth-phase-archive-20261018/.
Final audit source, logs, manifests, scripts and verified dependency cache retained.
Both field README hashes and walls-ledger hash unchanged:
 BSU dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933
 BVI fd49791f7d68e197372bfb55bf0289d3c19d24a39bfdb67eb8881d76a0b869e9
 ledger 2a4421e0c14fdc8ed9e2f107d79b941e5407945c12abb2b1e1fc99ed40267630
Serena find_symbol rejected the new Lean path as ignored; direct file edits used. update_plan unavailable; pipeline card is durable tracker.

## Next conjecture, NOT certified or counted
For a finite set S of odd primes, actual weight sum a_p[delta1-2delta2-p*deltap+2p*delta2p] has response parity(n)*sum a_p Rp(n).
Conjecture full affine plus full sixth-lag data determine all coefficients up to common sign, including empty/zero support; all through-five data remain independently sign-blind.
Mechanism: three frequencies P/(2p), P/(2p), (p-2)P/(2p) each have order 2p and sum to P/2. Pair with negatives of q's triple to get a six-frequency resonance exposing a_p^3*a_q^3. Audit normalization (expected P^5 for the anchored five-lag transform), then recover pair products by cube injectivity and a rank-one real Gram classification.
Proposed three-mode scalar counterexample S={3,5,7}: positive u³=5,v³=2; compare (1,u,-v) and (1,-u,v). Coordinate squares agree, and sixth zero-lag cross terms cancel since gamma5*u³=12*5=60=30*2=gamma7*v³, gamma_p=(p-1)(p-2). Not common-sign multiples. Requires actual three-prime CRT proof, not certified yet. Positive survivor must be full lag-data recovery.

Frontier evidence: /tmp/bsu-sixth-frontier-r1.json, /tmp/bsu-sixth-crt-deep-r1.json, /tmp/bsu-sixth-next-frontier-r1.json. All returned 20 candidate/20 source inventories inspected; deep ingredient set was unrelated cyclic-generator material. partial=false, older coverage snapshots, semantic coverage unmeasured, background refresh unfinished. No global absence or external novelty claim. Refresh before next implementation.
