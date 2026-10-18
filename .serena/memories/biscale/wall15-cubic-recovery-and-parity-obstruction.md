# Wall 15: cubic recovery and parity obstruction (2026-10-18)

Classification: Progress. Wall 15 remains open; all-walls goal remains active. No RH work, numerical experiments, added premises/axioms, full builds, heartbeat changes, commits, pushes, or subagents. Neither field README nor docs/reports/walls-ledger.md was modified. Do not update the independent BVI worker's progress counter.

## Exact mathematics
Use the existing real finite divisor sieve s_c(n) = sum_{1<=d<=N,d|n} c(d), existing multiples coordinate Y_c(q) = sum_{1<=d<=N,q|d} c(d)/d, and P=N!.
The literal two-lag triple average T_c(h,k)=P^{-1} sum_{0<=n<P} s_c(n)s_c(n+h)s_c(n+k) has exact unnormalized double DFT P^2 Y_c(ord r)Y_c(ord s)Y_c(ord(r+s)).
Equality of every triple observation is equivalent to equality of every such triangular coordinate product.
For each positive odd q<=N, r=s=P/q reads P^2 Y_c(q)^3. Thus complete triple data recover the signed real coordinate at every odd order, including the mean. No nonvanishing, connectedness, or extra support premise; all natural cutoffs, including zero, are covered.

The even-mode counterexample at each cutoff N+10 has weights:
w_t(1)=1+t, w_t(2)=-2(1+t), w_t(3)=-3, w_t(5)=-5t, w_t(6)=6, w_t(10)=10t, zero elsewhere.
Only multiples coordinates Y6=1, Y10=t survive.
For t=+1 and -1, all existing affine quadratic moments agree, by the prior exact phase classification.
Actual response g_t(n)=(if 2 divides n then 1 else -1)*[-(1+t)+3*1_{3|n}+5t*1_{5|n}].
It satisfies g_t(n+15)=-g_t(n) on the actual factorial residue group.
Translation by 15 permutes that group, so every odd-length translated moment vanishes, for every lag vector and every t. The cyclic lemma covers arbitrary residue lags; the real bridge covers natural lags (integer lags reduce modulo P).
Yet g_1(0)=6 and |g_-1(n)|<=5 for every n. Hence the entire affine family plus the infinite hierarchy of all odd translated moments does not recover absolute origin response, even modulo translated global sign.
Strong positive survivor audited before route retirement: complete triangular-product classification plus exact signed odd-coordinate recovery.

## Production and verification
Three new leaves in formal/GaloisForLFunctions/BiScaleUncertainty/:
- SieveTripleFourier.lean: 10 public exports.
- ParityLiftedSieveMoments.lean: 6 public exports.
- CubicSievePhaseRecovery.lean: 16 public exports.
Total 32 public exports = 25 theorems + 7 definitions. Namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.
All final named ORIGINAL-source checks via lake --old env lean -j 1 passed, exit 0, no diagnostics:
- /tmp/bsu-cubic-fourier-final-r1.log
- /tmp/bsu-cubic-parity-final-r1.log
- /tmp/bsu-cubic-main-r2.log
The main check compiled the absolute original source with --root=/Users/michael/Documents/code/hgt/formal from the prior verified /tmp/bsu-two-lag-workspace cache (same toolchain, original-source symlink, existing full dependency closure). Four owned supporting artifacts copied in and two owned main artifacts copied back, all byte-verified. No umbrella/full build.
All 32 public signatures and all axiom closures audited in /tmp/bsu_cubic_public_audit.lean, log /tmp/bsu-cubic-public-audit-r1.log, exit 0. Only propext, Classical.choice, Quot.sound; no sorryAx.
Printed and inspected all 7 exported definition bodies plus actual sieveSeq, selbergMultiplesCoord, AffineSieve.affineMoment. These are literal existing arithmetic objects, no production proxy definitions.
All three imports wired exactly once in the BiScaleUncertainty umbrella.
Scoped lexical discovery inspected all 44 declarations (13/14/17), exactly all 32 public exports, no pagination gap.
Final index refresh and scripts/formal_tools.py lint --check-generated both passed exit 0:
 /tmp/bsu-cubic-index-r2.log and /tmp/bsu-cubic-lint-r2.log.
381 existing large-file warnings; no errors, stale generated errors, or proof-debt findings.
Certificate verifier /tmp/bsu_cubic_verify_certificate.py passed.
No checked source changed after final verification. All owned process handles terminal.

## Durable records
- Stage 3 theorem card: docs/drafts/pipeline/3-formalized/wall15-cubic-odd-mode-recovery-and-parity-obstruction.md
- Failed route with positive survivor: docs/drafts/pipeline/5-failed/wall15-full-recovery-from-affine-and-odd-moments.md
- Next conjecture: docs/drafts/pipeline/0-backlog/wall15-sixth-moment-recovery-in-the-even-prime-pair-sector.md
- Evidence: /tmp/bsu-cubic-phase-manifest.json and /tmp/bsu-cubic-phase-session.json.
- Three obsolete prototype Lean files moved without overwrite into /tmp/bsu-cubic-phase-archive-20261018/. Final audit source, logs, manifests, reproduction scripts and verified cache retained.
- Incoming links updated on the two preceding affine cards. Prior checked affine Lean sources unchanged.
- Protected hashes remained unchanged:
  BiScale README dda7a67adbca527a21596c6fb672c28afb5feda594fe3b552a781325df7c3933
  BVI README fd49791f7d68e197372bfb55bf0289d3c19d24a39bfdb67eb8881d76a0b869e9
  walls ledger 2a4421e0c14fdc8ed9e2f107d79b941e5407945c12abb2b1e1fc99ed40267630
Predecessor memory: `mem:biscale/wall15-affine-sieve-phase-components`.

## Bounded frontier / limits
Both-field scoped hybrid searches inspected complete returned candidate/source inventories. Deep search was partial; semantic coverage unmeasured and background refresh incomplete. A lexical bispectrum/tripleCorrelation hit in RHTower.ThirdMomentResonance supplies a generic single continuum third-moment resonance identity, not full finite lag-data recovery; no RH imports/work. Concurrent BVI gcd-orbit result concerns ordinary periods, not this anti-periodic classification. No external novelty or global absence claim.
Wall 15 is not demolished: no arbitrary full phase reconstruction, quantitative stability, or minimal even degree proved.

## Next conjecture (NOT proved/formalized/countable yet)
Two-parameter coordinates Y6=a,Y10=b give g=(parity sign)[a R3+b R5].
Conjecture all translated moments of degree <=5 are invariant under b -> -b. Odd degrees already handled; the new quartic all-lag proof should use CRT and a lone prime-3 or prime-5 factor with zero mean in each odd cross term.
Symbolic candidate sixth zero-lag moment:
22a^6+360a^4b^2+480a^3b^3+1560a^2b^4+820b^6.
Its b-sign difference is 960a^3b^3.
Quadratics determine a^2,b^2; sixth moment should determine (ab)^3 and recover the pair up to global sign, including zero cases.
For general distinct odd primes p,q, candidate difference is 40a^3b^3(p-1)(p-2)(q-1)(q-2).
This is a paper conjecture derived symbolically via CRT and E[R_p^j]=((p-1)^j+(p-1)(-1)^j)/p, with no numerics. Refresh frontier and audit quartic all-lag proof before claiming minimal degree; do not treat general p,q as a separate contribution.
