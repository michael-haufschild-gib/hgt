# Wall 15: exact affine sieve phase components (2026-10-18)

Outcome: Progress. Wall 15 remains open; all-walls research goal remains active. No new analytic hypotheses, axioms, numerics, hgtl7, subagents, full/umbrella builds, commits or external messages. Do not update the independent BVI worker's progress counters.

## Exact result on actual arithmetic objects
For real finite divisor weights at cutoff N, existing sieveSeq gives s_c(k)=sum_{1<=d<=N,d|k} c(d), and existing selbergMultiplesCoord gives Y_c(q)=sum_{1<=d<=N,q|d} c(d)/d. Define affineMoment N c a b=(1/N!) sum_{0<=k<N!} s_c(k)s_c(a*k+b). This is the literal uncentered bilinear average, not a Fourier proxy or Hermitian covariance.

DFT in b, unnormalized: DFT A_c(a,.)(r)=N! Y_c(q)Y_c(q/gcd(q,a)), q=addOrderOf r in ZMod N.factorial. Every natural cutoff (including 0), slope (including 0), and translation is covered. A derived NeZero factorial instance is not an added premise.

Equality of every affine moment is equivalent to equality Y_c(q)Y_c(d)=Y_e(q)Y_e(d) for all 1<=d|q<=N. It is also equivalent to a Boolean sign mask relating the coordinate profiles, constant on each divisor edge with two nonzero endpoints; equivalently one sign per component of the nonzero divisibility graph. No connectedness/nonvanishing assumption. Slopes 1<=a<=N and translations 0<=b<N! already form a complete finite observation family. At edge d|q choose a=q/d and frequency N!/q. No stability/optimal sample claim.

Counterexample at every cutoff N+5: c(1)=-2,c(3)=3,c(5)=5; e(1)=0,e(3)=3,e(5)=-5, all other coefficients zero. Coordinates are supported at 3 and 5, values (1,1) and (1,-1). Every affine moment agrees, but s_c(0)=6 and |s_e(k)|<=5 for every k. Thus no translated global sign identifies responses, and no functional of the complete affine data recovers absolute origin response. Strongest positive salvage is the exact full classification plus finite completeness, not just this counterexample.

## Exact certificate
Three new leaves, common namespace GaloisForLFunctions.BiScaleUncertainty.AffineSieve:
- formal/GaloisForLFunctions/BiScaleUncertainty/AffineFourierCorrelation.lean: 6 public exports; generic cyclic correlation transform and concrete divisor-indicator transform.
- formal/GaloisForLFunctions/BiScaleUncertainty/DivisorSieveAffineSpectrum.lean: 17 exports; spectrum, comparable products, finite completeness, sign components, explicit 3/5 weights.
- formal/GaloisForLFunctions/BiScaleUncertainty/AffineSievePhaseRecovery.lean: 14 exports, importing existing PronicBezoutSplitAndPrimePowerIndecomposability for actual sieve objects.
Key final names: dft_affineMoment, affineMoment_eq_iff_comparable, affineMoment_finite_complete, affineMoment_eq_iff_signComponents, exists_same_affine_data_distinct_absolute_origin, no_absolute_origin_decoder.

37 exports = 26 theorems + 11 definitions. All 37 #check and #print axioms passed in /tmp/bsu_affine_public_audit.lean, exit 0, no warnings, only propext/Classical.choice/Quot.sound. All 11 exported definition bodies plus both underlying sieveSeq and selbergMultiplesCoord bodies printed and inspected. No copied temporary prototype definition appears in production. The formal certificate is coefficientwise; Ramanujan grouping is in the paper proof, not a separate exported Mobius-row theorem.

Final original named sources checked via lake --old env lean -j 1. Empty logs /tmp/bsu-affine-fourier-core-r3.log and /tmp/bsu-affine-spectrum-core-r1.log, observed exit 0. Main /tmp/bsu-affine-main-r1.log empty; fresh olean/ilean emitted, process terminal; its final tool output was drained during compaction so exit code was not separately retained. Independently importing this emitted main artifact and auditing every export exited 0 (/tmp/bsu-affine-public-audit-r1.log). No final source edited after check. Do not repeat unchanged successful checks.

Main/audit used prior verified /tmp/bsu-two-lag-workspace cache closure. Main compiled absolute original source with --root=/Users/michael/Documents/code/hgt/formal. This existing actual-object import graph is very large; import-only jobs can take minutes. One owned Lean process at a time. Parent artifacts copied into workspace and main artifacts back to root only after byte-hash checks; no unrelated artifacts overwritten.

## Durable evidence and integration
Formalized card: docs/drafts/pipeline/3-formalized/wall15-affine-sieve-correlation-phase-components.md.
Failed global-sign route: docs/drafts/pipeline/5-failed/wall15-global-sign-recovery-from-affine-moments.md. Retired only after exact positive survivor had dependency-closed paper proof and actual Lean certificate.
Manifest with every public name, source/artifact hashes and axiom closures: /tmp/bsu-affine-phase-manifest.json. State: /tmp/bsu-affine-phase-session.json.
Three imports occur exactly once in BiScaleUncertainty umbrella; umbrella was not built. Index refreshed, /tmp/bsu-affine-index-r2.log exit 0. Scoped lexical discovery inspected all 52 declarations (9+27+16), including all 37 public exports, and both spectrum pages. Namespace-only search initially missed first two modules; module-name queries found all. Evidence /tmp/bsu-affine-discovery-{fourier-r2,spectrum-r2,spectrum-20-r2,main}.json.
Final lint --check-generated exit 1, /tmp/bsu-affine-lint-r2.log: no owned module errors, no proof-debt diagnostics, no stale generated files; 381 existing size warnings; four concurrent unwired modules: RHTower.JointAncestrySquareShellFinitePowerCriterion, BiScaleUncertainty.EulerPoissonChiralDriftAndPrimeShiftRigidity, BezoutValuationIncidence.GcdOrbitProjectionAndExactTranslationPeriods, BezoutValuationIncidence.SawtoothBezoutSuccessorGradientAndRouteFZZPBridge. Leave unrelated work untouched; do not claim global lint green.
Both field READMEs and walls ledger were read-only for this task. BiScale README and ledger match initial hashes. BVI README changed concurrently from 93dd937ee375387f198f4275b9139faf9989ee69ddcd4d913d06633ee4a2f22a to fca0e2559b2407f9fc9a59b2d4d65f481682b9c1893182514e4133496cb5b0e0; no writes from this task, no revert. Manifest preserves both hashes.
Three owned prototype lean files archived via mv -n to /tmp/bsu-affine-phase-archive-20261018/. Final audit, logs, manifest and cache workspace retained. All owned processes terminal.

## Next conjecture, not completed work
Backlog docs/drafts/pipeline/0-backlog/wall15-cubic-odd-mode-recovery-and-parity-obstruction.md. Literal triple correlation double DFT should equal P^2 Y(ord r)Y(ord s)Y(ord(r+s)); r=s at odd q gives P^2Y(q)^3 and unconditional signed odd-mode recovery. Profiles supported at 6,10 with values (1,+/-1) should retain all affine quadratic data and annihilate every odd translated moment via g(n+15)=-g(n), while one reaches 6 and the other stays within absolute 5. Use shift 15, not P/2 (factorial has extra 2 powers). No Lean certificate on this next card; refresh frontier and prove paper before implementation. Bounded corpus evidence /tmp/bsu-affine-cubic-frontier.json, no external novelty claim.

## Tool discipline
No update_plan tool available; durable card is tracker. Serena symbol tools ignore Lean tree in this session; new-file/apply_patch fallback used. Guard potentially long Python with scripts/run_guarded.py; use documented research command directly. Keep read-only files untouched, no full builds, one owned foreground Lean process. Goal is not complete or blocked.