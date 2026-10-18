# Wall 11: exact two-lag sieve moment cone — formalized 2026-10-18

Outcome: **Progress**. Wall 11 remains open; the user's broader research goal remains active. No RH argument, wall closure, external novelty claim, or classification of every realizing weight. Previous turn: `mem:biscale/wall14-integer-affine-shear-size`.

## Concrete theorem
For actual finite signed real divisor-sieve weights, let s(k)=sum_{1<=d<=M,d|k} c(d), H=sum c(d)/d, and Y(e)=sum_{e|d<=M} c(d)/d. `periodCovariance M c h` is the literal centered average of (s(k)-H)(s(k+h)-H) over k=1,...,M!, divided by M!. Exact generalized CRT gives joint density gcd(a,b)/(ab) when gcd(a,b)|h and zero otherwise. Zero lag equals existing `sieveVariance`; lag one equals existing `bezoutCoprimeQuadraticForm - H^2`; lag two is sum_{e=2}^M r2(e)Y(e)^2, where r2(e)=mu(e)+2*1_(2|e)*mu(e/2).

Writing (V,x,y)=(C0,C1,C2), the exact cone has facets:
- 2V+3x+y >= 0;
- V+x+y >= 0;
- V-x+y >= 0;
- V-4x-2y >= 0;
- V-x-2y >= 0.

Its normalized rays (x/V,y/V) are (-1,1),(-1/2,-1/2),(0,-1),(1/2,-1/2),(0,1/2), from modes 2,3,4,6,12. All arithmetic rays satisfy the facets. A useful stronger lemma proves phi(q)>=8 for odd q>=2 with mu(q)=1, via two distinct odd prime divisors.

For EVERY cutoff N+12 and arbitrary prescribed real mean H, an actual finite weight has literal moments (V,x,y) iff these five facets hold. Explicit nonnegative variance masses (A,B,C,D,E):
1. x+y>=0: A=(V-4x-2y)/3; D=2(V-x-2y)/3; E=2(x+y); B=C=0.
2. x+y<0 and V+2x+y>=0: A=(V-x+y)/3; C=-x-y; D=2(V+2x+y)/3; B=E=0.
3. Otherwise: A=V+x+y; B=-2(V+2x+y); C=2V+3x+y; D=E=0.
Set Y1=H and Y2=sqrt(A),Y3=sqrt(B/2),Y4=sqrt(C/2),Y6=sqrt(D/2),Y12=sqrt(E/4), zero elsewhere. Existing `RHTower.pmRamanujanResidueCoeff` supplies the finite inverse; that inverse is reused, not claimed new.

Complete actual-sieve linear dual: alpha V+beta C1+gamma C2>=0 for every cutoff and weight iff all five expressions alpha-beta+gamma, 2alpha-beta-gamma, alpha-gamma, 2alpha+beta-gamma, 2alpha+gamma are nonnegative. Modes 4 and 12 give two actual weights at every N+12 and arbitrary H with identical mean H, variance 1, C1=0, but C2=-1 and 1/2. The second lag adds information.

## Formal sources and exports
All new exports are in namespace `GaloisForLFunctions.BiScaleUncertainty.TwoLagSieve`.
- `formal/GaloisForLFunctions/BiScaleUncertainty/TwoLagArithmeticCone.lean`: 7 public exports, including divisor kernel, odd totient bound, arithmetic facets, explicit five-mass equivalence and abstract cone dual.
- `formal/GaloisForLFunctions/BiScaleUncertainty/TwoLagSievePeriod.lean`: 3 public exports: shifted count, joint count and joint density.
- `formal/GaloisForLFunctions/BiScaleUncertainty/TwoLagMomentCone.lean`: 14 public exports, including literal `periodCovariance`, three bridges, finite inverse profile/weight, `exists_sieve_with_two_lag_moments_iff`, `universal_two_lag_sieve_inequality_iff`, and `exists_same_first_moments_distinct_second_lag`.
Total: 24 public exports (19 theorems, 5 definitions). Former separate diagonal source was merged into the main leaf to avoid redundant heavy imports; no `TwoLagSieveDiagonal.lean` remains in the tree.

Card: `docs/drafts/pipeline/3-formalized/wall11-two-lag-sieve-moment-cone.md`, with complete dependency-closed paper proof, bounded corpus evidence, certificate, limitations and log. Stage 3 only.

## Verified evidence
All FINAL named-leaf sources passed direct Lean checks with exit 0 and no warnings:
- `/tmp/bsu-two-lag-arithmetic-cone-r4.log`
- `/tmp/bsu-two-lag-period-r2.log`
- `/tmp/bsu-two-lag-moment-r2.log`
Public audit `/tmp/bsu_two_lag_public_audit.lean` imported actual final main module; all 24 signatures and axiom closures plus all five printed definitions manually inspected. Exit 0, no warnings, only `propext`, `Classical.choice`, `Quot.sound`. Log `/tmp/bsu-two-lag-public-audit.log`. Machine check verified every expected export, allowed axioms and final source hashes.

Each new leaf imported exactly once in BiScaleUncertainty umbrella. Index regeneration passed. Scoped documented lexical research pages offsets 0/20/40 returned all 46 declarations and all 24 public exports; complete for this scoped inventory, not global novelty. Initial hybrid/deep corpus coverage was partial/stale; no external novelty claim.

`/tmp/bsu-two-lag-manifest.json` preserves all 24 names, exact source hashes, direct check logs, audit data, wiring, discovery, protected hashes, artifact provenance, lint history and cleanup. `/tmp/bsu-two-lag-session.json` has no active owned job. Final records verified all 3 source hashes, all 3 protected document hashes and 3 imports.

Latest repository lint `scripts/formal_tools.py lint --check-generated` exited 1 with ONE unrelated concurrent error: `GaloisForLFunctions.BezoutValuationIncidence.DilatedCellScalingAndSecondOctaveFermiJumpBridge` is unreachable from its theorem-area umbrella. Log `/tmp/bsu-two-lag-lint-final.log`; 381 pre-existing large-file warnings; no TwoLag or active proof-debt errors. Earlier run had two other unwired modules (StationaryResolventMarkovPositivityAndNodalDefectProducer and PrimeTailCalibrationAndMobiusDefect), now wired by their owners. Latest repository gate is NOT claimed green; preserve concurrent work.

## Runtime and scope discipline
The existing sieve definition's source import graph spans 9,349 project modules; the exact BVI dependency spans 9,354. Import finalization can take 8–15 minutes. `/tmp/bsu-two-lag-workspace` retains an isolated toolchain-matching cache with current root closure, previously verified Wall 13 fallback artifacts and one missing WeilPolarConeFirstVariation.olean copied from the existing Muntz boundary cache. No unrelated source/dependency artifacts overwritten; only six owned new .olean/.ilean files installed to root cache with hashes checked. No full/umbrella builds or heartbeat changes. Do NOT repeat unchanged successful Lean checks; retain verified workspace and evidence.

Seven obsolete owned scratch sources safely archived via mv -n under `/tmp/bsu-two-lag-archive-20261018/`; final audit source/logs/manifest/reproduction scripts/workspace retained. No owned running jobs. Both field READMEs and docs/reports/walls-ledger.md remained strictly read-only with hashes unchanged. No subagents, numerical experiments, hgtl7, commits/pushes or external messages. Keep all concurrent BVI modules, cards and research ledgers untouched.
