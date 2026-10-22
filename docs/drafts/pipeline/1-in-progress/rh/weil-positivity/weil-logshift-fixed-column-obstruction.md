# Fixed history-coordinate errors and moment summability

Status: late-column result formalised; original coordinate-zero conjecture remains open. Corpus-only research, 2026-10-09.

## Primary conjecture

`¬ Summable (fun n => weilLogShiftRecoveryMomentResponse 0 n 0)`.

The moving inverse diagonal grows exponentially, but this does not decide one fixed response column. A proof would obstruct signed moment control even for arbitrarily small errors supported on one fixed history coordinate, independently of the decay rate assigned to later coordinates. If false, extract the corresponding finite-error stability theorem and inspect other columns.

## Exact implications to keep separate

- A nonsummable fixed column means two distinct amplitudes along that coordinate cannot both yield summable origin moments; their moment difference is a nonzero scalar multiple of the column.
- Every positive error envelope at that coordinate permits two such amplitudes. Hence at least one admissible perturbation is origin-nonsummable, and inward transfer excludes all real shifts for that witness.
- Nonsummability alone does not prove unbounded individual terms or the previous residual-unboundedness statement.
- If the fixed column is summable, that coordinate error preserves signed moment summability at origin. Determine the strongest exact stability statement instead of treating this as a failed negative result only.

## Investigation plan

1. [x] Re-search local corpus; inspect native inverse recurrence and off-diagonal weights.
2. [x] Prove a dependency-closed late-column growth/divergence argument. Coordinate zero remains open.
3. [x] Prove and audit the positive tail result; no early-column route is retired.
4. [x] Formalise the late-column conclusions; compile, axiom audit, import/index/lint checks.
5. [x] Persist findings and next conjecture; finish owned scratch cleanup.

## Log

- 2026-10-09 — previous turn proved constrained exponential-error divergence for 0<=sigma<4-pi. Current task tests fixed-column behavior; no inference from moving-diagonal growth is assumed.
- 2026-10-09 — direct corpus search and recurrence inspection found no fixed-column result. Existing central-margin lower bound uses four small transition factors, too weak for adjacent amplification. A sharper central interval must retain only the two facing small factors; the other two lie on the plateau. Coordinate zero is not currently controlled. Pivoting to a proposed theorem for every sufficiently late fixed impulse column, which would still address arbitrary positive precision envelopes.

## Proposed late-column proof, still to formalise

Write W(n,j) for the native recovery weight. Set a=99*pi/100 and beta=pi+9/4. Desired unconditional analytic bounds are:

1. C>0 with |W(n,j)|<=C exp(-a*j-4*j/(n+1-j)) for every 2<=j<=n. Extend the existing cutoff edge bound to all positive r by using exp(8-4r): for r>=2 the old estimate applies; for r<2 this factor is at least one. The overlap satisfies log((n+1)/j)<= (n+1-j)/j. Apply the common cutoff factor to all three kernel terms, then paired-kernel upper envelopes at shifts log2 and0, and sqrt(j)>=1.
2. D>0 with W(n,n-1)>=D exp(-beta*n) eventually. The origin and plus-shift cutoff terms vanish in this entry. For column j=n-1, integrate over radius d=1/(20n) around half the separation z=log(j)-log2. The overlap half-width is at least1/(n+1), hence at least19/(20n) for large n. Both facing margins are at least9/(10n); the two opposite factors equal1 on the plateau. The elementary transition lower bound S(x)>=exp(-1/x)/2 gives total edge cost exp(-(20/9)n)/4. Existing real-kernel lower estimates and the exponential chord bound give a constant times n^(-2) exp(-(pi+20/9)n) for the weight. Absorb n^(-2) into the gap 9/4-20/9=1/36. This yields the desired beta bound. No numerical experiment is involved.
3. Diagonal bound follows from1: W(n,n)<=C exp(-(a+4)n), while W(n,n)>0 is already proved.

Pure exponent comparison for n>=j+2 and j>=625:

beta*n-a*j-4*j/(n+1-j)-(j+1)*(n-j-1) <= -n/100.

To check it, put m=n-j-1>=1 and eta=pi/100<1/25. The coefficient gap is m+4/(m+2)-2=m^2/(m+2)>=m/3. Thus m^2/(m+2)-1/4-eta>=m/25. Since beta<25/4, the exponent is at most -j*m/25+(25/2)m, hence at most -j*m/50 for j>=625, and j*m>=n/2 gives -n/100.

Choose a global seed threshold J>=625 so that all analytic bounds hold, n*(C/D)*exp(-n/100)<=1/2, and (D/(2C))*exp((a+4-beta)*n)>=exp(n). Such J exists because a+4-beta=7/4-pi/100>1.

For a fixed impulse at coefficient seed s=k+2>=J, let g_j=Inv(unit(k))_j-Inv(0)_j. Native triangular equations give g_j=0 below s, g_s=1/W(s,s)>0, and sum_{j=2}^n W(n,j)g_j=0 for n>s. Induct on n to prove |g_n|>=exp(n)|g_(n-1)|. Earlier steps imply |g_j|<=exp(-(j+1)*(n-j-1))|g_(n-1)| for s<=j<=n-2. The exponent comparison bounds the entire older tail by half of W(n,n-1)|g_(n-1)|. Reverse triangle inequality and the diagonal bound then force the next growth step.

This gives |g_n|>=|g_s| exp((s+1)*(n-s)). Since s>=625, the coefficient growth beats the origin kernel's strict lower exponential rate and the sqrt normalization; the fixed-column absolute origin moments should tend to infinity. This would prove divergence for all sufficiently late columns, not specifically column0. Quantitative analytic lemmas and induction remain to be formally verified; do not report the late-column conclusion as proved yet.

Planned new leaf scopes: two-facing-edge lower bound; recovery row/adjacent estimates; late-column recurrence and growth. Existing precise cutoff and kernel lemmas remain the only analytic inputs.

## Two-edge lower bound: dependency-closed paper proof

For d>0, z>=0, a>0, assume z/2+d+a<=L and 1<=L+z/2-d. On the central interval (z/2-d,z/2+d], the factors S(L+t) and S(L-(t-z)) are exactly1; both remaining factors are at least S(a). The existing real-kernel lower bound gives a product at least (2*pi^2*S(a))^2 exp(-2*pi*exp(z+2*d)). Integrating over width2*d gives the corresponding truncated-autocorrelation lower bound. This loses only two transition factors, improving the earlier four-factor margin lemma in the plateau regime.

For x>0, expNegInvGlue(x)=exp(-1/x), and each denominator summand is at most1. Thus S(x)>=exp(-1/x)/2. Squaring and substituting into the central bound yields (d*(2*pi^2)^2/2)*exp(-2/a-2*pi*exp(z+2*d))<=KL_L(z). All ingredients are already proved in local Lean or elementary ordered-field/exponential inequalities; no new analytic premise is introduced. Formalising these lemmas first, then the native recovery row estimates.

- 2026-10-09 — `WeilLogShiftTwoEdgeLower.lean` now compiles/exports successfully: explicit transition lower bound, central two-edge lower bound, and its explicit exponential version. First compilation exposed a missing local transition-nonnegativity fact and a redundant tactic; corrected without changing the argument. Row envelope and pure tail exponent gap are written, currently under Lean validation. Native subdiagonal identity and quadratic-prefactor lower envelope are drafted but not compiled yet. No fixed-column conclusion is proved at this stage.

- 2026-10-09 — `WeilLogShiftRecoveryRowBounds.lean` now compiles/exports without diagnostics: relaxed all-scale edge bound, full-row absolute envelope for every 0<a<pi, and the exact 625-threshold exponent comparison. `WeilLogShiftSubdiagonalAmplification.lean` compiled its native adjacent identity, quadratic-prefactor lower bound, every strict rate b>pi+20/9, and unconditional eventual W(n+1,n)>=2*exp(n+1)*W(n+1,n+1). Removed redundant-tactic warnings; added the combined pointwise older-tail domination threshold, pending validation. This threshold is designed to sum over at most n+1 older entries in the induction. `WeilLogShiftRecoveryColumns.lean` now expresses the existing impulse inverse as a coefficient column and exposes its exact seed, row recurrence, and moment normalization; pending validation. All theorem axiom and global lint/index audits remain pending. Fixed-column growth induction remains the next mathematical step.

- 2026-10-09 — `WeilLogShiftRecoveryColumns.lean` compiled/exported without diagnostics. Added draft `WeilLogShiftLateColumnRunaway.lean`: private finite older-tail estimate, then unconditional existence of a late-seed threshold with exp((j+1)*(n-j))*|column(k,j)|<=|column(k,n)| at every pair of post-seed indices. The adjacent identity and two exact finite-sum splits supply the recurrence; cardinality<=n+1 sums the pointwise tail estimate. This is still awaiting Lean validation. For the moment payoff, the planned coefficient rate exceeds 2*pi+1, a strict upper bound for every real-shift paired-kernel critical rate; a positive lower kernel envelope and sqrt(n)<=n+1 should then yield absolute moment terms tending to infinity for each sufficiently late fixed column at every real shift.

## Next payoff after the fixed-column theorem passes Lean

- 2026-10-09 — The late-column theorem PASSED its first Lean compilation: all sufficiently late fixed impulse columns have absolute moment terms tending to infinity at every real shift; explicit nonsummability corollary also passed. No new analytic premise was assumed. All five leaves are now wired into RHTower.lean. The original coordinate-zero conjecture remains open; this proves the separate statement about all sufficiently late columns needed for arbitrary precision envelopes.
- 2026-10-09 — Final audit complete: all five final leaves compile/export without diagnostics; all 23 public theorem axiom sets are exactly `[propext, Classical.choice, Quot.sound]`. Five unique imports, final source hashes/object freshness, scoped gap/limit checks, and all 24 public API index rows verified. Index exit0. Global lint exit1 only for six unrelated unreachable modules, listed in `docs/drafts/pipeline/3-formalized/weil-logshift-late-column-runaway.md`; no affected-file diagnostic. Successor result is now recorded in `docs/drafts/pipeline/3-formalized/weil-logshift-arbitrary-precision-impulse.md`.
- 2026-10-09 — All owned jobs terminal. Removed all ten explicit `/tmp/hgt-weil-column-*` scratch/log/manifest files, including the earlier search result; absence verified. Final source hashes and unique imports rechecked before cleanup. The indefinite corpus goal remains active; next increment is the arbitrary-precision impulse theorem. Coordinate zero stays open on this card.

For any bounded center history and any sufficiently late fixed coordinate k, at most one real amplitude t on the line center+t*unit(k) can fail nowhere tail-unboundedness. Indeed, failure implies failure of origin tail-unboundedness (by the existing origin-to-all-shifts theorem), hence eventual boundedness at origin. If two distinct amplitudes both failed, subtracting their eventually bounded origin moments would bound |t-u|*|Response(0,n,k)|. Fixed-column runaway contradicts this. This proof uses only finite affine moment identities and the pending fixed-column theorem.

Consequently, every strictly positive coordinatewise error envelope, however fast it decays, permits a bounded history with nowhere tail-unbounded moments, differing from the prescribed center at exactly one arbitrarily late coordinate and preserving any requested finite prefix. Take k beyond both thresholds, and compare the two nonzero amplitudes epsilon(k) and epsilon(k)/2: at most one is exceptional. Both obey the envelope. This removes the former subcritical-exponential restriction for existence, and gives a stronger co-singleton statement along each late impulse line. Do not claim this payoff formalised yet; create its precise successor card after validating the fixed-column theorem.
