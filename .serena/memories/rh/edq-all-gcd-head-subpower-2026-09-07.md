# EDQ all-gcd corrected heads: closed Lean estimate (2026-09-07)

RH goal remains ACTIVE, unachieved. This goal turn made mathematical/formal PROGRESS: unconditional aggregate bound extends preceding coprime-head theorem to ALL exact gcd groups, plus total-variation comparison. Frontier map remains READ ONLY and was not edited. No subagents, commits, or numerical experiments this turn. Preserve user Lean discipline: one foreground Lean per agent, scratch checks, only targeted final build, audit only new declarations, no umbrella/full builds. No owned processes/scratch remain.

## New authoritative leaf
formal/GaloisForLFunctions/RHTower/EulerDeletionGcdHeadSubpower.lean (about475lines), namespace RHTower.DeletionGcdHead. Wired after EulerDeletionCoprimeHeadSubpower in RHTower.lean. Three public defs, five public theorems (8 total audited). Private helpers are arithmetic and finite-form manipulations, no new axioms/premises/computational certificates.
- residueQuadratic r N k: mu(r)^2 times coprime cofactor-pair residue Gram at actual moduli r*a,r*b, with masks gcd(r,a)=gcd(r,b)=1; a,b<=N/r.
- harmonicQuadratic r N: corresponding physical harmonic coefficient K_r(N)=sum_(gcd(d,e)=r)mu(d)mu(e)/(de).
- initialEnergy r N: H_r=sum_(k=1..N) B_r(N,k)/[k(k+1)].
- residueQuadratic_eq_actual: original mu(r*a)mu(r*b), original moduli and coordinates.
- gcd_pairs_eq_image (r>0): actual gcd-r pairs d,e<=N exactly image (r*a,r*b) of coprime cofactor pairs through N/r. Positive-r multiplication is injective.
- harmonicQuadratic_eq_actual (r>0): original coefficient harmonic form.
- exists_initialEnergy_remainders_subpower (line300): for every epsilon>0, exists C>0, ALL naturalN (including0), sum_(r=1..N)|H_r(N)-K_r(N)*DeletionCoprimeHead.headMass(N)|<=C*N^epsilon.
- exists_initialEnergy_variation_comparison (line443): same for abs(sum_r|H_r|-headMass(N)*sum_r|K_r|).
headMass A_N=sumk<=N k/(k+1) is reused from preceding leaf.

## Direct arithmetic mechanism
r>=1,Q=N/r,t=k/r natural, v=(k:Real)/r retains affine offset v-t. Actual mu product factors as mu(r)^2 mu(a)mu(b) on masks; failed mask makes original coefficient zero. Complete inner coprime masked floor column is supportedCount(r*a,t). Exact polarization:
B_r(N,k)-k² K_r(N)=mu(r)^2*(-2v L+F),
L=sum_(a<=Q,gcd(a,r)=1)mu(a)/a*S_(r*a)(t),
F=sum_(a<=Q,gcd(a,r)=1)mu(a)*floor(t/a)*S_(r*a)(t).
If t0 remainder0. Otherwise r*a<=N,t<=N and preceding Rankin estimate give S<=C_delta N^(2delta). Thus |L|<=C N^(2delta)(1+logN), |F|<=v*C N^(2delta)(1+logN). Weighted absolute remainder <=3C N^(2delta)(1+logN)/(r*k). Sumr andk adds two harmonic factors, choose delta=epsilon/5. This proves total absolute error, not merely fixed-r or signed aggregate. Comparison follows reverse triangle inequality.

## Consequence and remaining hard target
Previous fixed-budget experiment (`mem:rh/edq-head-tail-budget-and-cotangent-gap-2026-09-07`) failed B in2rawcases. Those finite constant-budget failures DO NOT distinguish subpower growth strategies: the aggregate corrected-head difference is now proved subpower. Do not repeat that diagnostic or claim it rules out polynomial separation asymptotically.
Remaining actual estimate: retained polynomial variation A_N*sum_r|K_r(N)| together with complete later tail. New theorem removes aggregate corrected-head remainder from growth obligation, NOT coefficients or tail. Full chain Euler deletion -> exact complex zero balance -> signed arithmetic separation -> off-line exclusion -> RH. No new RH receiver added; no route retired. All-gcd theorem only raw cutoff; does not assert uniform-in-inner-X bounds for arbitrary outer log-taper M.

Corpus checks this turn included all-tree mobius cancellation, gcd sum coprime, signature/joint orientation, exact covariance/squarefree shear and current decomposition. Joint fifth-word convergence holds off-line, and full-energy factorization retains cross terms; neither supplies new source sign law. No new external mathematical premise used.

## Docs
New docs/drafts/pipeline/3-formalized/edq-gcd-head-subpower.md (full statement, proof, boundary, validation).
Working card docs/drafts/pipeline/1-in-progress/edq-full-covariance-core-attack.md has closed all-gcd proof section and corrected asymptotic reading of finite budget test.
Previous edq-coprime-head-subpower formalcard links extension.
STATUS appended generic MUST-AGGREGATE-CORRECTION-COSTS: must bound total correction cost for growing components; finite constant failures cannot show different powergrowth when aggregate correction subpower. Existing retained-polynomial entry preserved. Frontier untouched. Index refreshed once (4changed due foreign additions), repository lint PASS exit0; existing large-file warnings only. Scoped gitdiffcheck passed.

## Verification and cleanup
Complete scratch passed lake env lean no diagnostics. Final LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionGcdHeadSubpower exit0, newleaf built10sec,10902 graphjobs mostlycached. Six pre-existing missing olean artifacts discovered transitively:
XiCauchyTransformCompleteness, SuzukiCarlemanJumpPhaseObstruction, SuzukiGroundEdgeApertureObstruction, SuzukiFiniteMorseResolventJetCompletion, SuzukiGlobalLocalScalarPickUniversalityLaw, HedenmalmCenterMixedLocalThreePoint.
Restored these one-at-a-time via lake env lean -o neededtarget (nootherownsource edits). Final Lake audit recompiled those dependencies to restore its full artifacts; manual olean-only recovery did not restore all Lake outputs. Future avoid needless duplicate recovery if equivalent complete artifact recovery is available. No large or umbrella build ran. Cached dependencylogs replayed oldwarnings; newleaf clean.
Audit only8publicdecls via separate/tmpfile: exactly propext,Classical.choice,Quot.sound for all. No Lean.ofReduceBool/sorryAx/addedaxiom. All own sessions CLOSED (95221 namesinitialmissing,22593firstdep,19071remainingdeps+names,67082/65143/76682/13467/86271/93319scratch,41317more names,32666finalbuild,88750axioms,11259index,84123lint). Removed /tmp/edq_gcd_head_names.lean,more_names.lean,proof.lean,axioms.lean. Final process check shows no owned Lean. Foreign unrelated DualCarrierWeightRightShift activity was preserved.