# Chronological recovery: hardest-problem checkpoint

User explicitly rejects further routine operator formalization. Every turn must attack hard mathematics. Active goal: genuinely new field with intrinsic zeta zeros outside RH; novelty and priority unestablished. No goal completion claim.

## Current hard target — exact sign, not another numerical scan

The stronger positive-moment conjecture now has a reproducible numerical counterexample candidate. Let actual gaps be δ_k (weight k+1), γ_k=(δ_k/δ_0)^2, s=3/10000, and

p(x)=sum_(j=0)^17 c_j x^j,
c_j=(-1)^j binom(17,j) binom(18+j,j)/(j+1).

This is P_17^(1,0)(1−2x)/18, a canonical normalized Jacobi polynomial (DLMF 18.5.7), with exact rational coefficients independent of a fitted numerical eigenvector. Candidate exact inequality:

sum_(i,j=0)^17 c_i c_j s^(-i-j) δ_(i+j)^2 < 0.

Numerical value −0.000003981952758270649181357..., or −0.000243400090218270818985648... divided by δ_0². If proved exactly, excludes any positive moment measure because it would integrate a polynomial square. Only δ_0,...,δ_34 needed. Rational s removes any dependence on a numerical approximation of ρ. THE NEGATIVE SIGN IS NOT YET PROVED. Do not import numerical bounds/certificates into Lean. Next attack exact sign or structural obstruction; no more degree scans without a new mathematical reason.

## Exploration already completed and downloaded

Folder docs/drafts/pipeline/2-fully-proven/computations/chronological-recovery-gaps; remote /root/chronological-recovery-gaps. All math numerics only authorized Runpod SSH root@157.157.221.29 port27094 ~/.ssh/id_ed25519, up to24workers, BLAS/OpenMP1. All jobs ended; no owned Lean process was started this turn. All outputs downloaded, REPORT.md rewritten as compact knowledge notes.

Retained: minimax_probe.py/minimax-results.json (m1..8 grid LP); refine_probe.py/refined-results.json (70digit); moment_tests.py/moment-tests.json (8moments); factor_probe.py/factor-results.json (m1..32,110digit); structure_probe.py/structure-results.json; extension_probe.py/extension-results.json (m1..64,140digit); witness_probe.py/witness-results.json (independent coefficient coordinates,m1..35,230digit); diagnostics_probe.py/diagnostics-results.json.

Factor method F(c)=c^m product(c−d_j)(2−c−d_j). Log second derivative strictly negative between roots. Exactly one interior peak per interval before last root; on final interval derivative decreases to m>0 at1, so endpoint1 is peak. Equal alternating heights plus interlacing characterize exact minimax, but small numerical residuals do not certify exactness.

Extension uses analytic Schur elimination of diagonal contact Jacobian block: m×m solve instead of2m×2m. Witness verification instead solves monomial-coefficient/contact equations with heights ±1 at230digits; maximum relative disagreement with factor gaps6.9e−135, all residuals<1e−180. This corroborates, not proves, sign.

Squared γ:17×17 unshifted Hankel positive,18×18 minimum eigenvalue≈−9.5666e−26; first-entry Schur complement≈−0.00041286769. Shifted matrices positive through32. ALL2080 Hausdorff finite differences of64scaledmoments positive, and all63gapratios increasing. Finite triangles are weaker than positivity on all polynomial squares of available degree. A square with interior zeros cannot have nonnegative Bernstein coefficients at any finite degree; the infinite Hausdorff implication uses approximation. Don't repeat the earlier erroneous favorable inference.

Unsquared gaps first unshifted negative atsize10; shifted also negative by24, so 'only negative atom atzero' model unsupported. Log-gap backward differences first negative atorder24: numerical obstruction to infinite-divisibility route. Neither is a proved no-go. Fixed-degree Fenton intertwining (Farkas–Nagy–Révész2021/39,Th4.1) does not compare degrees.

## New positive survivor — full paper proof, not Lean

New card docs/drafts/pipeline/2-fully-proven/chronological-recovery-uniform-spectrum.md. It proves uniform block growth, strictly stronger than the one-orbit rate:

lim_(d→∞)[sup_k δ_(k+d)/δ_k]^(1/d)=ρ.

Let T_d monic weighted minimizer, t_d norm, S_d positive root sum<d/4. T_0=1,t_0=1. H_d=c^d T_d(u/c) is homogenization, includingc0. It begins u^d−S_d u^(d−1)c+O(c²). Correct it:

A_d=H_d+S_d c H_(d−1).

Its c coefficient vanishes and c^0 coefficient is u^d. Thus A_d∈actualA=R[u,c²,c³], acts asU^d onB/A. Physical norm≤t_d+S_d t_(d−1)≤t_d+(d/4)t_(d−1)=B_d. Multiplying any attained normalized degree(k+1)residual byA_d preserves required c coefficientu^(k+d). Hence δ_(k+d)≤B_dδ_k ALLk,d. Since t_d^(1/d)→ρ, B_d^(1/d)→ρ. Lower bound k0 squeezes uniform limit.

Complexify actual Hilbert shift: U b_k=(δ_(k+1)/δ_k)b_(k+1). NormU^d=sup blockratios. Outside|z|>ρ Neumann series converges. Inside|λ|<ρ, vλ=sum λ^k δ0/δk b_k is convergent nonzero eigenvector ofU* with eigenvalueλ. Spectrum of complexifiedU exactly closeddisc radiusρ. No moment positivity, ratio convergence, or log-convexity used. This positive survivor is not yet Lean formalized and does not prove the remaining curvature inequality.

## Existing rate theorem, paper only

Card chronological-recovery-exponential-rate.md. W(r)=1−sqrt(1−4r),r∈[0,1/4]; δ_(m−1)=t_m/S_m by paper weighted alternation/coefficient duality. Transform t=1−c,r=(1−t²)/4 gives even unrestricted monic weightedCheb degree2m,weight sqrt(1−|t|),potentialQ=−.5log(1−|t|).

Uniqueθ∈(0,π/2):2(π−θ)=3πsinθ; b=cosθ≈.838771399357. ρ=(b²/16)exp[(2/π)integral0π/2log(1−bcos s)ds]≈.0173600420998208830164. Paper limδk^(1/k)=ρ; any positive compact γmeasure would endatρ². Smooth quadratic extension outsidea∈(b,1),energycomparison handles singular endpoints; don't apply whole-line support theorem without this step.

Equilibrium measure μ=integral0^b arcsine[-a,a] H'(a)da, H(a)=(I(a)−π/2)/π, I(a)=(π/2+arcsina)/sqrt(1−a²),I(b)=3π/2. Wallis/Abel identity proves weighted potential condition. μ is APPROXIMATION ROOT measure, NOT gap moment measure. S_m/m→b/(4π)+3b²/16 fromrootdistribution harmonicmoments. Strong constant-prefactor asymptotic still unproved.

## Formal checkpoint unchanged

106leaves1094decl=810theorems284defs. All final exact leaf builds,axiom audits,wiring,index/lintpassed earlier. Latestfive: CubicRecoveryMultiplier9, CubicCuspMultiplier9,CubicHilbertShift11,CubicRecoveryCommutator8,CubicRecoveryPositivity8. No newLeanthisturn. /tmp/chronological-recovery-shift-audit-summary.txt and corresponding-index.txt,-lint.txt. Unfinished /tmp/chronological_cubic_recovery_moments.lean notexported/notcounted/notpriority. Do not falsely claim momenttheorem or exactwitnesssign formalized.

Primary compactnotes: 1-in-progress/chronological-recovery-moment-problem.md; 1-in-progress/excursion-intervention-geometry.md updated. All actualmathverification rules persist: foregroundoneprocess, lake env lean scratch,finalleafonlylakebuild,no full/umbrella build,nonewaxioms/nonumericalcertificate, #printaxiomsinscratch,wireleaves,lintgate. No commitsbyus; sharedtree otheragentsworking—preserveunrelatedfiles/processes.