# Exact joint phase cancellation and its unpaid energy cost

Status: finite phase classification, logarithmic-cost escape, smooth-mixture and actual real-active-node bridges, full-energy coercivity and normalized energy escape are Lean-audited. Later entries below supersede historical implementation checkpoints. **BRIDGE**, scientific novelty unestablished. Parent mechanisms are Kronecker recurrence, separation and finite positive quadrature. Full PBAP and Candidate D remain OPEN. This statement closes an exactness gap in the L376 two-frequency sketch; it does not prove a cheap cancellation theorem.

## Statement

Let p>=5 be prime, L=(log p)/2, and 0<W<log 2. Fix any nonzero real smooth function beta supported in [0,W]. Write psi(x)=integral beta(u+x) beta(u) du. For every M>1 and every real R there are finitely many frequencies t_j>R and positive weights w_j such that

    sum_j w_j = M,
    1 + sum_j w_j cos(t_j (log n-L)) = 0     (2<=n<p).

The number of frequencies can be at most p-1. Define real smooth profiles

    beta_0(u)=beta(u),
    beta_j,c(u)=sqrt(w_j) beta(u) cos(t_j u),
    beta_j,s(u)=sqrt(w_j) beta(u) sin(t_j u).

Their aggregate autocorrelation is

    Psi(x)=psi(x) [1+sum_j w_j cos(t_j x)].

It vanishes at every shifted node log n-L, n>=2. The associated two-cluster differences g_i(u)=beta_i(u)-beta_i(u-L) are an actual finite smooth mixture, null at every integer logarithm. All profiles use the same fixed broad support; no shrinking-packet approximation occurs. Total squared mass of the beta_i is (1+M) integral beta^2, and of the g_i is twice that. Thus normalization retains the base profile with coefficient theta=1/(1+M), arbitrarily close to 1/2 from below.

The finite phase system has the **sharp infimum M=1, never attained**. Every exact positive solution has M>1, but every M>1 is achievable after every frequency threshold R. This sharp statement is about modulation weights, not the spectral mass of an atom in an absolutely continuous Fourier measure.

The finite phase classification and broad-profile construction both hold for every prime p>=5. The support argument needs L>W, which follows from log p/2>log 2>W. The earlier sufficient condition L>2W was unnecessary; the separate Candidate D formulation retains its stated scope.

## Arithmetic and recurrence

Set a_n=log n-L for 2<=n<p. None is zero: n^2=p would contradict primality. Distinct a_n are neither equal nor opposite: equality forces n=m, and opposition forces nm=p, impossible when 2<=n,m<p.

The finite prime frequencies (log q)/2 for q<=p are rationally independent. Multiplying a rational relation by a common denominator and by two gives an integer relation among prime logarithms, ruled out by unique factorization. This is exactly the independence already proved by the corpus, with a nonzero common rational scaling.

Prescribe phase pi for (log p)/2 and phase zero for all other prime frequencies. No integer n with 2<=n<p contains p as a prime factor. Hence along arbitrarily late Kronecker approximants,

    exp(i t log n) -> 1,
    exp(i t L) -> -1,
    cos(t a_n) -> -1

simultaneously. The corpus `kronecker_approx_atTop` supplies the arbitrary lower threshold on t; no rate or finite upper height is asserted.

## Exact positivity, not approximate cancellation

For fixed R let v(t)=(cos(t a_n))_(2<=n<p), t>R, and C=conv{v(t):t>R}, with ordinary finite convex hull in R^(p-2).

First, 0 is an interior point of C. To prove this, every nonzero linear observable must take both signs arbitrarily late. For real coefficients c_n, put h(t)=sum c_n cos(t a_n). Elementary integration gives its average on [R,R+T] tending to zero. The distinct nonzero frequencies up to sign also give

    average h(t)^2 -> (1/2) sum c_n^2 > 0.

Indeed expand the square and apply 2 cos u cos v=cos(u-v)+cos(u+v); each nonzero-frequency average tends to zero, and only the n=m difference term remains. If h were nonnegative on a tail, its boundedness would give 0<=h^2<=B h on that tail, contradicting these two limits. Apply the same argument to -h. Finite-dimensional separation, or the corpus `zero_mem_interior_convexHull_image_Ioi`, now gives the asserted interiority.

Second, z=(-1,...,-1) belongs to closure C by the prescribed Kronecker phases. Let k=1/M, so 0<k<1. The point kz belongs to C, in fact to its interior. Here is the exact step that approximate cancellation alone misses. Choose r>0 with ball(0,r) contained in C, and q in C sufficiently close to z that k||q-z||<(1-k)r. Convexity gives ball(kq,(1-k)r) contained in C; that ball contains kz. Thus kz is an actual finite convex combination of actual values v(t_j) with t_j>R. Caratheodory reduces the number of nodes to at most (p-2)+1. Delete zero weights and multiply the remaining probability weights by M. Their moments are exactly -1 and their total mass is exactly M.

## Sharpness and nonattainment

For any one node a_n, the identity sum w_j cos(t_j a_n)=-1 and cos>=-1 imply M=sum w_j>=1. If M=1, positivity forces cos(t_j a_n)=-1 for every positive weight and every n. In particular t_j a_2 and t_j a_3 are odd integer multiples of pi, so a_2/a_3 is rational.

That ratio is irrational. A rational relation v a_2=u a_3, with integers u,v and v nonzero, yields

    2v log 2 - 2u log 3 + (u-v) log p = 0.

Prime-log independence (p>=17 distinguishes all three primes) forces u=v=0, a contradiction. Thus M=1 is impossible. Together with exact existence for every M>1 this proves the sharp unattained infimum without a numerical estimate.

## Actual smooth-mixture realization

For each j, the cosine and sine autocorrelations sum to w_j cos(t_j x) psi(x), by the addition formula under the integral. There are finitely many terms, all smooth and compactly supported. At x=0, cos^2+sin^2=1 gives the exact mass identity.

Since p>=5 and W<log 2, L>W. For 2<=n<p the phase identity kills Psi(log n-L). For n>=p, log n-L>=L>W and support of psi in [-W,W] kills the sample. Thus the shifted-null property holds for every n>=2, including all nodes above the finite interpolation range.

Translation expansion gives the aggregate autocorrelation of the g_i as

    2 Psi(x)-Psi(x-L)-Psi(x+L).

At x=log n, n>=2, the first term vanishes because log n>=log 2>W, the second by the shifted-null property, and the third by support. Negative samples vanish by evenness. Taking symmetric real samples and dividing by sqrt(n) gives exactly the WP01 `logValue` constraints. All mixture weights can be taken as one after absorbing w_j into the profiles, so this is the actual nonnegative finite-mixture cone. Disjointness of the two support intervals proves the factor-two mass identity.

This construction does not claim that each cosine or sine test is individually integer-null. Their cancellations are collective, as required by the WP01 scope.

## Full pole and gamma audit

No pole is discarded. If beta is nonnegative, let P_+=integral beta(u)e^(u/2)du and P_-=integral beta(u)e^(-u/2)du, both positive. The base difference g_0 has exact pole energy

    2 P_+ P_- (1-e^(L/2))(1-e^(-L/2)) < 0.

The combined cosine/sine pair at frequency t has both corresponding oscillatory Laplace moments. Their products tend to zero as t tends to infinity, by the Riemann-Lebesgue lemma applied separately to beta e^(u/2) and beta e^(-u/2). Since the total modulation weight M is fixed, choosing every t_j>R makes the entire added pole contribution tend uniformly to zero as R tends to infinity. The negative base pole therefore survives exact joint nulling.

This is not a negative full-PBAP witness. Here is a uniform energy check that also retains the two-cluster interference. Write F=paperFT(beta), m=integral beta^2, and use Fourier measure dt/(2 pi). The paired difference density at frequency T and unit weight is exactly

    (1/2) |1-exp(i t L)|^2 (|F(t-T)|^2+|F(t+T)|^2).

Its total mass is 2m, since the physical support intervals are disjoint. Choose K so integral_{|s|>K}|F(s)|^2 dt/(2 pi)<m/4. For either translated F density, the full integral against |1-exp(i(s+/-T)L)|^2 is 2m: the cross Fourier coefficient is psi(L)=0. Removing |s|>K loses at most 4*(m/4)=m. Hence the two bands centered at +/-T together retain at least m of the paired density, even if they overlap (the two density summands are counted separately). Every point counted there satisfies |t|>=T-K. The corpus gamma bound gammaBracket(t)>=log(1+|t|/4)-10 and its global floor -10 therefore give, for T>R>K,

    Gamma(pair of two-cluster differences)
      >= m log(1+(R-K)/4)-20m.

Multiplying by w_j and summing uses only sum w_j=M. The fixed base gamma term is constant, and the added pole tends uniformly to zero as established above. Therefore full energy tends to positive infinity as R tends to infinity. No minimum-energy conclusion follows from this particular realization.

## Stronger boundary obstruction: escape forced by near-minimal mass

**Paper-proved strengthening; Lean pending.** Fix p and beta as above. For every real A there is a delta>0 such that every exact finite nonnegative phase correction with 1<M<1+delta has full (literal gamma plus both poles) two-cluster mixture energy greater than A. This holds without imposing any frequency threshold. The same divergence holds after normalizing the mixture mass to one. Thus the limiting base coefficient theta=1/2 cannot be approached at bounded energy in this fixed-profile family.

Here is a dependency-closed proof. Let a_2=log 2-L, a_3=log 3-L and

    d(t)=2+cos(a_2 t)+cos(a_3 t).

This continuous function is strictly positive on the entire real line. It is nonnegative termwise; a zero would make both cosines -1, contradicting the prime-log independence argument in the nonattainment proof. For each H>=0, compactness of [-H,H] gives a minimum d_H>0. Every exact correction satisfies the identity

    sum_j w_j d(t_j)=2(M-1).

Consequently its total weight with |t_j|<=H is at most 2(M-1)/d_H. As M tends to 1 from above, correction weight leaves every bounded interval, while its total weight tends to one. This is a constraint-forced statement about all feasible corrections, independent of how they were constructed.

Let e(t) be the full energy of the unit-weight cosine/sine pair of two-cluster profiles at frequency t. The preceding Fourier-band proof, with |t| in place of t, gives e(t)->+infinity as |t|->infinity: gamma tends to infinity, and both pole products tend to zero. Also e(t)>=-B globally for some finite B>=0. Indeed gamma is at least -20m, and each polar Laplace integral is uniformly bounded by the corresponding integral of |beta(u)| exp(+/-u/2); the two fixed translation factors are finite. No positivity hypothesis is used.

For any K>0, choose H so e(t)>=K whenever |t|>H. Write b_H for correction weight in [-H,H]. Then

    sum_j w_j e(t_j) >= K(M-b_H)-B b_H,
    0<=b_H<=2(M-1)/d_H.

As M decreases to one, the lower limit is at least K. Since K is arbitrary, correction energy tends uniformly to positive infinity. Adding the fixed base energy changes no divergence conclusion. Total mixture mass is 2m(1+M), tending to 4m>0, so normalization also preserves divergence.

The added pole contribution itself tends to zero under these same constraints: split frequencies at H, use the uniform global bound times b_H inside, and the uniform Riemann-Lebesgue tail bound times M outside. Thus for nonnegative beta the negative base pole persists while gamma necessarily dominates near this weight boundary.

Verdict: **BRIDGE**, not a solution of D2 and not an established claim of scientific novelty. The parent is elementary compactness plus coercivity. This excludes a precise possible failure mechanism for D2: bounded-energy counterexamples cannot approach M=1 with p and beta fixed. It gives neither a uniform gap as p or beta vary, nor the energy sign for M bounded away from one.

## Hostile audit and next conjecture

- False? The finite interpolation proof uses interiority, not a claim that an arbitrary boundary point lies on the orbit. The endpoint M=1 is explicitly excluded and proved unattainable.
- Circular? Neither positivity, RH, a producer, nor a zero-location premise enters. The only arithmetic input is unique factorization.
- Parent theories? Kronecker plus finite positive quadrature explains the construction. Verdict **BRIDGE**; do not claim scientific novelty from its Lean implementation. L376 already sketches the limiting two-phase idea. The exact finite positive correction and fixed broad profile are the audited strengthening here.
- Does it solve D? No. The missing quantity is height-sensitive cost. Small total correction mass does not imply small logarithmic gamma energy. Conversely the null constraints do not force a vanishing base weight merely because there are many nodes.

Next falsifiable target D2: retain all shifted-node constraints in the **minimum full gamma-plus-pole energy** over these finite modulation mixtures, allowing their frequencies and weights to vary jointly. Prove this infimum is nonnegative, or find an admissible negative witness with a dependency-closed proof. A bound on correction mass alone is inadequate; a bound that uses only a single averaged quadrature repeats L376. [OPEN CORE]: the exact height-sensitive lower cost of simultaneous cancellation at the node set log n-(log p)/2.

## Primary-source audit

The finite positive-moment mechanism is classical; see Bayer–Teichmann, *The proof of Tchakaloff's theorem*, Theorem 1 and Corollary 2: https://people.math.ethz.ch/~jteichma/tchakaloff120405.pdf . Their result explains exact finite positive moment representation; it does not assert the PBAP energy sign.

Korolev–Rezvyakova, *On simultaneous approximations to the logarithms of primes* (2022), treats quantitative local Kronecker approximation: https://www.mathnet.ru/php/archive.phtml?jrnid=cheb&option_lang=eng&paperid=1257&wshow=paper . Its abstract gives an interval-length existence bound for prescribed phases, not the sharp logarithmic energy cost needed here. Bailleul's *Explicit Kronecker-Weyl theorems and applications to prime number races*, https://arxiv.org/abs/2007.05763 , is another primary equidistribution parent, not a PBAP result. No external source found in this audit supplies D2.

Additional current primary source: Stefan Kunis, [Positive quadrature and mobile sampling of multivariate trigonometric polynomials](https://arxiv.org/html/2608.11915v1), submitted 2026-08-12. Its exactness assumptions concern full bounded-degree trigonometric polynomial spaces and Haar integration; its covering-radius/curve-length estimates do not immediately supply this sparse shifted-character energy bound. This is an adjacent parent audit, not evidence of novelty.

## Active-node audit and strengthened arithmetic lemma

The construction above intentionally cancels every phase for 2<=n<p. This overdetermines the actual profile constraints: only nodes where psi(log n-L) is nonzero need a phase cancellation. Therefore the mass-one escape result must not be claimed for every actual null modulation family merely from the two equations at n=2,3; those nodes may lie outside the profile's autocorrelation support.

A stronger elementary arithmetic fact removes this particular limitation whenever two distinct nodes are active. For any distinct positive integers n,m<p, the frequencies log n-(log p)/2 and log m-(log p)/2 are rationally independent. Indeed an integer relation u a_n=v a_m gives

    2u log n - 2v log m + (v-u) log p = 0.

The p coordinate of unique factorization forces v=u, since neither n nor m contains p. The relation then becomes u(log n-log m)=0, and n!=m forces u=v=0. Thus their cosines can never both equal -1 at any real time. This proves exactly the strict positivity and compact-band gap of the two-node defect used above, for any such pair.

Consequently the same mass-one cost divergence proof applies to every fixed-profile exact null modulation family having at least two distinct active shifted nodes, without imposing phase equations at inactive nodes. This is a paper-closed strengthening of the obstruction, with formalization pending. It does not cover profiles with fewer than two active nodes and gives no uniform constant as the profile or p varies. The p-coordinate proof also establishes the M>1 classification for cancellation on any subset of {2,...,p-1} containing two distinct nodes; existence follows by restricting the already proved full-system construction. A singleton has attainable mass one, so the two-node condition is a sharp structural distinction.

Hostile verdict remains **BRIDGE**: rational independence, compactness, and coercivity are classical parents. The advance needed for D2 remains a quantitative full-energy lower bound away from this boundary, retaining the actual active nodes. No such bound has been proved here.

Support-bound refinement (paper audit before promotion): the smooth-mixture construction needs only L>W, since that separates the physical clusters and forces all above-cut shifted samples outside [-W,W]. Every prime p>=5 gives log p/2>log 2>W. Thus its full null-mixture conclusion extends from p>=17 to p>=5. The earlier L>2W bound was sufficient but stronger than used. Candidate D's separate L>2W formulation is unchanged. This refinement is elementary and carries no additional novelty claim.

## Exact real-null criterion for complex profiles

The analytic construction also allows complex beta. In that scope the correct active condition is **Re psi(log n-L) != 0**, not merely psi(log n-L) != 0. For support in [0,W], W<log 2, L>=0, the unshifted and positive-shift samples vanish at x=log n, n>=2. Hermitian symmetry and the real weights then give the exact identity

    sum_g c(g) logValue(g,n)
      = -2 Re psi(log n-L) [1+sum_j w_j cos(t_j(log n-L))] / sqrt(n).

For L=log p/2 and p>=5, all n>=p are outside the correlation radius. Hence the full real integer-null condition is equivalent to the phase equations precisely at the real-active nodes 2<=n<p. Since sqrt(n)>0, the reverse implication loses no information. Two distinct real-active nodes therefore suffice for the previously proved logarithmic-cost escape. This is an exact restriction to the actual PBAP null constraints; it does not infer complex nullness from real nullness. Paper proof is closed; this interface extension remains to be checked in Lean.

Formal checkpoint: `JointConvex` and the strengthened `JointPhase` targeted builds pass. The arbitrary-pair logarithmic escape scratch audit passes. Final direct-source/axiom audits and the smooth-mixture bridge remain pending at this checkpoint. Scientific novelty remains unestablished.

## Quantitative coercivity bridge for the literal energy (paper proof)

For fixed nonzero smooth compact beta and fixed L>W, the same argument can be strengthened to constants C>=0 and m=integral |beta|^2>0 such that the literal unit-weight cosine/sine pair energy satisfies

    e(T) >= m log(2+|T|) - C                 (every real T).

This supplies a direct interface to the formal logarithmic-cost theorem. Here is a dependency-closed proof using only the corpus Fourier identities and derivative bound, with no numerical experiment. Let B=integral |beta''|. The corpus's twice-integrated Fourier bound gives |F(s)| |s|^2 <= B on the real axis. For |T|>0 and |xi|<=|T|/2, both |xi+T| and |xi-T| are at least |T|/2. The paired two-cluster density is at most twice the sum of the two shifted Fourier squares, hence at most 64 B^2/|T|^4 on that band. Its integral there, with measure dxi/(2 pi), is at most 64 B^2/(2 pi |T|^3). Choose R so this is at most m for |T|>=R. Total pair spectral mass is exactly 2m by Plancherel and disjoint physical clusters. At least m mass remains outside the band. The global bound gammaBracket>=-10 and the exterior bound gammaBracket>=log(1+|T|/8)-10 give

    Gamma(pair) >= m log(1+|T|/8)-20m.

Since 1+|T|/8 >= (2+|T|)/16, this is at least m log(2+|T|)-m log16-20m. Both pole contributions have a uniform absolute bound independent of T: |cos|,|sin|<=1 bound the two translated profiles' weighted L1 norms by those of |beta(u)|+|beta(u-L)|, and the autocorrelation pole transform is a product of the corresponding two Laplace transforms. Thus e(T) obeys the claimed logarithmic lower bound outside [-R,R]. Globally Gamma>=-20m and the same pole bound hold; increasing C by m log(2+R) covers the remaining compact interval.

For nonnegative weights with M<2, summing gives total mixture energy >= E0+m sum w_j log(2+|t_j|)-2C, where E0 is the fixed base energy. The actual real-active two-node escape theorem therefore yields full-energy divergence as M decreases to one. This quantitative coercivity estimate is paper-proved, **not yet Lean-formalized**. It does not establish any sign at masses separated from one or uniformity under variation of beta or p.


For later variation of p, the pole bound should retain the two opposite translation factors separately. Set A_+=integral |beta(u)|e^(u/2)du and A_-=integral |beta(u)|e^(-u/2)du. Each modulated channel has Fourier values at the two poles bounded by (1+e^(L/2))A_+ and (1+e^(-L/2))A_- respectively. The total paired signed pole is therefore bounded below by

    -4 (1+e^(L/2))(1+e^(-L/2)) A_+ A_-.

This grows on the p^(1/4) scale when L=log p/2, with beta fixed. Replacing both factors by the larger one would introduce an avoidable p^(1/2) loss. No quantitative phase-cost bound uniform in p is supplied by the compactness argument; that remains the substantive height problem.

Final six-leaf checkpoint: all targeted builds and final direct-source audits pass; all 40 named axiom checks report standard axioms only. This completes the finite cancellation, smooth realization, exact real-active criterion and logarithmic-cost escape. Full-energy coercivity and its normalized energy-escape corollary remain paper-only; no route retirement or PBAP completion is claimed.


## Full-mass logarithmic refinement (new paper-closed conjecture)

A stronger lower bound retains the full paired mass. Set ell(x)=log(2+|x|), c0=10+log4 and

    J = integral |F(s)|^2 ell(s) ds/(2 pi).

Then, for every real T and every fixed nonzero profile with L>W,

    Gamma(pair,T) >= 2m ell(T) - 2m c0 - 4J,
    e(T) >= 2m ell(T) - 2m c0 - 4J
            - 4(1+e^(L/2))(1+e^(-L/2)) A_+ A_-.

Proof: triangle inequality gives 2+|T| <= (2+|xi|)(2+|xi-T|), hence ell(T)<=ell(xi)+ell(xi-T); the same holds with xi+T. The established gamma lower bound implies gammaBracket(xi)>=ell(xi)-c0. Write P(xi)=|1-exp(i xi L)|^2, A(xi)=|F(xi-T)|^2, B(xi)=|F(xi+T)|^2 and D=(P/2)(A+B). Since 0<=P<=4 and ell>=0,

    D gammaBracket
      >= D(ell(T)-c0)
         - (P/2)[A ell(xi-T)+B ell(xi+T)]
      >= D(ell(T)-c0)-2[A ell(xi-T)+B ell(xi+T)].

Integrating uses the exact total mass integral D=2m and translation invariance of each log moment. Each translated moment is J, giving the error 4J. All integrals are justified: the corpus proves absolute integrability of |F|^2 gammaBracket and |F|^2 for smooth compact profiles. The pointwise bound 0<=|F|^2 ell<=|F|^2(gammaBracket+c0) then proves integrability of J by domination. The same shifted integrable majorants control the error with P. Both pole terms are retained through the explicit preceding lower bound.

Hostile audit: this proof keeps P in the exact leading mass term; it bounds only the nonnegative error term by P<=4. It works for complex profiles and every real T, needs no recurrence-height premise, and does not assume gamma positivity. It yields a stronger fixed-profile coercivity estimate, not a uniform positive energy sign as p or beta vary. Its parent is elementary logarithmic submultiplicativity plus exact Fourier mass; scientific novelty remains unestablished. Formalization is pending. The inverse-cubic central-band estimate remains a separate quantitative concentration statement and is not required by this refined energy proof.


## Frontier interpretation and remaining test

Two separately audited realization mechanisms now expose the same missing quantity. Narrow integer packets realize prescribed torus moments but have full energy escaping with packet count. Fixed broad modulation profiles admit exact cancellation with base coefficient approaching one half, but their required real frequencies have unbounded logarithmic cost at that boundary. This is evidence about these two constructions, not a universal obstruction theorem for all torus methods.

The resulting research inference is that moment feasibility alone is too weak an invariant for the current route. A viable next theorem must retain the joint moment constraints and the literal frequency cost. In the broad family, the explicit pole scale is p^(1/4), while the full-mass gamma lower bound retains 2m times the logarithmic frequency cost. The open test is a quantitative, simultaneous-constraint lower cost with constants tracked as p and the profile vary, or a fully admissible negative witness. Neither the fixed-profile compactness argument nor a one-average sampling surrogate discharges that test. The full PBAP cone also contains mixtures beyond this modulation family, so solving D2 would still require an extension argument.

JointFourier is also fully Lean-audited: exact Fourier formulas and inverse-quartic central density bound, with targeted build, final source audit and seven standard-axiom checks. Seven Joint leaves and 47 named axiom checks are complete. The full-mass gamma and literal-energy inequalities above remain paper-only.

## Current analytic audit and ancestry

The full-mass estimate is being formalized directly, including the two signed poles. The finite-mixture consequence is

    E(c) >= E0 + 2m sum_j w_j ell(t_j) - C sum_j w_j,

with the explicit nonnegative fixed-profile constant

    C = 2m(10+log4)+4J+4(1+e^(L/2))(1+e^(-L/2))A_+A_-.

For any target A, use the existing actual-real-null logarithmic escape at threshold (A-E0+2C)/(2m), and shrink its delta below 1. Then sum w<2, so E(c)>A. Active real autocorrelation at either selected node forces beta nonzero, hence m>0; no independent nonzero hypothesis is required. Actual mixture mass is exactly 2m(1+sum w), between 2m and 6m in this neighborhood. Applying energy escape to 6m max(A,0) proves E(c)/mass(c)>A. These arguments use the already formal real-null two-active-node theorem, not equations at inactive nodes. This section remains paper status until the final source audits are recorded.

Primary-source audit on 7 October 2026: [Laptev–Weth, Spectral properties of the logarithmic Laplacian](https://www.ma.imperial.ac.uk/~alaptev/Papers/laptev-weth-2020-revised.pdf) provides the classical logarithmically weighted Fourier-form context. [Connes–Consani, Weil positivity and Trace formula, the archimedean place](https://arxiv.org/abs/2006.13771) studies a single-place positivity mechanism; its abstract does not assert the full present null-mixture theorem. [Chen–Chen–Hauer, 2602.06581v5](https://arxiv.org/abs/2602.06581v5), revised 30 September 2026, studies the fractional-logarithmic Fourier symbol. Its abstract supplies adjacent energy-space results, not the actual PBAP gamma-plus-poles inequality. Current work is classified BRIDGE; no scientific novelty or literature-completeness claim follows from this search.

A further extension check follows directly from the exact Fourier factor already proved: every channel in the fixed-L cluster family has transform zero at every real frequency satisfying exp(i xi L)=1, in particular at xi=0. Positive mixing cannot remove these common spectral zeros. General integer-null mixtures need not share them: a nonzero nonnegative smooth test with sufficiently short support is integer-null and has nonzero integral. Therefore an exact representation of the full null cone by one such cluster family cannot be assumed. This is a structural scope check, not a claimed novel theorem; approximation with changing support/family or an additional positive component would need its own energy and null-constraint proof.

## Final formal checkpoint — 8 October 2026

The full-mass gamma bound, explicit two-pole full-energy bound, actual real-null energy escape and mass-normalized escape are now Lean-complete in `JointCoercivity`, `JointEnergy`, and `JointEnergyEscape`. All targeted builds and final direct-source audits pass with empty final diagnostics; 24 new named axiom checks use standard axioms only. This supersedes the earlier paper-only checkpoints in this working proof. Ten Joint leaves and 71 named checks are complete. D2 away from correction mass one and the full PBAP extension remain open; no scientific novelty or full-solution claim is made.

## Current critical-energy attack: an actual phase minorant

Status, 8 October 2026: **OPEN CORE**. The following sufficient certificate is
paper algebra, not a new scientific theorem and not an assumed positivity input
to Lean. Its existence is the research question.

Fix the actual smooth profile beta and prime p from the audited two-cluster
family. Put L=log(p)/2, and let A contain exactly the integers 2<=n<p where
Re autocorr(beta)(log(n)-L) is nonzero. Write a_n=log(n)-L. Let e(T) be the
literal full energy of the cosine/sine cluster pair at modulation T, including
both signed poles, and let E0 be the full energy of the unmodulated cluster.
The definitions give e(0)=E0: the sine test is zero and the cosine test is beta.

**D2-CERT.** There are real numbers d_n, n in A, such that, at every real T,

    sum_{n in A} d_n cos(a_n T) <= e(T).

This is a concrete finite-coefficient existence conjecture for the actual
one-variable energy curve. Construct the coefficients and prove the all-T
inequality; do not insert that inequality as a hypothesis and call the task
solved. Only sufficiency is asserted here, not a dual-attainment equivalence.

The normalization needed for positivity is automatic. Evaluating at T=0 gives
sum d_n<=E0. For every actual nonnegative finite null correction, the audited
active-node equations give sum_j w_j cos(a_n t_j)=-1. Therefore

    E0 + sum_j w_j e(t_j) >= E0 - sum_n d_n >= 0.

This retains the entire actual full energy, every real-active constraint and
arbitrary correction mass. There is no constant Fourier coefficient available
for free: adding a constant changes the inequality by that constant times the
uncontrolled total correction mass. Equations at inactive nodes cannot be used.

Hostile checks:

- The existing coercive floor is 2m log(2+|T|)-C(beta,L). Its negative constant
  cannot be discarded or converted into an allowed zero-frequency atom. That
  floor alone does not construct D2-CERT.
- Three compatible cluster differences can produce frequencies a,b,a+b. Their
  common target -1 under a positive correction forces total correction mass
  at least 2, since
  `3+2cos(ta)+2cos(tb)+2cos(t(a+b))=|1+exp(ita)+exp(-itb)|^2>=0`.
  Equality forces equilateral phases at each used frequency; rational
  independence of a,b excludes finite attainment. This classical Gram bound
  concerns three exact equations, not arbitrary actual multi-cluster nullness.
  It gives no gamma-plus-pole sign and does not justify independent pair repairs.
- A sampled pole-kernel quadrature must still bound its trigonometric error at
  every real height. The verified log-lattice Poisson bound retains a square-root
  height weight. Replacing it by log(2+|T|) repeats the unpaid L380/C383 estimate.
  Compact-band approximation, total-mass control and a pointwise Euler-factor
  cancellation do not supply that replacement.

The next substantive step is a profile-dependent construction of d_n with its
complete signed error controlled by the actual e(T), or a rigorous obstruction
to that construction with its strongest positive survivor. No coefficient
construction or closing paper proof is currently available. Full PBAP stays open.

## Signed modulation kernel — formalized 8 October 2026

Continue with a smooth compact complex profile beta supported in [0,W], now
requiring L>2W and W>0. Write psi(y)=Re autocorr(beta)(y), m=psi(0),
omega(y)=exp(-y/2)/(1-exp(-2y)), and A0=Re digamma(1/4)-log pi.
The already verified paired-correlation identity gives

    Phi_T(y) = 2 psi(y) cos(Ty)
      - psi(y-L) cos(T(y-L)) - psi(y+L) cos(T(y+L)).

This is the real autocorrelation of the actual cosine/sine cluster pair.
It has Phi_T(0)=2m. Gamma's Binet identity and Fourier inversion give

    Gamma(Phi_T) = 2 A0 m
      + 4 integral_(0,infinity) omega(y)(m-psi(y)cos(Ty)) dy
      + 2 integral_(-W,W) omega(L+y) psi(y) cos(Ty) dy.

The two poles together give

    Pole(Phi_T) = 4(1-cosh(L/2))
      integral_(-W,W) cosh(y/2) psi(y) cos(Ty) dy.

Subtracting the T=0 identity and folding the even profile yields the exact
formal capstone

    e(T)-e(0) = integral_(0,W) K_L(y) psi(y)(1-cos(Ty)) dy,

    K_L(y) = 4 omega(y) - 2[omega(L+y)+omega(L-y)]
      + 8(cosh(L/2)-1)cosh(y/2).

All displayed integrals converge. Near zero, the subtraction supplies
1-cos(Ty)=O(y^2), while omega(y)=O(1/y); the shifted terms are smooth on
[-W,W]. Away from zero compact support handles psi. The original Gamma
identity is justified by the corpus Binet/Tonelli theorem and its C2 Fourier
cosine-moment identity. Psi is even even when beta is complex; no complex-null
constraint is substituted for real nullness.

For 0<y<W, both L-y and L+y exceed y. Omega is positive and strictly
decreasing, so 4 omega(y)-2[omega(L+y)+omega(L-y)]>0. The remaining term is
positive. Hence K_L(y)>0. The positive survivor is therefore:

    psi >= 0 on (0,W)  ==>  e(0) <= e(T) for every real T.

In particular every real nonnegative beta meets this domain condition. This
does not assert e(0)>=0. It cannot by itself pay the negative seed energy in
D2-CERT. For arbitrary complex beta, psi need not be nonnegative.

The same formula suggests a precise classification of the stronger
nonnegative Levy-jump residual ansatz. At distinct nonzero absolute active
frequencies, its signed jump measure would have continuous density K_L psi
and atoms d_n. Levy uniqueness would require psi>=0 and d_n>=0; residual
nonnegativity at zero would require e(0)>=sum d_n. Conversely psi>=0 and
e(0)>=0 admit d=0. This classification still needs its actual-source and
uniqueness audit; it is not a finished no-go, and general D2-CERT does not
require this ansatz. No route is retired here.

Ancestry/novelty: L373/L375 supply the real-space Gamma/pole formulas;
JointProfiles supplies the actual paired correlation. The new CCM actual-head
Gamma module independently proves the full-domain Binet--Plancherel identity.
The present calculation is a specialized bridge, not a claimed significant
scientific discovery. Gao's Levy--Khintchine uniqueness theorem is classical:
https://pmc.ncbi.nlm.nih.gov/articles/PMC7604715/ . A finite-dimensional Riesz
extension could also recover a cosine minorant from an already established
null-cone sign; that supplies no independent sign estimate and is not selected
for another wrapper formalization. No primal-attainment claim is made.

Formal checkpoint: `WeilWorkPBAPJointJump` and `WeilWorkPBAPJointModulation`
are wired and pass targeted `--old` builds and final direct-source audits.
All 11 named axiom checks use only standard Lean axioms. The exact increment
is `jointPairFullEnergy_sub_zero`; `jointPairFullEnergy_zero_le` proves the
restricted minimum, and `jointPairFullEnergy_zero` identifies its literal
seed energy. Lean integrates over `(0,infinity)`; the proved support condition
annihilates the integrand beyond W. The general complex profile is retained
in the identity, and real-autocorrelation nonnegativity is an explicit domain
restriction only in the minimum theorem. No PBAP sign is inferred from it.

## Historical crossing proposal — superseded by explicit width

Status: **SUPERSEDED AND SELECTED SECTOR CLOSED**. [JOINT-WIDTH-SECTOR.md](JOINT-WIDTH-SECTOR.md)
constructs W explicitly and proves the concrete negative-seed certificate,
universal real-null energy margin and nonempty prime family in Lean. The
crossing argument below is retained as research history; it is not a missing
premise of the completed proof.

Original proposal: Fix one nonzero real nonnegative smooth
bump phi supported in [0,1], positive in its interior, and use the actual
profiles beta_W(u)=phi(u/W), 0<W<log(2). For every sufficiently large prime p,
put L=log(p)/2. Conjecture: some width W has negative literal seed energy
E0(W), but an actual real-active node n and c>0 satisfy, for every real T,

    -c cos((log(n)-L)T) <= e_W(T).

This is a specific one-node instance of D2-CERT on a nontrivial negative-seed
sector, not a claim about all profiles or a replacement for full PBAP.
Evaluating at zero gives E0(W)+c>=0, and the exact active-node equation pays
the coefficient for every nonnegative finite real-null correction.

Proposed mechanism, all obligations retained:

1. Derive actual small-width normalized Gamma/pole estimates. Seed energy is
   positive for sufficiently small W and negative at a fixed positive width
   once L is large. Construct a zero-energy boundary W0 from this actual family;
   do not add existence of such a boundary as an input assumption.
2. Prove W0 is large enough that a nearest-integer shifted logarithm is inside
   the nonzero autocorrelation interval. No inactive-node equation is usable.
3. Strengthen the exact positive-kernel minimum to strict positivity away from
   T=0 for the nonzero nonnegative bump. Together with the already formal
   coercivity, this bounds e_W0 away from zero on the set where cos(aT)<=0.
   A sufficiently small c>0 then gives a strictly positive residual
   e_W0(T)+c cos(aT) at every T, including T=0.
4. Prove joint continuity in width and modulation and a coercive bound uniform
   in a compact width neighborhood. Only then can the residual margin persist
   to actual nearby widths with negative seed energy. Compact-band continuity
   alone does not handle all heights.

The finite-dimensional continuity step is classical. The research content to
audit is the actual negative-seed sector with all parameters constructed and
the all-height bound proved. Current corpus search is complete at 68,630 files,
with incomplete refresh and mostly pending/source-only compiler metadata.
All candidate/source statements and the ingredient set were inspected. The
suggested zero-deficit/zero-weight chain assumes a Weil-positive completion or
concerns a different energy; it does not prove this conjecture. No literature
novelty or absence claim has been established.
