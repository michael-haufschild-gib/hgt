# Exact joint phase cancellation and its unpaid energy cost

Status: dependency-closed paper proof of the finite cancellation statement below; Lean audit pending. **BRIDGE**, scientific novelty unestablished. Parent mechanisms are Kronecker recurrence, separation and finite positive quadrature. Full PBAP and Candidate D remain OPEN. This statement closes an exactness gap in the L376 two-frequency sketch; it does not prove a cheap cancellation theorem.

## Statement

Let p>=17 be prime, L=(log p)/2, and 0<W<log 2. Fix any nonzero real smooth function beta supported in [0,W]. Write psi(x)=integral beta(u+x) beta(u) du. For every M>1 and every real R there are finitely many frequencies t_j>R and positive weights w_j such that

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

The finite phase classification itself already holds for every prime p>=5. The stronger bound p>=17 is used only for the broad-profile support conclusion L>2W. The proof and hostile audit below apply unchanged to that arithmetic strengthening: it only requires the three distinct primes 2, 3, p. Lean exposed no new analytic premise here.

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

Since p>16 and W<log 2, L>2W. For 2<=n<p the phase identity kills Psi(log n-L). For n>=p, log n-L>=L>W and support of psi in [-W,W] kills the sample. Thus the shifted-null property holds for every n>=2, including all nodes above the finite interpolation range.

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
