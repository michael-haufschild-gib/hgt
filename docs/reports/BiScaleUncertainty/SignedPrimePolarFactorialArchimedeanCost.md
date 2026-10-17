# Archimedean cost and signed cancellation of the balanced factorial sources

Status: dependency-closed paper proof and Lean certificate verified; contribution 11.
`SignedPrimePolar.factorialSourceArchimedean_certificate` has only n:ℕ as input
and closes the actual domain, growth, signed-difference and normalized-cost claims.
All notation P_N,M_N,F_N,G_N,H_N,δ,ε is from
`SignedPrimePolarFactorialSourceFactorization.md`, with N≥1 and r=sqrt(N).
Write E(f)=∫₀∞(h_f(0)−h_f(x))w(x)dx, w(x)=exp(x/2)/sinh(x).

## Explicit bounds

Set L=log(4N+1), Q=10^6 N^5 and

B_N=[6L+7+2log Q]/sqrt(N),
U_N=2sqrt(N)[6+32(log(6Q)+π)+60(log(24000N)+π)].

The balanced sources belong to the literal archimedean jump-energy domain.
Their energies obey

6exp(−1/2)sqrt(N)log N−B_N ≤ E(P_N), E(M_N) ≤ U_N,
E(P_N)−E(M_N)=−2∫₀∞H_N(x)w(x)dx,
|E(P_N)−E(M_N)|≤2B_N.

Thus both source costs grow on the sqrt(N)log N scale, although their signed
energy difference is only O(log N/sqrt(N)). These are statements about the
constructed family, not lower bounds for every possible source factorization.

Combining the established origin-energy interval [6r,46r] with these estimates
also gives, for either balanced source V=P_N or M_N,

E(V)/h_V(0) ≥ (3/23)exp(−1/2)log N−[41+2log(10^6)]/6.

The family therefore exposes an explicit normalized logarithmic jump-energy
cost. Its small prime–polar scalar pairing does not hide this source cost.

## 1. Quantitative regularity of the explicit profiles

The clamp qε has |qε(a)−qε(b)|≤|a−b|/ε by the min/max contraction inequalities.
The tent τδ has |τδ(a)−τδ(b)|≤|a−b|. A function vanishing outside [a,b], also
zero at its endpoints, inherits its interval Lipschitz bound globally: for a
point outside the interval, compare the inside point with the nearer endpoint.

On [0,L], exp(x)≤4N+1≤5N and exp(x/2)≤5N. The mean-value bound for the smooth
exponential factors gives |exp(x)−exp(y)|≤5N|x−y| and the same coarse bound for
exp(x/2). Since ε≥δ≥1/(15N), every term qε(j exp(x)/K), 1≤j≤K, has Lipschitz
constant at most 75N². The sum has size at most K and Lipschitz constant at most
75KN². Hence Uε,K has interval Lipschitz constant at most
K(5N+375N³)≤380KN³. The weighted stencil has total coefficient budget
4N+4(2N)+4N=16N. Since sqrt(N)≥1, R_N has Lipschitz constant at most
6080N^4≤10000N^4. R_N vanishes at and outside 0,L, so this bound is global.
Reflection gives the same bound for F_N.

The previously proved square bound R_N(x)²≤4exp(x)/N gives |R_N|≤5 on its
support. Since L≤4N, ∫|F_N|=∫|R_N|≤5L≤20N. Thus the product of the Lipschitz
constant and the L¹ norm is at most 200000N^5≤Q.

For G_N(t)=exp(3t/2)τδ(t)/ε² on [0,2δ], exp(3t/2)≤exp(3δ)=A≤2.
Its exponential factor has Lipschitz constant at most 3 there; τδ≤δ≤1.
The numerator therefore has Lipschitz constant at most 3δ+2≤5. As
ε≥δ≥1/(15N), the global source Lipschitz constant is at most
1125N²≤2000N². Both endpoint values vanish, justifying the global extension.
Finally G_N=exp(t/2)ρ_N, with ρ_N≥0, ∫ρ_N=1, and exp(t/2)≤expδ≤2 on its
support. Therefore ∫|G_N|≤2 and the Lipschitz/L¹ product is at most 4000N².

These bounds are deliberately coarse polynomial estimates. Their logarithms,
not their polynomial sizes, enter the final jump-energy upper bounds.

## 2. Literal energy admission without C²

For any compact continuous globally K-Lipschitz real source f,

0≤h_f(0)−h_f(x)≤K||f||₁|x|,   h_f(0)−h_f(x)≤2||f||₂².

The first upper bound follows by integrating f(u)[f(u)−f(u+x)] in absolute
value. The lower bound and the second upper bound are the existing compact-source
chord/Cauchy inequalities. The integrand is measurable and dominated on x>0 by
K||f||₁ xw(x). The corpus proves ∫₀∞xw(x)dx<∞. Hence the literal jump integral
is absolutely integrable, without an assumed C² approximation.

This admits F_N,G_N and their scaled sums P_N,M_N. Pointwise quadratic identities
can consequently be integrated. They give nonnegative energies and

E(P_N)+E(M_N)=2[r E(F_N)+E(G_N)/r].

Source scalar homogeneity is applied only after actual integrability has been
proved, and the shared mixed terms are retained until this exact identity.

## 3. Quantitative upper bounds

The inspected weight estimates are xw(x)≤3 for 0<x≤1 and
∫_a∞w(x)dx≤log(6/a)+π for 0<a≤1. If the source increment is at most M|x|
and at most K on x>a, splitting the now-admitted integral gives

E(f)≤3Ma+K[log(6/a)+π].

For F_N use M=Q, K=32, a=1/Q, obtaining
E(F_N)≤3+32[log(6Q)+π].
For G_N use M=4000N², K=60N, a=1/(4000N), obtaining
E(G_N)≤N{3+60[log(24000N)+π]}.
Each balanced source energy is nonnegative and at most their sum. The exact
parallelogram identity therefore gives the stated U_N bound for both sources.

## 4. Small signed archimedean contrast, with the factor two fixed

On x>0 the already verified autocorrelation contrast is
(h_(P_N)(x)−h_(M_N)(x))/2=H_N(x). Equal origin energies imply

E(P_N)−E(M_N)=−2∫₀∞H_N(x)w(x)dx.

The coefficient is two, not four. In particular each energy differs from their
mean r E(F_N)+E(G_N)/r by at most |∫H_Nw|.

For x≥0, R_N vanishes on the negative half-line. Its global Lipschitz bound and
ρ_N≥0, ∫ρ_N=1, exp(t/2)≤2 give |H_N(x)|≤20000N^4 x≤Qx/r. The previous
pointwise bound is |H_N(x)|≤2exp(x/2)/r, and H_N vanishes above L.
The linear bound dominates |H_N|w by (Q/r)xw, proving absolute integrability.

Put a=1/Q. On (0,a], xw(x)≤3 gives contribution at most 3/r.
For x≥a, the elementary bound 1−exp(−2x)≥2x/(1+2x) yields

|H_N(x)|w(x)≤[4+2/x]/r.

Integrate only to L+1, since H_N vanishes above L. Here a≤1≤L+1. The tail is
at most [4(L+1−a)+2log(L+1)−2log a]/r. Using log(L+1)≤L and −log a=log Q
gives at most [6L+4+2log Q]/r. Adding the near part proves |∫H_Nw|≤B_N.

## 5. Lower bounds from the narrow factor and normalized cost

G_N is supported in [0,2δ] and vanishes at both endpoints. Thus h_(G_N)(x)=0
for x≥2δ. As 2δ≤1/(6N), this applies on [1/N,1]. On that interval the
inspected reciprocal-weight estimate gives w(x)≥exp(−1/2)/x. Nonnegativity
of the full jump integrand and ∫G_N²≥6N now give

E(G_N)≥6exp(−1/2)N ∫_(1/N)^1 dx/x
       =6exp(−1/2)N log N.

The mean balanced energy is at least E(G_N)/r. The signed contrast estimate
then gives the stated lower bound for each balanced source.
For the normalized bound use 6r≤h_V(0)≤46r, A_N=6exp(−1/2)r log N≥0,
and B_N≥0. Division of E(V)≥A_N−B_N gives
E(V)/h_V(0)≥A_N/(46r)−B_N/(6r).
Finally L≤4N, log N≤N, N≥1, and log Q=log(10^6)+5log N imply
B_N/(6r)≤[41+2log(10^6)]/6, proving the displayed normalized estimate.

## Audit boundary

The prior C² logarithmic-tail and parallelogram results do not themselves admit
these nonsmooth explicit sources. The new package must discharge that gap on the
actual family and verify quantitative signed cancellation. Generic Lipschitz
admission or a renamed classical logarithmic bound alone is not counted.
The local search returned partial=false, no errors and a complete file inventory;
compiler metadata was predominantly pending/source-only and refresh was deferred.
Candidate lemmas and source arguments were inspected. Retrieved C² source lemmas
and compact local-Lipschitz existence results do not supply the explicit bounds.
No external novelty claim follows from this audit.

## Verification

Nine direct leaf compilations passed and wrote oleans. Eleven scratch axiom
audits, including the complete endpoint, use only propext, Classical.choice and
Quot.sound. Current source hashes match `/tmp/spp11-final-manifest.json`.
Every new module is imported once; index refresh passed and lists the endpoint
in `SignedPrimePolarSourceArchimedeanCertificate.lean:97`.
Global lint exits 1 for 22 unrelated unwired modules, listed in the facts ledger;
no package-local error occurs. Evidence: `/tmp/spp11-*.log` and
`/tmp/spp11_final_axioms.lean`. No full/umbrella build or numerical experiment
was run. The field README was not edited.
