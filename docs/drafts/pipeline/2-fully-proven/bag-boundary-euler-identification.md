# BAG boundary Euler product identification

Target: for every real tau!=0, the ORIGINAL prime-ordered product
 E_tau(N)=product_(p<=N)(1-p^(-1-i*tau))
tends to 1/zeta(1+i*tau). Combined with the formalized mixed Euler tilt
stability, this also identifies every O(1/logN) complex displacement.
Paper proof formalized01ar in ChiRamanujanBoundaryEulerProduct.
Both original boundary and moving-product conclusions audited; P3 card current.

1. Write q_p=p^(-1-i*tau) and R(q)=log(1-q)+q using the principal logarithm.
For every prime norm(q_p)=1/p<=1/2, so1-q_p lies in the slit plane and
norm(R(q_p))<=2/p^2. The R sum is absolutely convergent. The actual prime
partial sums of q_p converge to A_tau by PrimeZetaOneLineConvergence.
Thus sum_(p<=N) log(1-q_p) -> -A_tau+sum_p R(q_p)=:B_tau.
The exact finite exp-sum identity gives E_tau(N)->exp(B_tau), a nonzero value.

2. For sigma>0 put q_sigma,p=q_p*p^(-sigma). The series over primes is
absolutely convergent; exp(sum_p log(1-q_sigma,p))=1/zeta(1+sigma+i*tau)
by the ordinary right-half-plane Euler product. Each R(q_sigma,p) tends to
R(q_p), with the SAME summable majorant2/p^2 for every sigma>=0.
Consequently the summed logarithmic remainder tends to the boundary remainder.

3. The linear prime sum tends to A_tau as sigma decreases to zero.
Let a_n=1_(n prime)*q_n, with a_0=0, and B_m=sum_(n<=m+1)a_n. Exact finite
summation by parts, followed by the absolutely convergent right-hand sum,
gives sum_n a_n*n^(-sigma)=sum_m B_m*w_sigma(m), where
w_sigma(m)=(m+1)^(-sigma)-(m+2)^(-sigma).
The corpus DeningerAbelianTelescope proves w_sigma>=0, its sum is1, and
every fixed weight tends to0. B_m tends to A_tau and is bounded.
For each epsilon, its tail error is bounded by epsilon times total weight1;
the finite head tends to0. This proves the complex Abel limit. Equivalently,
apply the existing real DeningerAbelian_tendsto to the real and imaginary
parts and reconstruct the complex sum, justifying both sums by boundedness.

4. By2and3 the inverse-zeta expression tends to exp(B_tau). Since tau!=0,
zeta is continuous at1+i*tau, away from its pole. Its boundary value is
nonzero by the corpus/mathlib one-line nonvanishing theorem. Therefore the
same expression tends to1/zeta(1+i*tau); uniqueness identifies exp(B_tau).
All factors, principal-log domains, absolute remainder majorants and the
complex Abel passage have explicit proofs available in the preceding steps.

Corpus read: DeningerAbelianLimit, DeningerAbelAverage,
DeningerAbelianTelescope, DeningerAbelSummation, DeningerDirichletAbel/Limit,
HTGeometry/DirichletSeriesBoundedPartialSums; PrimeZetaOneLineConvergence;
new ChiRamanujanOscillatoryLogWindow and ChiRamanujanMixedEulerTilt.
Search58506 nonpartial65945files gen1246322, all20candidate+20source inspected;
background refresh incomplete and older coverage snapshot. Candidate names
still require the prescribed Lean scratch probes before use.

This closes only the intended boundary-Euler ingredient on paper. Full M1
actual rational label responses/collisions, compact-uniform source control,
actual physical profiles and coupled tails, signed axes norm saving,
growing moments and common-height return remain open. RH goal ACTIVE.

01ar audit: scratch61580 terminal0, production35732 terminal0 with one
nonfatal ring information message, axiom20469 terminal0 standard3 for both
public theorems. Index35848 PASS/API2/importonce. Lint35721 has unrelated
unreachable-module errors/existing warnings; no finding in this leaf.
Implementation uses the existing bounded-partial-sum continuation and its
finite-sum limit instead of introducing a separate right-hand prime tsum.
The exact Abel probability-average identity supplies the same boundary
passage; no absolute-prime-series premise is introduced. Search92754
nonpartial65950files gen1246475; all20candidate+20source entries inspected.
