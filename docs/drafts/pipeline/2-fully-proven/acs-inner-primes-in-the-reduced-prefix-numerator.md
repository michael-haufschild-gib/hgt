# Inner primes in the reduced numerator of every square prefix

There are constants \(c,C>0\) such that for every sufficiently large prime \(p\) and every \(N\ge C\sqrt p\), the reduced rational prefix \(P_N=\prod_{n=1}^N d_{\rm ord}(nD_n)\) has \(v_p(P_N)\ge cp\). Hence none of these primes divides the reduced denominator.

## Proof

Write \(x=\sqrt p\), \(B_j=j^2H(\log(j^2/p))\). The long-lag formula and nonnegativity of the spline autocorrelation give
\[
 v_p(d_{\rm ord}(jD_j))\ \ge\ (2/x)(2B_j-B_{2j+1})-K .
\]
Indeed the exact negative coefficient of \(B_{2j+1}\) inside the parentheses is \(-(j/(2j+1))^2\). The original mesh costs at most \(K_0/x\) per row and the floor costs at most one. Outside the prime horizon both spline terms vanish by their support. [Long lags](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePrimeProfileOfThreeSquareConductors.lean) · [Original quadrature](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheCoefficientIndependentPrimeMeshError.lean)

Choose a constant \(A>\max(e^4,\sqrt D,2)\), where \(D\) is the [mesh-support constant](acs-stabilization-of-individual-prefix-valuations.md). Put \(M=\lceil Ax\rceil\). Each \(B_i\) vanishes for \(i>M\). The map \(j\mapsto2j+1\) is injective, so \(\sum_{j\le M}B_{2j+1}\le\sum_{j\le M}B_j\). On \(x<j\le2x\), each \(B_j\ge p\min_{[0,\log4]}H\), with positive minimum. There are at least \(x/2\) such integers for \(x\ge2\). Thus \(v_p(P_M)\ge p\min_{[0,\log4]}H-KM\gg p\). Every \(N\ge(A+1)x\) has the same valuation by stabilization.
