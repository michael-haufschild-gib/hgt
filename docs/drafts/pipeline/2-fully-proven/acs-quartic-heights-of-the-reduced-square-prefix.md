# Quartic logarithmic heights of the reduced square prefix

Write the literal rational prefix \(P_N=\prod_{j=1}^N d_{\rm ord}(jD_j)=U_N/V_N\) in lowest terms. Both \(\log U_N\) and \(\log V_N\) have order \(N^4\) at every sufficiently large endpoint.

## Proof

Choose fixed \(0<u<v<C^{-2}\), where \(v_p(P_N)\ge cp\) for all sufficiently large primes with \(C\sqrt p\le N\). On \(uN^2<p\le vN^2\), the numerator exponent is at least \(cuN^2\), and the logarithmic prime mass is at least \((v-u)N^2/2\) for large \(N\). Thus \(\log U_N\gg N^4\). The reduced denominator divides the product of the single-conductor denominators, whose logarithms are \(O(j^3+j^2)\). Hence \(\log V_N\ll N^4\). The unconditional strip bound gives \(|\log P_N|\ll N^{15/4}=o(N^4)\). As \(\log P_N=\log U_N-\log V_N\), these two estimates give both quartic orders. The ACS target is cubic for their signed difference. [Inner primes](../3-formalized/acs-inner-primes-in-the-reduced-prefix-numerator.md) · [Individual denominator bounds](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheNumeratorAboveSquareRootMultiplicity.lean) · [Signed prefix estimate](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheSignedProductOverSquareConductors.lean)
