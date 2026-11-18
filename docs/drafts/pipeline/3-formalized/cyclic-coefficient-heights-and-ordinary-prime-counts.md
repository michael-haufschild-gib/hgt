# Cyclic coefficient heights and ordinary prime counts

For $q=2^{j+1}$ put $P_a(n)=\prod_{k<n}(qk+a)$ for odd $1\le a<q$, $g_q(n)=\gcd_aP_a(n)$ and $h_q(n)=\log(P_{q-1}(n)/g_q(n))$. Write $G_j(n)=\gcd_{0\le i\le j}\binom{2^{i+1}n}{2^in}$. For $n\ge1$,
$$|h_q(n)+\log G_j(n)-n\log(2q)|\le \psi(qn)-\vartheta(qn)+\log(n+1).$$
Consequently RH is equivalent to the following statement. For every $1/2<b<1$, arbitrarily large fixed $q=2^{j+1}$ admit a real $B$ with $\sum_{n<N}(h_q(n)-Bn)=O_{b,q}(N^{1+b})$.

For an odd prime power $m$, label a coordinate by $a=mr\bmod q$. Its multiples of $m$ number $\lfloor n/m\rfloor+\mathbf1_{r\le\lfloor qn/m\rfloor\bmod q}$. The last possible residue $r=q-1$ is attained at an odd label. Minimizing the first level is exact. Interchanging minimum and summation over higher levels costs at most $\lfloor\log_p(qn)\rfloor-1$ at each odd prime, for both the coefficient gcd and the binomial gcd. At two, $g_q(n)$ is odd and $v_2(G_j(n))+v_2(n!)=n$. Summing the valuation differences gives the stated higher-power allowance. Finally $P_{q-1}(n)\le q^n n!\le(n+1)P_{q-1}(n)$. Summing the resulting square-root bound and using the [binomial first-mean theorem](the-first-means-of-dyadic-binomial-gcds.md) proves the equivalence.

The branch $y=(1-z)^{-1/q}$ satisfies $(1-z)y^q=1$. Its powers $y^a$ have degree-$n$ Taylor coefficients $P_a(n)/(q^n n!)$, so $h_q(n)$ is their projective logarithmic height. [Taylor-coordinate identity](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheTaylorCoordinatesOfTheCyclicCover.lean)

Lean declarations: [cyclicCoefficientLevel_at_multiple](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/PrimePowerLevelsOfTheCyclicCoverCoefficients.lean), [cyclicCoefficientHeight_add_log_gcd](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheCommonDivisorOfTheCyclicCoverCoefficients.lean), [riemannHypothesis_iff_cyclicCoefficientHeight_first_means](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheCoefficientHeightsOfCyclicCoversDetectThePrimeWave.lean).
