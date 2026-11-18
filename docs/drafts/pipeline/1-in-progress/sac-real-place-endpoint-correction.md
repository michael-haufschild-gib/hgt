# The real-place endpoint correction to the mixed graph height

**Target.** Sum the actual directed off-diagonal Frobenius intersections $\Gamma_i\cdot\Gamma_m/i$ over $i<m\le j$ before gluing lower divisors and upper endpoints. The finite-place part should be $\psi(\lfloor j/i\rfloor)$ with the same normalization as the integer graph orders.

**Archimedean term.** For $j\ge i>0$, set $H_k=\sum_{a=1}^k1/a$. Partial fractions predict

$$
\sum_{i<m\le j}\frac{m^2}{m^2-i^2}
=j-i+\frac i2 H_{2i}-\frac i2(H_{j+i}-H_{j-i}).
$$

At $j=i$ the two harmonic terms cancel. At larger $j$ the last term is a reciprocal window of length $2i$, of size at most $i^2/(j-i+1)$. Its sign matters for opposing upper divisors. The other three terms separate into functions of the two degrees. The diagonal self-intersection is outside this directed sum. [Off-diagonal Frobenius identity](../../../../formal/GaloisForLFunctions/AbsoluteGeometryOfSpecZ/WeilsOffDiagonalIsContactsPlusJets.lean)

**Full lower divisor.** Transpose at fixed upper degree $m>0$. The jet sum is $m(H_{m-1}+H_{2m-1}-H_m)/2=mH_{2m-1}/2-1/2$. The contact sum is $\sum_{q\mid m}\Lambda(q)=\log m$. Thus a single independently evaluated column should control all signed upper divisors, with the archimedean and finite-place terms retained together. The arithmetic issue for a restricted lower divisor is precisely which complementary terms survive.

**Including the diagonal.** In the existing flat-divisor gauge the exact real variation at $j=i+k$ is $D_i(k)=H_{i+k}-(H_k+H_{2i+k})/2$. A candidate positive measure for its Hankel matrix has moments

$$
2D_i(k)=\int_0^1 x^k(1-x)\left(\sum_{a=0}^{i-1}x^a\right)^2\,dx.
$$

This would retain the real contribution as one positive quadratic form after arbitrary signed endpoint gluing. The Chebyshev remainder, the fractional boundary and the diagonal constant still enter the full pairing. [Flat-divisor gauge](../../../../formal/GaloisForLFunctions/HodgeTheoryOfAFixedPart/WeilsFormInTheGaugeOfTheFlatTail.lean)
