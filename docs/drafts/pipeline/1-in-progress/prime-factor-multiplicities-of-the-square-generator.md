# Prime-factor multiplicities of the square generator

Write $U_n/V_n$ for the reduced generator at $m=n$ and $X=n^2$. The numerator and denominator have logarithmic order $n^3$. Does the numerator systematically contain more prime factors counted with multiplicity?

Let $H$ be the autocorrelation and $W(v)=v^{-1/2}(2H(\log v)-H(\log(v/4)))$. The log moment is strictly negative:
$$\int W(v)\log v\,dv=-2\log4\int H(\log v)\,dv/\sqrt v.$$
For $T=\log X$, the identity
$$T\sum_p W(p/X)=\sum_p W(p/X)\log p-\sum_p W(p/X)\log(p/X)$$
removes the zeroth moment. The first sum is $O(n^{1+2w})$ at the actual zero width $w<1/2$. On the compact support of $W$, $T/\log p\to1$ uniformly. The prime number theorem applied to $W(v)\log v$ therefore gives $T^2X^{-1}\sum_pW(p/X)\to-\int W(v)\log v\,dv$. The unrounded dyadic row at $m=n$ is $2nW(p/X)$. The summed absolute substitution, quadrature and floor errors are $O(n^2)$, negligible on the $n^3/T^2$ scale. This predicts
$$\frac{(\log n^2)^2}{n^3}\big(\Omega(U_n)-\Omega(V_n)\big)\longrightarrow 4\log4\int H(\log v)\,dv/\sqrt v>0.$$

In the adjacent-factorial presentation $p=p!/(p-1)!$, balance requires exponent $-\sum_p e_p$ at $1!$. Its Stirling entropy is $\sum_p e_p[p\log p-(p-1)\log(p-1)]$, exceeding the log generator by $\sum_p e_p+O(n^2)$. The correction at $1!$ consequently exceeds the target scale despite the small sum of the individual $O(1/p)$ discretization errors. This distinguishes inequality of the multiplicities from inequality of the logarithmic sizes.

[Dyadic prime weight](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheDyadicPrimeWeightOfSquareConductors.lean) · [Reduced prime products](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ReducedOrdinaryPrimeProducts.lean)

The centered measure has a signed translation law for every continuous test $g$. With $F(u)=H(u)e^{u/2}$ its reading is $2\int [g(u)-g(u+\log4)]F(u)\,du$. It is strictly negative for each strictly increasing test. The signed cumulative mass through $u$ equals $2\int_{u-\log4}^{u}F(v)\,dv$, although the total mass is zero. The individual valuation comparison and its quadratic error are formalized in `diagonal_prime_exponent_profile_error`. [Prime exponents on the diagonal](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePrimeExponentsOnTheSquareDiagonal.lean)
