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

**The critical logarithmic weight.** For fixed real $s\ne1$, give each prime factor weight $(\log p)^s$. On the prime support away from the bounded rows, write $\log p=T+\log(p/X)$. Taylor expansion of $(1+\log(p/X)/T)^{s-1}$ against the prime logarithmic measure predicts
$$\sum_p e_p(\log p)^s\sim 2(s-1)n^3T^{s-2}\int W(v)\log v\,dv.$$
The numerator wins for $s<1$, the denominator for $s>1$. For the normalized sum $S_n(s)=\sum e_p\log p\,(\log p/T)^{s-1}$ the derivative near one should be asymptotic to $2n^3T^{-1}\int W(v)\log v\,dv<0$, uniformly on compact exponent intervals. Its unique root near one would then satisfy $s_n-1\sim -T\log(U_n/V_n)/(2n^3\int W\log v)$ along indices with nonzero discrepancy. RH would be equivalent to the one-sided bound $s_n-1\le C T/n$. Establishing the linear drift requires no conjecture about the sign at the critical weight.
