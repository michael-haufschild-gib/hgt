# Logarithmic weights on the square prime factors

For the reduced diagonal generator $q_n=U_n/V_n$ put $e_p=v_p(q_n)$, $X=n^2$, $T=\log X$ and $W(v)=v^{-1/2}[2H(\log v)-H(\log(v/4))]$.

For fixed real $s\ne1$, give each prime factor weight $(\log p)^s$. On the prime support away from the bounded rows, write $\log p=T+\log(p/X)$. Taylor expansion of $(1+\log(p/X)/T)^{s-1}$ against the prime logarithmic measure predicts
$$\sum_p e_p(\log p)^s\sim 2(s-1)n^3T^{s-2}\int W(v)\log v\,dv.$$
The numerator wins for $s<1$, the denominator for $s>1$. For the normalized sum $S_n(s)=\sum e_p\log p\,(\log p/T)^{s-1}$ the derivative near one should be asymptotic to $2n^3T^{-1}\int W(v)\log v\,dv<0$, uniformly on compact exponent intervals. Its unique root near one would then satisfy $s_n-1\sim -T\log(U_n/V_n)/(2n^3\int W\log v)$ along indices with nonzero discrepancy. RH would be equivalent to the one-sided bound $s_n-1\le C T/n$. Establishing the linear drift requires no conjecture about the sign at the critical weight.

For $W_+=\max(W,0)$ and $W_-=\max(-W,0)$, write $M=\int W_+=\int W_->0$ and $J_\pm=\int W_\pm(v)\log v\,dv$. The same expansion separately predicts that the geometric means of the numerator and denominator prime factors, divided by $n^2$, tend to $e^{J_+/M}$ and $e^{J_-/M}$. Their ratio tends to $e^{(J_--J_+)/M}>1$ in denominator-to-numerator order.

The absolute valuation error costs $O(n^2(1+T^{\max(s-1,0)}))$ at fixed $s$, since $p\ge2$ and the prime window ends at $O(n^2)$. The Taylor remainder on the compact support of $W$ costs $O(n^3T^{s-3})$. For the geometric means, apply the same expansion to the positive and negative parts separately before dividing height by factor count. [Absolute prime valuation error](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePrimeExponentsOnTheSquareDiagonal.lean)
