# Odd quotients in the ordinary-prime deficit

If RH fails, the §2.16 tests with exterior gain $cX^g$ also contain a single interval $[a,b]\subset(N,\lceil X^{1+\eta}\rceil]$ and an integer $H\ge X$ with $\sqrt H<a$ such that
\[
 s\sum_{\substack{a\le n\le b\\ \lfloor H/n\rfloor\ {\rm odd}}}
   (\mathbf1_{n\ {\rm prime}}\log n-1)>cX^g\sqrt H .
\]
Here $X=e^T\to\infty$, $X^{1/(1+\eta)}\le N\le X$, and $c,g>0$ are independent of the fixed $0<\eta\le1$. The primes in this sum are exactly the prime divisors of $H!/\lfloor H/2\rfloor!^2$ in $[a,b]$. The sign $s=\pm1$ satisfies $s\,m\Phi(v)<0$ at the displacement $v\le0$ selecting this interval, where $m=\int\Phi$. The endpoints include the original time and moving-edge restrictions. An arithmetic bound ruling out this signed discrepancy on the selected intervals remains open. [Same-test theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheOddQuotientIntervalInTheOrdinaryPrimeDeficit.lean#L326).

**One interval at fixed displacement.** Write $q_n=\mathbf1_{n\ {\rm prime}}\log n-1$. Substitute $t=v+\log n$ separately in each term of the finite band. With $Y=e^{T-v}$, the atom and exponential part of the kernel give exactly $\Phi(v)/\sqrt Y$. Thus the ordinary-prime test is
\[
 \int m\Phi(v)\frac{F_S(Y)}{\sqrt Y}\,dv,\qquad
 F_S(Y)=\sum_{n\in S}q_n\{Y/n\}.
\]
The set $S$ contains precisely $N<n\le L$ with $T/6<t\le6T$ and $1+e^{-t/2}\sqrt t<e^{-v}$. For $T\ge6$, the relative width decreases throughout the time interval. Since $t$ increases with $n$, the surviving indices are consecutive. The [ordinary-prime deficit](../3-formalized/ecs-proper-power-charge-inside-the-diagonal-interval.md) forces some $v$ with $s F_S(Y)>8 B\sqrt Y$, where $s$ has sign opposite $m\Phi(v)$ and $B=cX^g$ after decreasing the fixed coefficient $c$. Otherwise the negative integral costs at most $8B|m|\int|\Phi|$.

**One binary digit.** Let $D_S(H)=\sum_{n\in S,\ \lfloor H/n\rfloor\ {\rm odd}}q_n$. Doubling the numerator gives
\[
 2F_S(Y)-F_S(2Y)=D_S(\lfloor 2Y\rfloor).
\]
If every doubled numerator $z=2^{j+1}Y$ had $sD_S(\lfloor z\rfloor)\le2B\sqrt z$, induction would give $sF_S(2^jY)>8B\sqrt{2^jY}$ for all $j$, since $10\sqrt2<16$. The bound $|F_S|\le\sum_{n\in S}|q_n|$ for this fixed finite set contradicts that growth. Hence some digit exceeds the bound with the required sign. [Digit theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/OddQuotientsInTheFractionalPrimeTest.lean#L68).

**Square-root cutoff.** Put $H=\lfloor z\rfloor$. Discarding all $n\le\sqrt H$ costs at most $(1+\log4)\sqrt H$, using the Chebyshev bound $\sum_{p\le k}\log p\le k\log4$ and at most $k=\lfloor\sqrt H\rfloor$ reference atoms. At all sufficiently late tests $B\ge1+\log4$. The same Chebyshev estimate through $b$ gives $cX^g\sqrt H<(1+\log4)b$. Since $\sqrt H<a\le L\le X^3$ for $T\ge6$, it also exceeds $cH^{1/2+g/6}$. [Square-root cost](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/OddQuotientsInTheFractionalPrimeTest.lean#L127).

**Integer carrying the prime mass.** Put $Q_H=H!/\lfloor H/2\rfloor!^2$. The denominator divides the numerator. For $p>\sqrt H$, Legendre's formula has just one potentially nonzero term at both factorial arguments. Hence
\[
 v_p(Q_H)=\lfloor H/p\rfloor-2\lfloor H/(2p)\rfloor=\lfloor H/p\rfloor\bmod 2 .
\]
This works for odd and even $H$. Thus the prime term in the discrepancy is exactly the sum of $\log p$ over prime divisors of this one integer in $[a,b]$. The reference counts every integer in the interval with odd quotient. [Factorial identity](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheOddQuotientIntervalInTheOrdinaryPrimeDeficit.lean#L181).
