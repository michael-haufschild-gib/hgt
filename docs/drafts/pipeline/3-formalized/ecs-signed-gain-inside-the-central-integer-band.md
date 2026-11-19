# Signed gain inside the central integer band

Under failure of RH let $\Phi$ represent the forced state, $m=\int\Phi$ and $\Theta=\sup_\rho\operatorname{Re}\rho$. There is a fixed $s\ge0$ such that for every $1/2<b<\Theta$ and $0\le\kappa<b-1/2$, arbitrarily large integers $N$ admit $N/2\le U<V\le N$ with $V-U\le2N^{1-\kappa}$ and
\[
 m\int_{T/6}^{6T} K(T-t)
 \sum_{\substack{U<n\le V\\n>e^t+e^{t/2}\sqrt t}}
 (\Lambda(n)-1)n^{-1/2}\Phi(t-\log n)\,dt
 \ \ge\ c_{\Phi,b,\kappa}N^{b-1/2-\kappa},\qquad T=\log N+s,\quad c_{\Phi,b,\kappa}>0 .
\]
These integers are comparable to $X=e^T$. Their moving-edge row vanishes for $t\ge\log N$, since $e^t\ge N$ there. Thus the gain in the full middle test occurs before the selected octave $e^t\in(X,RX]$. [Signed band theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/PositivePrimeExcessInsideTheTestedBand.lean#L281).

Write $E(n)=\psi(n)-n$. For $b<b'<\Theta$, the [one-sided Chebyshev exponent law](../../../../formal/GaloisForLFunctions/RHTower/ChebyshevErrorExponentLaw.lean#L149) makes $E(n)-n^b$ unbounded above. At each new record $N$, $E(N)-E(j)\ge N^b-j^b$ for $j\le N$. Fix $1/2<q<r<1$. Minimize $E$ over the integers in $[\lfloor rN\rfloor,N]$ at $L$. For large records, $L\ge qN$ and $P_j=E(j)-E(L)$ satisfies $0\le P_j\le P_N$ on $[L,N]$, with $P_N\ge (1-r^b)N^b$. [Record interval](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/PrimeExcessOnARecordInterval.lean#L68).

Let $W_s(p)$ be the oriented whole tested weight at log abscissa $p$. The positive lower-range half-tilt gives $W_s(0)>0$ for some fixed $s\ge0$. The function $w(x)=W_s(\log x)$ is Lipschitz on $[1/2,1]$ with constant $B$ by the [tested-weight derivative formula](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheStateWeightsAfterTheOriginalFractionalTest.lean#L51). Choose $q$ so $B(1-q)\le w(1)/2$. At $T=\log N+s$ the exact scaling is $\sqrt N\,W_T(\log n)=w(n/N)$. Summation by parts and $0\le P_j\le P_N$ give
\[
 \sum_{L<n\le N}(\Lambda(n)-1)w(n/N)
 \ge \bigl[w(1)-B(1-L/N)\bigr]P_N
 \ge \tfrac12 w(1)(1-r^b)N^b.
\]

Partition $(L,N]$ into at most $\lceil N^\kappa\rceil$ consecutive blocks of width $\lceil N^{1-\kappa}\rceil$. Their signed sums add, so one carries at least $1/(2N^\kappa)$ of the total. For $\kappa>0$ its relative width tends to zero.

In this octave $\log N-\log L\le\log 2$. The early cutoff costs $O_\Phi(e^{-T/12})$ and the two first-window strips together cost $O_{\Phi,s}((1+\log N)^2)$ by the [moving-edge comparison](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheUpperReciprocalTermAtTheMovingEdge.lean#L103). Dividing the whole-weight estimate by $\sqrt N$ leaves a positive power, which absorbs both errors. At these same tests the prefix through $\sqrt X$ contributes $o_\Phi(1)$ and the tail past $\lceil X^5\rceil$ costs $O_\Phi(X^{-1/8})$. For suitable $b,\kappa$ the prefix through $X^{2/3}$ and the tail past $\lceil X^{8/7}\rceil$ together cost a vanishing fraction of the positive block. [Comparison on the record tests](ecs-upper-tail-on-prime-excess-records.md). [Lower prefix and reciprocal cutoffs](../3-formalized/ecs-reciprocal-prime-discrepancy-above-the-moving-edge.md) · [Uniform upper tail](../3-formalized/ecs-upper-integer-tail-of-the-original-prime-test.md).
