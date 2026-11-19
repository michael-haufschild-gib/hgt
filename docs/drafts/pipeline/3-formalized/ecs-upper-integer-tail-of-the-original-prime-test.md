# Upper integer tail of the original prime test

Let $\Phi$ be the continuous representative of the forced ECS state, $m=\int\Phi$, $X=e^T$, and $K(v)=e^{-v/2}\{e^v\}$. Put $a_n=\Lambda(n)-1$ and $w_n(t)=n^{-1/2}\Phi(t-\log n)$. For $T\ge1$, $s\ge0$, every integer $k\ge X^4e^s$ and all $U\le T\le M$,
\[
 \left|m\int_U^M K(T-t)
   \sum_{\substack{n>k\\ n>e^t+e^{t/2}\sqrt t}}a_n w_n(t)\,dt\right|
 \le C_\Phi e^{-s/8}.
\]
In particular, truncating the signed row on $(T/6,6T]$ at $\lceil e^{5T}\rceil$ costs $O_\Phi(e^{-T/8})$. The square charge remains in the retained row. [Upper integer tail theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheUpperIntegerTailOfTheOriginalPrimeTest.lean).

For $t\le T$, confinement gives $|w_n(t)|\le C_\Phi e^{2t}/(\sqrt k\,n^2)$ when $n>k$. The sum of $(\log n+1)/n^2$ converges, giving an absolute cost $O_\Phi(X^2/\sqrt k)$.

For $t>R\ge T$ translate by $v=t-\log n$. The kernel is exponential. On the state support $v\le0$, the far-edge condition is $e^{-v}>1+e^{-t/2}\sqrt t$. The right side decreases for $t\ge1$, so the surviving integers through any endpoint $L$ form a terminal interval above $\max(k,\lfloor e^R\rfloor)$. Abel summation of the project Chebyshev bound gives $|\sum_{b<n\le L}a_n/n|\ll_d b^{-d}$ for $0<d<3001/24000$, uniformly in $L$. Subtract the rays at $T$ and $M$ with $d=1/8$. Integration against $e^{-v/2}|\Phi(v)|$ costs $O_\Phi(\sqrt X\,k^{-1/8})$. On each bounded time interval confinement permits $L\to\infty$ by dominated convergence. [Reciprocal interval and time-endpoint estimates](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheLateTimeEndpointOfTheTestedIntegerRows.lean).
