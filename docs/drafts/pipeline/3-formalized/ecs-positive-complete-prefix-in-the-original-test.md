# A positive complete prefix in the original test

Suppose RH fails. Write $\Theta=\sup_\rho\Re\rho$, $P(T,N)$ for the oriented middle integral over every integer through $N$ beyond the moving wall, and $H(T,k)$ for the corresponding infinite tail. For all sufficiently small fixed $\delta>0$, there are $c,g>0$ and arbitrarily large integers $N$ admitting a test time
\[
 (1+\delta)\log N\le T\le(1+\delta)\log N+1,\qquad
 P(T,N)-|H(T,\lceil e^{8T/7}\rceil)|\ge cN^g.
\]
Every integer through $N$ is included. The only remaining contribution to the uncharged middle integral is the consecutive interval $(N,\lceil e^{8T/7}\rceil]$. [Complete-prefix theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/APositiveCompletePrefixInTheOriginalTest.lean#L437).

Let $m=\int\Phi$, $a=(m/2)\int e^{v/2}\Phi(v)\,dv>0$. For the whole tested weight $W_T(p)$ at log abscissa $p$, translation gives $e^{T/2}W_T(p)=a+r(T-p)$, where $r$ is continuous and $|r(u)|\le e^{-u/2}$ for all sufficiently large $u$. [Normalized lower weight](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheSignedIntegerWeightsBelowTheTestAbscissa.lean).

Put $q=\log N$, $S=(1+\delta)q$, $Z=e^{-\delta q/2}$ and $w(p)=\int_S^{S+1}r(t-p)\,dt$. On $0\le p\le q$ both $|w(p)|\le Z$ and $|w'(p)|=|r(S-p)-r(S+1-p)|\le2Z$. Discrete summation by parts against $E(j)=\psi(j)-j$ bounds the absolute mean prefix error by $Z(1+2q)\max_{j\le N}|E(j)|$. A maximum over the unit interval gives one original test whose normalized whole prefix is at least $a E(N)$ minus this error.

Choose $0<\delta<\min((\Theta-1/2)/2,(1-\Theta)/32)$, $b=\Theta-\delta/8$, $\theta=\Theta+\delta/8$. The one-sided Chebyshev exponent law gives $E(N)>N^b$ arbitrarily late, by rounding down from real arguments. Its upper bound gives $\max_{j\le N}|E(j)|\ll_\theta N^\theta$. The mean error is $o(N^b)$ since $\theta-\delta/2<b$. [Chebyshev exponent law](../../../../formal/GaloisForLFunctions/RHTower/ChebyshevErrorExponentLaw.lean#L149).

The physical prefix differs from its whole tested weights by $O_\Phi((1+q)^2)$ throughout this unit interval, from the first-wall-strip and early-time bounds. Multiplying by $e^{T/2}$ still gives $o(N^b)$ since $(1+\delta)/2<b$. The real-time upper-tail bound with $d=1-\theta$ gives $e^{T/2}|H|\ll e^{T/2}+e^{(1-8d/7)T}$. Here $0<1-8d/7<1$ and $(1+\delta)(1-8d/7)<b$, so this too is $o(N^b)$ at the selected time. Division by $e^{T/2}$ gives $g=b-(1+\delta)/2>0$. Splitting the complete moving-edge row at $N$ and $k=\lceil e^{8T/7}\rceil$ shows that subtracting just the band $(N,k]$ from the uncharged test leaves $P(T,N)+H(T,k)\ge cN^g$. [Moving prefix](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheLowerIntegerPrefixAtTheMovingEdge.lean) · [Uniform upper tail](../3-formalized/ecs-upper-tail-on-prime-excess-records.md).
