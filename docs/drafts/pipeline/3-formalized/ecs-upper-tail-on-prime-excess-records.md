# The upper integer tail on prime-excess records

For the continuous critical-state representative $\Phi$, put $m=\int\Phi$, $A_-=\int e^{-v/2}\Phi(v)\,dv$, $X=e^T$ and $k=\lceil X^{8/7}\rceil$. In the original signed test on $T/6<t\le6T$, let $P(T,j)$ and $H(T,k)$ be the oriented contributions beyond the moving wall from $n\le j$ and $n>k$, respectively. Write $\Theta=\sup_\rho\operatorname{Re}\rho$. For every $0<d<1-\Theta$,
\[
 |H(T,k)|\le D_{\Phi,d}+B_{\Phi,d}X^{1/2-8d/7}\qquad(T\ge1).
\]

For $E(j)=\psi(j)-j$, the [Chebyshev exponent law](../../../../formal/GaloisForLFunctions/RHTower/ChebyshevErrorExponentLaw.lean#L234) gives $|E(j)|\le Cj^{1-d}$. Both endpoints of the reciprocal Abel sum are bounded by $Ck^{-d}$. Its variation costs at most $(C/d)k^{-d}$, since $j^{1-d}(1/j-1/(j+1))\le (j^{-d}-(j+1)^{-d})/d$. Thus the signed reciprocal sum over $(k,L]$ is $O_d(k^{-d})$ uniformly in $L$.

Take $L=\lceil X^5\rceil$. The infinite moving-edge tail above $L$ is bounded by the [far-tail theorem](../3-formalized/ecs-upper-integer-tail-of-the-original-prime-test.md). On $(k,L]$ the difference between the middle integral and the whole tested weights is bounded. The early error decays as $e^{-T/12}$, and the two first-window costs are $O_\Phi((1+T)^2e^{-T/14})$, since $\log L\le6T$ and $\log k\ge8T/7$. The [whole-weight comparison](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheReciprocalTermAboveTheTestAbscissa.lean#L257) leaves $m A_-\sqrt X\sum_{k<n\le L}(\Lambda(n)-1)/n$ plus an error bounded by the state's eighth exponential norm times $X^4 k^{-7/2}\le1$. These bounds hold for every real $T\ge1$. [Uniform tail theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheUpperIntegerTailOnPrimeExcessRecords.lean#L40).

Under failure of RH let $1/2<\Theta<1$. The [positive band theorem](../3-formalized/ecs-signed-gain-inside-the-central-integer-band.md) gives arbitrarily large records $N$ with a consecutive block $(U,V]\subset[N/2,N]$ of width $\le2N^{1-\kappa}$ and gain $G\ge cN^g$ at $T=\log N+s$, where $g=b-1/2-\kappa$. Set $\kappa=\min((\Theta-1/2)/8,(1-\Theta)/64)$, $b=\Theta-\kappa$, $d=1-\Theta-\kappa$. Then $g>0$ and $g-(1/2-8d/7)=(1-\Theta-22\kappa)/7>0$. For $0\le j\le X^{2/3}$ the [lower-prefix formula](../3-formalized/ecs-chebyshev-discrepancy-in-the-lower-integer-prefix.md) gives $P(T,j)=O_{\Phi,d}(1+X^{-1/2+2(1-d)/3})$ uniformly in $j$. Since $d<1/2$, this exponent is smaller than $1/2-8d/7$. For some $\eta>0$, every sufficiently large one of the selected records therefore satisfies
\[
 |P(T,j)|+|H(T,k)|\le N^{-\eta}G\qquad (0\le j\le X^{2/3}).
\]
The same records and the same original test carry both estimates. At $j=\lfloor X^{2/3}\rfloor$, the block and both exterior ranges together retain at least $(1-N^{-\eta})G$. Since $U\ge N/2$ and $s$ is fixed, these ranges are disjoint for all sufficiently large records. The unresolved cost lies in $(j,k]\setminus(U,V]$. [Same-record theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheUpperIntegerTailOnPrimeExcessRecords.lean#L223).
