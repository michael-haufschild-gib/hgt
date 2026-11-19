# Reciprocal prime discrepancy above the moving edge

Let $m=\int\Phi$, $A_-=\int e^{-v/2}\Phi(v)\,dv$ and $K(v)=e^{-v/2}\{e^v\}$. Set $T=(7/8)\log k$ and $X=e^T$. For the forced critical state, the signed contribution of all integers above $k=X^{8/7}$ on the original middle interval satisfies
\[
 m\int_{T/6}^{6T} K(T-t)
 \sum_{\substack{n>k\\n>e^t+e^{t/2}\sqrt t}}
 (\Lambda(n)-1)n^{-1/2}\Phi(t-\log n)\,dt
 =m A_-\sqrt X\,R(k)+o_\Phi(1).
\]
Here $R(k)=H_k-\sum_{n\le k}\Lambda(n)/n-2\gamma$ is the limit of $\sum_{k<n\le L}(\Lambda(n)-1)/n$ in integer order. The formula integrates over every center.

For the whole tested weight at $n$, put $y=X/n$. Replacing $\{ye^{-v}\}$ by $ye^{-v}$ gives $mA_-\sqrt X/n$. The error before multiplication by $|m|/\sqrt X$ is at most $y\int_{v\le\log y}|\Phi(v)|e^{-v/2}\,dv$. Cauchy–Schwarz bounds it by $y^{9/2}\|e^{-4v}\Phi\|_{L^2(v\le\log y)}/\sqrt7$. The norm tends to zero at the left endpoint. Summing the absolute errors uses $\sum_{n>k}(\Lambda(n)+1)n^{-9/2}\ll k^{-7/2}$. Thus the infinite whole-weight tail has error $o_\Phi(X^4k^{-7/2})$ as $k/X\to\infty$. [Lean proof for the infinite whole-weight tail](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheReciprocalTermAboveTheTestAbscissa.lean#L288).

For the moving edge, take $L=k^5$, so $X^5\le L\le e^{6T}$. The first-window prefixes through $k$ and $L$ agree for $t\le\log k-1$ because the far edge is at most $e^{t+1}$. Above that time the two prefix bounds and $K(T-t)\le e^{(T-t)/2}$ give an absolute cost $O_\Phi((1+\log k)^2 k^{-1/16})$. The early time cut costs $O_\Phi(e^{-T/12})$. The signed row beyond $L$ costs $O_\Phi(e^{-T/8})$, and $\sqrt X|R(L)|\ll k^{-3/16}$ by the reciprocal interval estimate. All errors tend to zero for these same endpoints. [Moving-edge asymptotic](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheUpperReciprocalTermAtTheMovingEdge.lean#L163).

There are arbitrarily large $k$ with $|R(k)|\le 2/\sqrt k$. Otherwise the discrepancy has one eventual sign, since $|R(n)-R(n-1)|\le(1+\log n)/n\le2/\sqrt n$. For $f(u)=R(\lfloor e^{-u}\rfloor)$ on $u<0$, zero elsewhere, termwise integration gives its Laplace transform at $z>0$ as
\[
 \frac{-2\gamma+\zeta'(1+z)/\zeta(1+z)+\zeta(1+z)}{z}.
\]
With $B(s)=(s-1)\zeta(s)$, the numerator equals $-2\gamma+B'(s)/B(s)+(B(s)-1)/(s-1)$ at $s=1+z$. Its value at $s=1$ vanishes since $B(1)=1$ and $B'(1)=\gamma$. The real continuation is analytic for $z>-1$. The [Landau theorem for a measurable signed tail](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Analysis/LandauTailSignObstruction.lean#L146) then makes $|f(u)|e^{-u/2}$ integrable. The assumed lower bound makes it at least $2$ throughout a negative half-line, a contradiction. [Lean proof of cofinal small values](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/SmallValuesOfTheReciprocalPrimeDiscrepancy.lean#L220).

Along the resulting sequence $\sqrt X|R(k)|\le2k^{-1/16}$. The entire upper contribution tends to zero for either sign of $mA_-$. [Vanishing upper contribution](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheUpperReciprocalTermAtTheMovingEdge.lean#L302).

At $N=\lfloor\sqrt X\rfloor$ the lower prefix is $a(\psi(N)-N)/\sqrt X+o_\Phi(1)$, where $a=(m/2)\int e^{v/2}\Phi(v)\,dv$. The bound $|\psi(N)-N|\ll N^{7/8}$ makes its main term $O_\Phi(X^{-1/16})$. Thus on the same sequence the signed sum over all integers beyond the moving edge differs by $o_\Phi(1)$ from its band $\sqrt X<n\le X^{8/7}$, integrated over every center in $T/6<t\le6T$. [Lower Chebyshev term](ecs-chebyshev-discrepancy-in-the-lower-integer-prefix.md) · [Two-sided localization](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheUpperReciprocalTermAtTheMovingEdge.lean#L380).

The middle interval captures $-5T\le v<5T/6$ after $v=T-t$. Since $K(v)\le e^{-|v|/2}$ and $\int K=-2\operatorname{Re}\zeta(1/2)$, its charge $-m^2/2$ contributes $\operatorname{Re}\zeta(1/2)m^2+O_\Phi(e^{-5T/12})$. A positive limsup for the localized band would therefore exclude the forced state. [Kernel mass](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheSignedOrdinaryPrimeResponseAtEveryLateTime.lean#L23).
