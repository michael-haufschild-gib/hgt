# Diagonal localization of the signed integer test

If RH fails, the forced state has constants $c,g>0$ with the following property. For every $0<\eta\le1$, arbitrarily late original test times $T$ admit an integer $N$ with
\[
 X^{1/(1+\eta)}\le N\le X,\qquad
 S_{\rm int}(T)-B(T,N,\lceil X^{1+\eta}\rceil)\ge cX^g,\qquad X=e^T .
\]
Here $S_{\rm int}$ is the uncharged middle integral, and $B$ is the signed contribution from $N<n\le\lceil X^{1+\eta}\rceil$ in that same integral. The test times may depend on $\eta$. Both constants are independent of $\eta$. Exclusion requires an independent arithmetic lower bound for the signed contribution of this interval. [Original-test theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/APositiveCompletePrefixInTheOriginalTest.lean#L395).

**Signed floor estimate.** Put $d\in(0,1-\Theta)$, $Y=Xe^{-v}$, $w_j=\lfloor Y/j\rfloor$. For $k\le j\le Y$, the Chebyshev upper bound gives $|E(j)-E(k)|\le 2A k^{-d}Y$, where $E(j)=\psi(j)-j$. For $j>Y$, both $w_j$ and $w_{j+1}$ vanish. Summation by parts against $w_j$ costs at most $2Ak^{-d}Y w_k$, including the right endpoint at every $L\ge k$. Thus
\[
 \left|\sum_{k<n\le L}(\Lambda(n)-1)\lfloor Y/n\rfloor\right|
 \le 2A k^{-d}Y^2/k .
\]
In the normalized original weight, split $\{Y/n\}=Y/n-\lfloor Y/n\rfloor$ before estimating. The signed floor contribution integrates against $m e^{v/2}\Phi(v)/\sqrt X$. Confinement gives $\int e^{-3v/2}|\Phi(v)|\,dv<\infty$. The error in the reciprocal main term is therefore $O_\Phi(\sqrt X k^{-d} X/k)$ uniformly in $L$, with a constant also depending on $d$. The reciprocal term itself is $O_{\Phi,d}(\sqrt X k^{-d})$. [Signed floor remainder](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheSignedFloorRemainderAboveTheTestAbscissa.lean#L89).

**Transfer to the original test.** For $k=\lceil X^{1+\eta}\rceil$, split at $L=\lceil X^5\rceil$. The infinite tail past $L$ is bounded, and the cost of restoring the moving edge and time cut through $L$ is $O_\Phi(1+(1+T)^2 e^{-\eta T/2})$. Hence the actual tail is $O_{\Phi,d,\eta}(1+X^{1/2-(1+\eta)d})$ at every $T\ge1$. [Moving-edge tail](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheSignedFloorRemainderAboveTheTestAbscissa.lean#L216).

**Same-time lower prefix.** In the [complete-prefix argument](../3-formalized/ecs-positive-complete-prefix-in-the-original-test.md), choose $0<\delta<\min((\Theta-1/2)/2,\eta(1-\Theta)/4)$, $b=\Theta-\delta/8$, and $d=1-\Theta-\delta/8$. Then $(1+\delta)(1-(1+\eta)d)<b$. The tail is absorbed at the selected time in $[(1+\delta)\log N,(1+\delta)\log N+1]$. The retained power of $N$ is at least $(\Theta-1/2)/2$, uniformly in $\eta$. Taking $\delta<\eta$ gives $T\le(1+\eta)\log N$ eventually and leaves a power of $X$ of at least $(\Theta-1/2)/4$. The charge from §2.16 must still be included when returning to the full ordinary-prime test.
