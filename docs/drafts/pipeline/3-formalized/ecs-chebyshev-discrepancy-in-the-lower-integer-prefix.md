# Chebyshev discrepancy in the lower integer prefix

Let $X=e^T$, $m=\int\Phi$, $K(v)=e^{-v/2}\{e^v\}$ and $a=(m/2)\int e^{v/2}\Phi(v)\,dv$. Under failure of RH the forced state has $a>0$. For every fixed $C>0$, uniformly in integers $1\le N\le CX^{2/3}$,
\[
m\int_{T/6}^{6T} K(T-t)
 \sum_{e^t+e^{t/2}\sqrt t<n\le N}(\Lambda(n)-1)n^{-1/2}\Phi(t-\log n)\,dt
=\frac{a}{\sqrt X}\bigl(\psi(N)-N\bigr)+o_\Phi(1).
\]
The full oriented row also includes the charge $-m^2/2$ at each center. [Moving-prefix theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheLowerIntegerPrefixAtTheMovingEdge.lean#L418).

For the whole tested weight $W_T(n)$, write $y=X/n$ and $f(z)=\Phi(-z)$. Translation gives $\sqrt X W_T(n)-a=m\int f k_y$, where $k_y(z)=\mathbf 1_{z>0}e^{-z/2}(\{ye^z\}-1/2)$. Let $Q$ be the periodic primitive of $\{x\}-1/2$ with $Q(0)=0$. Its absolute value is at most $1/8$. The right derivative of $e^{-3z/2}Q(ye^z)$ equals $yk_y(z)-(3/2)e^{-3z/2}Q(ye^z)$ on $z>0$. Thus $G_y(z)=\int_0^z k_y$ satisfies $\|G_y\|_\infty\le1/y$. [Kernel and primitive](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheCenteredFractionalTestBelowItsAbscissa.lean#L38).

Put $b=1/y$ and $D(b)=\sup_{0<s\le b}\|f(\cdot-s)-f\|_1$. Each $\int f(z)k_y(z+s)\,dz$ differs from $\int f k_y$ by at most $D(b)$. Its average over $0<s<b$ is $b^{-1}\int [f(z-b)-f(z)]G_y(z)\,dz$, also bounded by $D(b)$. The ground-state increment law gives $D(b)=o(\sqrt b)$. The real Laplace transform has constant sign on $[0,1/2]$, giving $a>0$. Since $\sum_{n\le N}|\Lambda(n)-1|\le7N$, the whole-prefix remainder is $o_\Phi(N^{3/2}/X)$ as $X/N\to\infty$. [State increments](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheFirstAbsoluteMomentOfStateIncrements.lean) · [Signed weights and their sum](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheSignedIntegerWeightsBelowTheTestAbscissa.lean#L173).

For $t>0$ the omitted first window contains at most $e^{t/2}\sqrt t+1$ integers. Each atom is $O_\Phi(e^{-t/2})$ and each coefficient has magnitude at most $1+\log N$. The window is empty for $t\le0$ and its truncated reading vanishes for $t>\log N$. Integration against $K(T-t)\le e^{(t-T)/2}$ costs $O_\Phi(\sqrt{N/X}(1+\log N)(1+\sqrt{\log N}))$. Confinement bounds the complementary prefix by $O_\Phi(e^{2t})$ uniformly in $N$, so removing $t\le T/6$ costs $O_\Phi(e^{-T/12})$. For late $T$ there are no surviving atoms beyond $6T$ in this range of $N$.
