# The integer weights after the original fractional test

Let $X=e^T$, $m=\int\Phi$, $A=\int e^{-v/2}\Phi(v)\,dv$, $N(s)=\sum_{k\ge1}k^{-1/2}\Phi(s-\log k)$ and $D(s)=N(s)-e^{s/2}A$. Integrating a finite integer row against the original test gives it the real weight
\[
 W_T(x)=\int_{\mathbb R}m x^{-1/2}\Phi(t-\log x)K(T-t)\,dt.
\]
The [fractional primitive](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/IntegerQuadratureAsAFractionalPartConvolution.lean) gives $W_T(x)=-m x^{-1/2}B_0(T-\log x)$ and $B_0'=-B_0/2+D$. Thus $W'_T(x)=m x^{-3/2}D(T-\log x)$. The possible $1/x$ term in the weight has coefficient $mA\sqrt X$. The zero-free Laplace half-plane controls the charge at $+1/2$; $A$ is the different value at $-1/2$.

**Moving far edge.** Parameterize the integer abscissa by $x=g(z)=z+\sqrt{z\log z}$, where $z>X$ is the farthest contributing center for the complementary row. Put $p(r)=\log g(e^r)$, $q=r-p(r)$, $s=T-p(r)$, and $C(q)=m\int_q^0e^{-v/2}\Phi(v)\,dv$. Removing the first window from this finite tested row subtracts exactly $e^{T/2-p}C(q)$ from $W_T(e^p)$, since $K(T-t)=e^{(T-t)/2}$ for $t>r>T$ and the state vanishes past its wall. For the resulting weight $V_T(r)$,
\[
 e^{p-T/2} V_T'(r)=p'(r)\big[m e^{-s/2}N(s)-mA+C(q)\big]
       + q'(r)m e^{-q/2}\Phi(q).
\]
Here $p'\to1$, $q,q'\to0$, and $N(s)=O_\Phi(e^{2s})$ by confinement. As $r,r-T\to\infty$, the scaled derivative tends to $-mA$. [Lean formalization in progress](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheStateWeightsAfterTheOriginalFractionalTest.lean).

**Time-truncation error.** Put $a_n=\Lambda(n)-1$ and $E(Y)=\sup_{L\ge k\ge\lfloor Y\rfloor}|\sum_{k<n\le L}a_n/n|$. The [centered Mertens limit](../../../../formal/GaloisForLFunctions/RHTower/MertensSecondTheorem.lean) gives $E(Y)\to0$. For $R>\max(T,1)$ the signed integral over $t>R$ of every finite row through $L$ has absolute value at most
\[
 |m|e^{T/2} E(e^R)\int_{-\infty}^0 e^{-v/2}|\Phi(v)|\,dv .
\]
Indeed $v=t-\log n\le0$ and $K(T-t)=e^{(T-t)/2}$. At fixed $v$ the residual indices satisfy $e^{R-v}<n\le L$. Imposing the far-edge condition $n>u+\sqrt{u\log u}$ with $u=ne^v$ adds $e^{-v}>1+\sqrt{\log u/u}$. Since $\log u/u$ decreases for $u>e$, the surviving indices are still an interval. The same bound thus pays the true complementary row, uniformly in $L$, at each fixed $T$. This argument concerns ordered sums and uses cancellation before taking absolute values. A bound uniform as $T\to\infty$ requires a rate for $E(e^R)$.

**Remaining estimate.** Isolate the reciprocal polar row with its actual sign and control the variation of the remainder on the middle range. The near-wall scale gives $C(q)=O_\Phi(e^{-r/2})$ and $q'e^{-q/2}\Phi(q)=O_\Phi(e^{-r/2})$. These estimates leave the signed reciprocal prime excess and the full $-m^2/2$ charge in the test.
