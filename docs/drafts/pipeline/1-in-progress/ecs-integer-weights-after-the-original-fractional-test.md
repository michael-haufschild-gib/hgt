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
Here $p'\to1$, $q,q'\to0$, and $N(s)=O_\Phi(e^{2s})$ by confinement. As $r,r-T\to\infty$, the derivative on the left tends to $-mA$ uniformly. This computation uses the actual moving endpoint. An infinite exchange between test and integer series still requires its own signed endpoint estimate.

**Remaining estimate.** Isolate the reciprocal polar row with its actual sign and control the variation of the remainder on the middle range. The near-wall scale gives $C(q)=O_\Phi(e^{-r/2})$ and $q'e^{-q/2}\Phi(q)=O_\Phi(e^{-r/2})$. These estimates leave the signed reciprocal prime excess and the full $-m^2/2$ charge in the test.
