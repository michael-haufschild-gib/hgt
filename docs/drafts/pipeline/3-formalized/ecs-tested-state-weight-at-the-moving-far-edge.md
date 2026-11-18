# Signed slope at the moving far edge

Let $\Phi$ be the continuous representative of the forced state, $m=\int\Phi$, and $A=\int e^{-v/2}\Phi(v)\,dv$. Put $g(u)=u+\sqrt{u\log u}$, $p=\log g(e^r)$ and $q=r-p$. Integrate the oriented weight of the row at $x=e^p$ against the original $K(T-t)$ over all centers with $g(e^t)<x$. Write $V_T(r)$ for this integral. For every function $T(r)$ with $r-T(r)\to\infty$,
\[
 e^{p-T(r)/2}\,\partial_r V_{T(r)}(r)\longrightarrow -mA ,
\]
where the derivative holds $T$ fixed. The sign of $mA$ remains open. [Lean theorem](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheStateWeightsAfterTheOriginalFractionalTest.lean#L264).

**Proof.** The function $g(e^t)$ is strictly increasing, so the surviving centers are exactly $t<r$. Write $W_T(e^p)$ for the row integrated over all time and $C(q)=m\int_q^0e^{-v/2}\Phi(v)\,dv$. For $r>\max(0,T)$ the wall at $t=p$ and the exact kernel on $t>r$ give $V_T(r)=W_T(e^p)-e^{T/2-p}C(q)$. With $s=T-p$ and $N(s)=\sum_{k\ge1}k^{-1/2}\Phi(s-\log k)$, differentiating the integer fractional primitive gives
\[
 e^{p-T/2}\partial_r V_T(r)
 =p'(r)\big[m e^{-s/2}N(s)-mA+C(q)\big]+q'(r)m e^{-q/2}\Phi(q).
\]
Confinement gives $N(s)=O_\Phi(e^{2s})$ as $s\to-\infty$. Since $p'\to1$ and $q,q'\to0$, only $-mA$ survives. [Cutoff identity and derivative](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheStateWeightsAfterTheOriginalFractionalTest.lean#L164) · [Exact set of centers](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheStateWeightsAfterTheOriginalFractionalTest.lean#L316).
