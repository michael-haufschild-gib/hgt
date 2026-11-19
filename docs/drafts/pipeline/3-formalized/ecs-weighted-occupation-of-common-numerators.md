# Weighted occupation of common numerators

In [§2.16, step 3](../../../reports/review-1911/obstacles-summary.md#216-programme-to-close-ecs), consider two prescribed intervals $(u_i,v_i]$ with positive odd quotients $q_i$. At terminal block length $D$ their joint admissible integer numerators are exactly $A\le H<B$, where
$$
 A=D+\max(q_1v_1,q_2v_2),\qquad B=\min((q_1+1)(u_1+1),(q_2+1)(u_2+1)).
$$
Indeed the smallest quotient on each rectangle of numerators and denominators occurs at $(H-D,v_i)$ and the largest at $(H,u_i+1)$. Increasing $D$ consumes the common overlap one integer at a time. [Common numerator range](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheWeightedOccupationOfPairedQuotientCells.lean#L54).

Put $X=e^T$. For any physical time set in the middle test, retain only atoms whose actual displacement $v=t-\log n$ can realize the pair at **some** binary digit, with any further measurable restriction such as its state orientation. The absolute integral of their contribution to the original oriented ordinary-prime band $k<n\le L$ is at most
$$
 C_\Phi L X^{-1/2}\max(0,\log B-\log A).
$$
This includes both signs, the moving physical edge, and all binary digits at once. The outer multiplier is the integral of the original state. The estimate is zero once $A\ge B$. [Oriented pair bound](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheWeightedOccupationOfPairedQuotientCells.lean#L318).

**Weighted occupation.** More generally let $W$ be a measurable, bounded-above region of log numerators of finite length. A displacement $v$ is eligible if $T+(j+1)\log 2-v\in W$ for some $j\ge0$. The atom times the original kernel has absolute value at most $X^{-1/2}e^{v/2}|\Phi(v)|$, by $0\le\{e^{T-t}\}<1$. The state vanishes for $v\ge0$ and satisfies $|\Phi(v)|\le C e^{2v}$. Thus the displacement weight is bounded by $C g(v)$ with $g(v)=e^v\mathbf1_{v\le0}$. Write $b(v)=\min(1,e^v)$ and $h=\log2$. Then $g(v)\le2(b(v)-b(v-h))$. For every $z$,
$$
 \sum_{j<J}g(T+(j+1)h-z)\le2.
$$
The upper bound on $W$ bounds all contributing digit positions on $v\le0$. Translation and reflection on the real line therefore bound the weighted occupation by $2C\,|W|$, with overlapping hits charged only through this uniform sum. [All binary lifts](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheWeightedOccupationOfPairedQuotientCells.lean#L146). The ordinary coefficients have total absolute mass through $L$ at most $(1+\log4)L$ by Chebyshev's bound. This proves the integral estimate with $C_\Phi=2C|m|(1+\log4)$ for any measurable subset of the eligible displacements. [Original test](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheWeightedOccupationOfPairedQuotientCells.lean#L240).

For a finite list of possible common numerators use the **union** of their unit log intervals $[\log H,\log(H+1))$. Its length is at most $\sum_H1/H$. If all listed numerators are at least $X$, deleting every eligible displacement changes the signed reading by at most $C_\Phi L\,\#N/X^{3/2}$. In particular a list carrying a fixed fraction of a deficit of size $cX^g$ must have order at least $X^{3/2+g}/L$ distinct common numerators. [Signed removal bound](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Wall/TheWeightedOccupationOfPairedQuotientCells.lean#L455). The missing arithmetic input is an upper bound for the log measure occupied by the full family of state-oriented adverse pairs on the selected tests.
