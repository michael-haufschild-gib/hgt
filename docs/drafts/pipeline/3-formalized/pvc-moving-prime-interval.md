# A moving prime interval for both Vaughan counts

**Stage** 3-formalized. **Type** Theorem (Lean). **Route** PVC.

Write $f(m)=\Lambda(m)-1$, $q_j=1+\lfloor L/j\rfloor$, and
$$
 B_L(t)=\sum_{j\le L}\mu(j)(\lfloor t/j\rfloor\bmod q_j),\qquad
 A_L=\sum_{j\le L}(1+q_j).
$$
For $X=\lfloor N/d\rfloor$ put
$$
 T(L,U;X)=\sum_{U<m\le X/(L+1)} f(m)\,[1-B_L(\lfloor X/m\rfloor)].
$$
At any Vaughan width $W$, replacing each $\psi(X)-X$ by $T(L,U;X)$ in the signed count costs at most
$$
 \sum_{d\le W}|b_V(d)|\,
 \big[A_L(25\sqrt N+|2\gamma|)+8(1+A_L)U\big].
$$
With $U=\lfloor\sqrt N\rfloor$ and $L=\lfloor N^{\varepsilon/2}\rfloor$ the cost is $O_{V,W}(N^{1/2+\varepsilon})$, uniformly for $N\ge1$. Thus at both PVC widths the reweighted long variable can be restricted to $\sqrt N<m\le N/[d(L+1)]$ at the required precision.

**Proof.** The complete divisor row $D(Y)=\sum_{k\le Y}(\psi(\lfloor Y/k\rfloor)-\lfloor Y/k\rfloor)$ satisfies $|D(Y)+2\gamma Y|\le25\sqrt Y$. For $Y=\lfloor X/j\rfloor$, summing a single remainder against $f(m)$ gives $D(Y)-q_jD(\lfloor Y/q_j\rfloor)$ by interchanging the divisor sums. Its linear term is $-2\gamma(Y\bmod q_j)$. Summing the resulting bounds with $|\mu(j)|\le1$ costs at most $A_L(25\sqrt X+|2\gamma|)$.

For $1\le t\le L$ the moduli do not change any floor, so Möbius inversion gives $B_L(t)=1$. The factor $1-B_L(\lfloor X/m\rfloor)$ therefore vanishes for $X/(L+1)<m\le X$. Removing $m\le U$ costs at most $(1+A_L)\sum_{m\le U}|f(m)|\le 8(1+A_L)U$. Apply these estimates at each divided horizon. Finally $A_L\le L(L+2)\le3N^\varepsilon$ for the stated choice.

**Open.** Bound the signed sum of the $T(L,U;\lfloor N/d\rfloor)$ with the actual coefficients $b_V(d)$ at both widths. The estimate above bounds the error of replacing the count by that sum.

**Lean.** `abs_mangoldt_remainder_sum_le` bounds the complete weighted prime excess. `abs_cofactorCount_sub_middle_power_le` proves the moving-cutoff estimate. [Prime count between two moving cutoffs](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/ThePrimeCountBetweenTwoMovingCutoffs.lean)
