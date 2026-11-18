# A power descent for the actual cofactor count

**PVC · Paper theorem.** Let $E(X)=\psi(X)-X$. Write $g_D$ for the jump of $1-\mathrm{factorialPrefix}(D+1,t)$, extended by zero at $t=0$, and $M_R$ for the divisor stencil mass. For every $D\ge0$, $X\ge1$,
$$
\left|E(X)-\sum_{D<v\le\sqrt X}g_D(v)E(\lfloor X/v\rfloor)\right|
\le M_{D+1}(41\sqrt X+2|\gamma|).
$$
At $D=\lfloor X^\delta\rfloor$ with $0<\delta<1/2$, every summand uses a horizon strictly smaller than $X^{1-\delta}$. More strongly, the original count $C_{V,W}$ reproduces itself with the same $V,W$ throughout. Put $D_N=\lfloor N^\delta\rfloor$. Then
$$
C_{V,W}(N)=\sum_{D_N<v\le\sqrt N}g_{D_N}(v)C_{V,W}(\lfloor N/v\rfloor)
  +O(\|b_V\|_{1,[1,W]}N^{1/2+\delta}).
$$
The constant is uniform in $\delta\ge0,V,W,N$.

**Proof.** Write $c_e$ for the stencil coefficients at $D+1$. Its jumps are $g_D(v)=\mathbf1_{v=1}-\sum_{e\mid v}c_e$ for $v\ge1$. The full sum over $v\le X$ consequently equals $E(X)-\sum_e c_e C(\lfloor X/e\rfloor)$, where $C(t)=\sum_{j\le t}E(\lfloor t/j\rfloor)$. The [complete divisor estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheCompletedCofactorRowRetainsThePrimeError.lean) gives $|C(t)+2\gamma t|\le25\sqrt t$. Replacing $\lfloor X/e\rfloor$ by $X/e$ in the linear term costs at most $2|\gamma|$ per divisor. The reciprocal moment $\sum_e c_e/e=0$ cancels the linear term.

For $a\ge1$, transpose the tail over $v>a$ against the increments $\Lambda(n)-1$. Each $n\le U=\lfloor X/(a+1)\rfloor$ sees two inner prefix endpoints, whose difference has magnitude at most $2M_{D+1}$. Since $\sum_{n\le U}|\Lambda(n)-1|\le8U$, the tail costs at most $16M_{D+1}U$. Take $a=\lfloor\sqrt X\rfloor$ and use $g_D(v)=0$ for $v\le D$. For all $x=\lfloor N/d\rfloor$ the same upper cutoff $a=\lfloor\sqrt N\rfloor$ still costs at most $16M_{D+1}\sqrt N$; terms with $v>x$ have $E(0)=0$. Set $D=D_N$ for every $d$ and use $M_{D+1}\ll D+1$. The two finite sums commute and $\lfloor\lfloor N/d\rfloor/v\rfloor=\lfloor\lfloor N/v\rfloor/d\rfloor$. The inner sum is exactly $C_{V,W}(\lfloor N/v\rfloor)$.
