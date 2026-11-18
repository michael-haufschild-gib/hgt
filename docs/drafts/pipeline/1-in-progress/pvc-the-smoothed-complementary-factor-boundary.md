# A smoothed complementary-factor boundary below the square root

**PVC · Conjecture.** For fixed $0<\eta<10^{-9}$ and logarithmic cutoffs, use the average of the complementary-factor cutoffs $v\le a$ at integers $a\in[A,A+S)$, where $A=\lfloor X^{1/2-\eta}\rfloor$, $S=\lceil X^{3\eta}\rceil$. Equivalently, retain $v\le A$ with weight one and taper to zero by $A+S$. The conjectured cost at either Vaughan width is square-root error up to logarithms.

Let $G_D(n)=\sum_{v\le n}g_D(v)$, $w_R(0)=0$ for the purpose of taking differences, and $b_R(j)=w_R(j)-w_R(j-1)$. At fixed $a$ and $T=\lfloor X/p\rfloor$ the tail is exactly
$$
\sum_{j\le T/(a+1)} b_R(j)\bigl(G_D(\lfloor T/j\rfloor)-G_D(a)\bigr).
$$
The original product lower bound is inactive here for $p>X^{1/200}$ and large $X$. The [prime-multiple slice estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnRepeatedPrimeFactors.lean) removes coprimality at square-root cost.

Write the divisor stencil of $G_D(n)$ for $n>0$ as $1+\sum_e c_e\{n/e\}$, with $\sum_e c_e/e=0$, and put $m_D=1+\tfrac12\sum_e c_e$. Splitting at $m_D$ leaves one boundary term proportional to $\psi(U_a)-U_a$ at $U_a=\lfloor X/(a+1)\rfloor$. The other term is a centered reciprocal fractional-part sum over $pj\le U_a$. Below $\sqrt X$ absolute counting suffices. Between $\sqrt X$ and $U_a$, the [product-window estimate](../../../../formal/GaloisForLFunctions/PrimeExponentialSums/FractionalPartsAcrossAReciprocalProductWindow.lean) handles long factors; short $j$ still requires the sharp prime estimate for the bare divisor stencil.

The [moving prime-error bound](../2-fully-proven/pvc-averaging-the-prime-error-at-a-complementary-boundary.md) controls the boundary directly: transposition and the quadratic primitive give $O((D+1)^2\lfloor X/(A+1)\rfloor/S)$ after averaging. The open step is the dual stencil estimate on the whole product window and its exact transfer to the tapered row.
