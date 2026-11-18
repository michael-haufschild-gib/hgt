# A smoothed complementary-factor boundary below the square root

**PVC · Conjecture.** For fixed $0<\eta<10^{-9}$ and logarithmic cutoffs, use the average of the complementary-factor cutoffs $v\le a$ at integers $a\in[A,A+S)$, where $A=\lfloor X^{1/2-\eta}\rfloor$, $S=1+\lfloor\sqrt X/(A+1)\rfloor$. Equivalently, retain $v\le A$ with weight one and taper to zero by $A+S$. The conjectured cost at either Vaughan width is square-root error up to logarithms.

Let $G_D(n)=\sum_{v\le n}g_D(v)$, $w_R(0)=0$ for the purpose of taking differences, and $b_R(j)=w_R(j)-w_R(j-1)$. At fixed $a$ and $T=\lfloor X/p\rfloor$ the tail is exactly
$$
\sum_{j\le T/(a+1)} b_R(j)\bigl(G_D(\lfloor T/j\rfloor)-G_D(a)\bigr).
$$
The original product lower bound is inactive here for $p>X^{1/200}$ and large $X$. The [prime-multiple slice estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnRepeatedPrimeFactors.lean) removes coprimality at square-root cost.

Write the divisor stencil of $G_D(n)$ for $n>0$ as $1+\sum_e c_e\{n/e\}$, with $\sum_e c_e/e=0$, and put $m_D=1+\tfrac12\sum_e c_e$. Splitting at $m_D$ leaves the boundary coefficient $m_D-G_D(a)$ times $\sum_{p>F}\log(p)w_R(\lfloor U_a/p\rfloor)$, where $U_a=\lfloor X/(a+1)\rfloor$. The other term is a centered reciprocal fractional-part sum over $pj\le U_a$. Below $\sqrt X$ absolute counting suffices. Between $\sqrt X$ and $U_a$, the [product-window estimate](../../../../formal/GaloisForLFunctions/PrimeExponentialSums/FractionalPartsAcrossAReciprocalProductWindow.lean) handles long factors. For $j\le X^{10^{-6}}$ and logarithmic stencil divisor $e$, put $Z=X/(ej)$. A nonempty prime block at $P$ has $X^{0.4999}\le P\le X^{0.5001}$ and $X^{0.9999}\le Z\le X$ for large $X$. Thus $P^{1.998}\le Z\le P^{2.002}$, the range of the [prime fractional-part estimate](../../../../formal/GaloisForLFunctions/PrimeExponentialSums/FractionalPartsOfReciprocalPrimes.lean).

For the boundary term at each $p$, apply the [moving-prefix estimate](../2-fully-proven/pvc-averaging-the-prime-error-at-a-complementary-boundary.md) at $T=\lfloor X/p\rfloor$ to $u_j=b_R(j)$. Every $j$ retains one interval of $a$, and $|b_R(j)|\ll R$. Summing $\log(p)/p$ and dividing by $S$ costs $O((D+1)^2 R(1+\log X)X/((A+1)S))$. Summing the [dual stencil](../2-fully-proven/pvc-the-dual-divisor-stencil-through-the-product-window.md) over the moving endpoints still requires its exact transfer to the tapered coprime row.
