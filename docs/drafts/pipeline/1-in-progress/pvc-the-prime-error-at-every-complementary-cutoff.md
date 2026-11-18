# The prime error at every complementary cutoff

**PVC.** Write $E(t)=\psi(t)-t$, $g_D$ for the inner jumps, and $w_R$ for the centered factorial weight. For arbitrary $a$, the complete Mangoldt tail
$$
\sum_{a<v\le X}g_D(v)\sum_{u\le X/v}\Lambda(u)w_R(\lfloor X/(uv)\rfloor)
$$
differs from $\sum_{a<v\le X}g_D(v)E(\lfloor X/v\rfloor)$ by $O((1+M_{D+1})(1+M_R)(1+\log(RX+2))\sqrt X)$. The [factorial estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CenteringTheFactorialPrimeWeight.lean) bounds the difference at each quotient. The [truncated quotient lemma](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnTruncatedQuotientIntervals.lean) then uses bounded prefixes of $g_D$ on every quotient fibre. The cost is uniform even when $X/a$ exceeds the reciprocal prime window.

For the ordinary coprime tail, large repeated first factors cost square-root error by the [prime-multiple bounds](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationOnRepeatedPrimeFactors.lean). Proper powers have bounded half-weight up to logarithms. The [uniform slice saving](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CancellationAcrossComplementaryFactorSlices.lean) handles the short first primes at the moving lower limit $pv>pa$. If $a\ge\lfloor Y/(F+1)\rfloor$, the original product cutoff $Y$ is inactive on the tail with $p>F$.

The full scalar sum has an independent normalization. The unit increment in $g_D$ supplies $E(X)$. A divisor $e$ of the remaining stencil contributes the [complete divisor error](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheCompletedCofactorRowRetainsThePrimeError.lean) at $\lfloor X/e\rfloor$. Its linear mean cancels by $\sum c_e/e=0$. With $A=\lfloor\sqrt X\rfloor$, transposition of $E$ gives a sharper scalar conclusion. For every $n\le X/(A+1)$ the inner sum over $A<v\le X/n$ is the difference of two floor primitives, of size at most $2M_{D+1}$. Since $\sum_{n\le U}|\Lambda(n)-1|\le8U$, the discarded tail costs at most $16M_{D+1}\sqrt X$. Thus
$$
\left|E(X)-\sum_{D<v\le\sqrt X}g_D(v)E(\lfloor X/v\rfloor)\right|
\le M_{D+1}(41\sqrt X+2|\gamma|).
$$
Here $D$ is free. At $D=\lfloor X^\delta\rfloor$ with $0<\delta<1/2$, every retained horizon is below $X^{1-\delta}$ and the error is $O(X^{1/2+\delta})$. Controlling the signed sum of these smaller errors remains open.
