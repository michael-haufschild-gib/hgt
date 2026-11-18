# A fixed power descent at square-root precision

**PVC · Formalized.** Take $\eta=1/200$. The implied constant is absolute. With $D=\lfloor N^\eta\rfloor$ and $M=\lfloor N^{1/2+\eta}\rfloor$, the expansion is
$$
C_{V,W}(N)=\sum_{D<v\le M}g_D(v)C_{V,W}(\lfloor N/v\rfloor)
+O(\|b_V\|_{1,[1,W]}\sqrt N).
$$
Every retained argument is below $N^{1-\eta}$ for all $b>1/2$. The tail costs $O((D+1)N/(M+1))$ by transposition. The [complete identity](pvc-a-power-descent-for-the-actual-cofactor-count.md) leaves only the factorial stencil of the elementary divisor remainder. A uniform $O(x^\theta)$ bound for that remainder with $\theta\le 1/2-\eta$ suffices even at full stencil mass $O(D+1)$.

For $s=\lfloor\sqrt x\rfloor$, the symmetric hyperbola formula writes the divisor discrepancy as $-2\sum_{n\le s}(\{x/n\}-1/2)+O(1)$. Indeed $s^2\le x\le s^2+2s$, so $0\le x/s-s\le2$ and $0\le x\log(x/s^2)-(x-s^2)\le (x-s^2)^2/s^2\le4$. The [harmonic half bounds](../../../../formal/GaloisForLFunctions/RHTower/HarmonicHalfErrorBounds.lean) put $2x(H_s-\log s-\gamma)$ between $x/(s+1)$ and $x/s$, whose difference is at most two. The portion $n\le x^{0.49}$ is bounded by its length. The rest lies in the [sharp integer reciprocal interval](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/IntegerCancellationOnMiddleDivisorIntervals.lean), of cost $O(x^{0.47}(1+\log x))$. Stirling contributes $O(1+\log x)$, giving $|C(x)+2\gamma x|\ll (1+\log x)x^{0.49}\ll x^{99/200}$ for $C(x)=\sum_{j\le x}E(\lfloor x/j\rfloor)$. Equivalently the [exact smooth decomposition](../../../../formal/GaloisForLFunctions/RHTower/DivisorHyperbolaAbelBound.lean) differs from twice the centered reciprocal sum by $O(1+\log x)$.

For $1\le x\le N$ the complete stencil consequently costs $O((D+1)(N^{99/200}+1))=O(\sqrt N)$ including its rounded linear part. Since $N/(M+1)\le N^{99/200}$, the tail costs the same. The common cutoffs allow the finite cofactor sum to commute with the dilation at every width. The remaining problem is cancellation among those signed cofactor counts.

**Lean.** [`sum_centered_quotient_to_sqrt`](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/IntegerCancellationOnMiddleDivisorIntervals.lean). [`complete_divisor_error_power`](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/PowerCancellationInTheCompleteDivisorError.lean). [`fixed_gap_cofactor_descent`, `fixed_gap_divided_horizon`](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/AFixedPowerGapInBothVaughanCounts.lean).
