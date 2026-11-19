# Sharp variation at the log-square wall

- **Stage** 1-in-progress
- **Question** Which part of the observed variation comes from the rough signed head, and which from the smooth floor center?

The signed difference between the original floor-centered reading and the corrected interior equals \(-y\Psi(\lfloor X/y\rfloor,y)\) up to \(\sqrt X\log X\), uniformly in the selected Mangoldt weights. At the log-square wall the smooth lower bound therefore forces this particular difference to be negative at every large endpoint, with ratio tending to one against the negative center. Its magnitude also gives a lower bound for the full path variation from a fixed starting cut. The same identity keeps the negative smooth bias at a polynomial wall.

**Sharpness question.** For the natural log-square wall and the hyperbola head, the proposed total variation for the Mangoldt weight is asymptotic to \(e^{-\gamma}\sqrt X\log X/(4\log\log X)\). The square at \(d^2\) contributes \(|\mu_{b(d^2)}(d)|\log d\). A jump from \((k-1)^2\) to \(k^2\) in the primorial changes only coefficients divisible by a prime in that interval. The total absolute change at that jump is \(O(e^{k/2})\), by counting multiples, hence \(O(\sqrt X)\) over all such jumps. The remaining input is the weighted squarefree rough population at its moving cutoff. For ordinary primes the extra singly squared prime must exceed the cutoff; determining its contribution gives a second test of the leading coefficient.

For a height path with \(H_{i+1}-H_i\in\{0,1\}\) and increasing walls \(Y_i\), each arriving prime \(p>Y_N\) raises the head by \(\log p\) when the wall and reading agree. If the wall changes at that step, discard the prime. The discarded log mass is at most \((Y_N-Y_0)\log H_N\), since each nonzero integer wall increment costs one. Thus the variation of either genuine reading is at least
\[
 \vartheta(H_N)-\vartheta(\max(H_0,Y_N))-(Y_N-Y_0)\log H_N .
\]
This remains true up to \(o(H_N)\) at the log-square wall for arbitrary proper-power edits whose total variation at each atom is at most \(B\Lambda(q)\). At a switch sum the common-height coefficients *with signs* first. They give \(\sum_q\Delta a(q)M_{Y_i}(\lfloor H_i/q\rfloor)\). At any fixed exponent \(\Theta<s<1\) their total absolute price is at most a constant times \(BE_s(Y_N)H_N^s\sum_{q\text{ nonprime}}\Lambda(q)q^{-s}\), which is \(o(H_N)\) for polynomial-height paths. Consequently, along \(H_i=\lfloor i^\alpha\rfloor\) for \(0<\alpha\le1\), the full path variation has power exponent \(\alpha\). The half-plus threshold for total variation is exactly \(\alpha\le1/2\); the signed terminal price has the distinct threshold \(\alpha\Theta\le1/2\).
