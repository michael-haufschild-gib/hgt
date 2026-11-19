# Removing proper prime powers at sharp quotient endpoints

- **Stage** 1-in-progress
- **Question** Can ordinary primes alone detect the square-root bound in the centered quotient sum, even at the critical exponent of the inversion?

Let \(M_y(t)=\sum_{n\le t,(n,P(y))=1}\mu(n)\). In the centered prime-power reading replace \(\psi_y(X/m)\) by \(\sum_{y<p\le X/m}\log p\), retaining the same rough cofactor and integer floor. Call the result \(R_y(X)\). Transposing the finite divisor rectangle gives the exact equation
\[
 M_y(X)\log X=-R_y(X)-y\Psi(\lfloor X/y\rfloor,y)
 -\sum_{\substack{p>y,\ k\ge2\\ p^k\le X}}\log p\, M_y(\lfloor X/p^k\rfloor)
 +\sum_{k<X} M_y(k)\log(1+1/k).
\]
The last two sums read strictly smaller endpoints. At any \(s\ge1/2\), under an induction price \(Hk^s\) for those rows, logarithmic variation costs at most \(2HX^s\) for \(s\le1\). The proper powers cost at most \(HX^s(\frac12\log X+O(1))\). Squares contribute at most \(\sum_{p\le\sqrt X}\log p/p\le\frac12\log X+O(1)\). Higher powers have uniformly bounded mass since \(\sum_p(\log p)p^{-3/2}/(1-p^{-1/2})<\infty\). The coefficient one half leaves room for the observed reading even at \(s=1/2\).

At \(y=b(X)=\lfloor\log(X+1)\rfloor^2\), the complete smooth population costs \(O_\varepsilon(X^{1/2+\varepsilon})\). Bound the single ordinary-prime reading at each endpoint. Induct over the endpoint, then over all higher prime cutoffs, with price \(CE_s(y)X^s\). The equation closes the first cutoff once \(\log X\) dominates the absolute constants; Euler deletion pays the remaining cutoffs. Restore the full prefix with one more Euler product. Conversely, a full prefix bound controls the old prime-power reading and all smaller frozen rows, hence their proper-power correction. For a general increasing allowance \(v\ge1\), critical inversion costs at most two Euler products at exponent one half. In either direction the raw quotient sum transfers an allowance \(v(X)\sqrt X\) to \(v(X)(b(X)+1)E_{1/2}(b(X))^2\sqrt X\). Every finite power of the latter price has order \(\exp(O(\log X/\log\log X))\). The raw and centered criteria therefore retain this finer scale as well. The required bound on the signed ordinary-prime reading itself is open.

**Lean status.** Exact ordinary-prime decomposition and critical inversion await verification.
