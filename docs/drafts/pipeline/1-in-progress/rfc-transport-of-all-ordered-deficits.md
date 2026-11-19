# Can one prime row receive all unmatched children?

- **Stage** 1-in-progress
- **Question** Can the largest-pair move transport all negative excesses of a maximum ordered-fibre matching?

Write \(S=X/c\), \(b=cq\), \(T=S/q\), \(t=\log q/\log S\), and \(a=\log q/\log T=t/(1-t)\). The old row has negative prime endpoints at scale \(T\); the eligible positive pairs have smaller factor above \(q\). For \(a<1/2\) the asymptotic ratio of pairs to primes is
\[
 H(a)=\int_a^{1/2}\frac{dv}{v(1-v)}.
\]
Only the positive part of \(1-H(a)\) needs new primes. At \(a\ge1/2\) the whole row is deficient. The new demand relative to the prime supply at \(c\) integrates against \(dt/[t(1-t)]=da/a\).

**Exact capacity at first order.** Replacing the integrand of \(H\) by its minimum four gives demand bounded by the function that is zero below \(1/4\), equals \(4a-1\) on \([1/4,1/2]\), and equals one on \([1/2,1]\). Its total cost is exactly
\[
 \int_{1/4}^{1/2}(4a-1)\frac{da}{a}+\int_{1/2}^1\frac{da}{a}=1.
\]
**Strict spare capacity.** The identity \(1/[v(1-v)]=4/[1-(1-2v)^2]\) gives \(H(a)\ge2-4a+(2/3)(1-2a)^3\). For \(1/3\le a\le3/8\), the cubic correction saves at least \(1/96\) of the prime row. Thus total limiting demand is at most \(1-\log(9/8)/96\).

The discrete theorem needs uniform lower bounds for old semiprime rows and an integrated upper bound on the positive part of the actual prime deficit. Transporting all unmatched children retains the signed sum. Keeping all previously matched negative vertices imposes a further capacity condition on the adjacent rows.

**Uniform integer quadrature.** Write \(A(n)=\sum_{p\le n}(\log p)/p\) and \(h=\log S\). Give prime \(p\) the interval \((A(p-1)/h,A(p)/h]\). These intervals are consecutive and have exactly the required weights. Mertens' first theorem places both endpoints within \(C/h\) of \((\log p)/h\), uniformly in \(p\ge2\). For a Lipschitz test of constant \(K\), integrating on each assigned interval in place of its value at the prime incurs at most \((KC/h)\) times the total mass. The two physical window endpoints cost at most \(2C\|f\|_\infty/h\). This gives uniform control even for a varying positive-part cutoff.

**Discrete deficit.** For \(T=S/q\), subtract the number of distinct pairs \(q<r\le\sqrt T<s\) with \(T<rs\le2T\) from the number of available prime endings, taking the positive part separately for each \(q\). Here \(r\le\sqrt T\) and \(s>T/r\) guarantee \(s>r\). For \(q\le S^{1/17}\), the replacement band \((T^{1/16},T^{1/2}]\) fits inside this supply and has no deficit. The cap \(\sqrt S<q\le\sqrt{2S}\) costs \(O(S/\log^2 S)\) since both final primes are comparable to \(\sqrt S\).

On the remaining compact exponent range the ordinary prime theorem is uniform at every complementary scale. The two required numerator tests have primitives \(\log(t/(1-t))\) and \(4/(1-t)-\log(t/(1-t))\), for the weights \(k(t)\) and \((4t/(1-t)-1)k(t)\), respectively. Split at \(t=1/5,1/4,3/11,1/3\). The signed primitive contributions give the exact unit leading cost above; the curvature saving occurs on \([1/4,3/11]\). The floor endpoints and the complementary prime-count errors still have to be carried through the positive parts in Lean.
