# Reflected composites at the prime midpoint

The all-endpoint route now uses the unique large prime beyond twice the square root. [Joint cofactor blocks and the remaining prime sum](acs-pvc-the-joint-cofactor-block-at-the-reflected-midpoint.md)

For \(n>1\), compare \(3n-k\) and \(3n+k\) for \(1\le k<n\). If \((k,n)>1\), both are composite. Let \(C(n)\) be the sum of \(\log(3n+k)\) over composite right partners with \((k,n)=1\), minus the corresponding sum of \(\log(3n-k)\) over composite left partners. The prime midpoint price \(P(n)=2\theta(3n)-\theta(2n)-\theta(4n)\) has the exact decomposition
\[
 P(n)=C(n)-\sum_{1\le k<n,\;(k,n)=1}\log\frac{3n+k}{3n-k}.
\]
The endpoint integers \(2n,3n,4n\) are composite. If \(6\mid n\), every surviving pair consists of coprime odd integers. Indeed a common prime divides \(2k\) and \(6n\), and \((k,n)=1\) excludes all such primes. [Midpoint and whole-prefix criterion](acs-pvc-two-adjacent-gcd-horizons-and-the-prime-midpoint.md)

**The baseline is a totient to bounded error, on paper.** Put \(c=10\log2-6\log3>0\), \(s=\operatorname{rad}(n)\), \(q=n/s\). The precision available at every endpoint is
\[
 P(n)=C(n)-c\varphi(n)
      -\frac{\mu(s)\varphi(s)}{144n}+O(q^{-3}).
\]
For the proof, Möbius inversion of the displayed coprime sum gives \(\sum_{d\mid n}\mu(d)F(n/d)\), where
\[
 F(h)=\log\!\left(\frac34\frac{(4h)!(2h)!}{(3h)!^2}\right)
     =ch-\tfrac12\log2+\frac1{144h}+O(h^{-3}).
\]
The equality follows by multiplying the \(h-1\) consecutive ratios. Stirling's two-term remainder is uniform down to \(h=1\). The constant term cancels since \(n>1\). The linear term sums to \(c\varphi(n)\). The reciprocal term uses \(\sum_{d\mid n}\mu(d)d=\prod_{p\mid n}(1-p)=\mu(s)\varphi(s)\). Only squarefree \(d\mid s\) contribute to the remainder, so its absolute value is at most a constant times \(q^{-3}\sum_{h\ge1}h^{-3}\). [Stirling expansion and remainder for positive arguments](https://dlmf.nist.gov/5.11#ii)

**Sparse ordinary-factorization test.** At \(n=u^r\) the main term is \(c u^{r-1}\varphi(u)\), and the remainder after the signed correction is \(O(u^{-3(r-1)})\). For all sufficiently large perfect powers with \(r\ge2\) the baseline minus \(c\varphi(n)\) therefore has sign \(\mu(s)\). Here \(s\le u\le q\), so the displayed nonzero reciprocal term has magnitude at least \(1/(144q^2)\). For a fixed \(r\ge2\), moving any integer terminal down to the nearest \(r\)-th power changes each prime-counting endpoint by \(O_r(n^{1-1/r})\) integers. Its log price changes by \(O_r(n^{1-1/r}\log(2n))\). Thus one upper estimate for \(C(u^6)-cu^5\varphi(u)\) by \(O_\varepsilon(u^{5+\varepsilon})\) for all \(u\) is equivalent to the whole-prefix \(11/3\) bound. Replacing six by two and five by one gives an equivalent test for RH. It suffices in each case to test multiples of six for \(u\), since that only multiplies the mesh gap by a fixed constant. Every surviving pair in these tests is coprime. Proving either upper estimate from the reflected composites remains open.

**The remaining prime factors have a short cofactor.** Expand the log of every retained composite by \(\log a=\sum_{q\mid a}\Lambda(q)\). For \((q,n)=1\), the difference between the counts of coprime multiples in the right and left intervals is exactly
\[
 \sum_{d\mid n}\mu(d)\left(\left\lfloor\frac{4n}{dq}\right\rfloor-
 2\left\lfloor\frac{3n}{dq}\right\rfloor+\left\lfloor\frac{2n}{dq}\right\rfloor\right).
\]
Each bracket belongs to \(\{-1,0,1\}\) because the two quotient intervals have the same length. If \((q,n)>1\) both counts vanish. Every \(q\le P\le2n\) occurring here divides a composite, so their combined cost is at most \(2^{\omega(n)}\psi(P)\). The same argument pays all remaining proper powers by \(2^{\omega(n)}(\psi(4n)-\theta(4n))\). Both estimates retain the terminal multiple of \(q\).

For \(n=u^r\), \(r=2\) or \(6\), take \(P=u^{r-1}\) and define
\[
 H_r(u)=\sum_{2\le v<4u,\;(v,u)=1}\;
 \sum_{p>u^{r-1}}
 \bigl(\mathbf1_{3u^r<pv\le4u^r}-\mathbf1_{2u^r<pv\le3u^r}\bigr)\log p .
\]
The inner sum runs over ordinary primes and is finite on its displayed support. Then on paper, at every \(u\ge2\),
\[
 P(u^r)=H_r(u)-cu^{r-1}\varphi(u)+O_{r,\varepsilon}(u^{r-1+\varepsilon}).
\]
Indeed \(2^{\omega(u)}\ll_\varepsilon u^\varepsilon\) and every remaining prime belongs to a composite with cofactor \(v\ge2\). The strict prime cut forces \(v<4u\). At \(r=6\) the large prime is unique. At \(r=2\) two different large prime factors each contribute their own logarithm. Terms with \(p\mid v\) at \(r=2\) cost \(O(u)\), since \(p^2\mid pv\le4u^2\) forces \(u<p\le2u\) and there are at most four such multiples for each prime. The open one-sided test is now \(H_r(u)\le cu^{r-1}\varphi(u)+O_\varepsilon(u^{r-1+\varepsilon})\), even when restricted to \(6\mid u\). It asks only for the signed price of ordinary primes with the stated short cofactors and both product endpoints.

**Opposite main terms at the moving cofactor cut.** Put \(P=u^{r-1}\), \(n=uP\), \(r\ge2\). Take only the first remaining octave of ordinary primes \(P<p\le2P\). Split its right-minus-left price at the cofactor \(v=2u\), with equality in the lower part. In the upper part the continuum length for each prime is exactly
\[
 u\,g(p/P),\qquad
 g(x)=
 \begin{cases}2-2/x&1\le x\le3/2,\\4/x-2&3/2\le x\le2.\end{cases}
\]
Indeed the left interval is truncated to \((2u,3n/p]\) until \(p=3P/2\), then disappears. The right interval keeps the common endpoint and ends at \(4n/p\). Counting coprime cofactors costs at most a constant times \(2^{\omega(u)}\) per prime by Möbius inversion. The upper price through any \(P<W\le2P\) is therefore
\[
 \varphi(u)\sum_{P<p\le W}(\log p)g(p/P)+O(P2^{\omega(u)}).
\]
The lower price has the opposite main term with the same uniform error. Their sum costs \(O(P2^{\omega(u)})\), even for an arbitrary selection of primes in the octave. For the complete octave, partial summation and \(\theta(x)=x+O_a(x^a)\), \(\Theta<a<1\), give upper and lower prices
\[
 \pm c P\varphi(u)+O_a\bigl(\varphi(u)P^a+P2^{\omega(u)}\bigr),
 \qquad c=\int_1^2g(x)\,dx=10\log2-6\log3.
\]
Thus an individual moving cofactor cut carries a signed main term of the full totient size. Its neighbor cancels it prime by prime to the target error already at \(r=2,6\). The cutoff here belongs to the reflected-composite decomposition. The collective price of primes above this octave in the original criterion remains open.
