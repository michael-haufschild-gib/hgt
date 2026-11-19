# One-sided mass in the reciprocal prime octave

Put \(e_n=\sum_{n/2<k\le n}\Lambda(k)/k-\log 2\), \(u^- = \max(-u,0)\), \(u^+=\max(u,0)\). For either sign the paper result is
\[
 \lim_{N\to\infty}\frac{\log\big(\sqrt N+\sum_{\sqrt N<n\le N}e_n^\pm\big)}{\log N}=\Theta .
\]
Lean verifies that a bound of \(A N^{5/6}\) for the total *negative* mass along an unbounded sequence implies \(|B(N)|\ll N^{11/3}\) at every terminal. The arithmetic bound on the negative mass remains open. [Conductor implication](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/BothSignsOfTheReciprocalPrimeOctave.lean#L661)

At \(X_M=\lceil M^{7/6}\rceil\) it suffices that
\[
 \sum_{\sqrt N<M\le N}\left(\log 2-\frac{\log Q_M(X_M)}{X_M}\right)^+\le A N^{5/6}
\]
along an unbounded sequence. The floor comparison gives \(e_{2M}^-\le (\log2-\log Q_M(X_M)/X_M)^+\), and \(e_{2M+1}\ge e_{2M}\). Extending below \(\sqrt N\) costs \(O(\sqrt N)\) since the octave mass is bounded. The independent estimate on this total deficit remains open. [Integer gcd product](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheGcdProductOnOneMangoldtOctave.lean#L90)

All horizons can share one integer \(X=\lceil N^{7/6}\rceil\). With \(I_N=(\sqrt N,N]\cap\mathbb N\), the sufficient estimate becomes the single product inequality
\[
 2^{K N^2}\prod_{M\in I_N}\min\{2^X,Q_M(X)\} \ \ge\ 2^{X|I_N|}
\]
for one fixed integer \(K\) at arbitrarily large \(N\). Taking logarithms divides the total cost by \(X\). The difference between the normalized gcd deficit and \(e_{2M}^-\) is at most \(O(M/X)\), so the whole rounding bill before division is \(O(N^2)\). Removing the proper powers costs \(O(X\sum_{M\le N}M^{-1/2})=O(N^{5/3})\) before division. The minimum retains precisely the horizons where the integer product falls short of \(2^X\).

At the RH scale take \(X=N\lceil\sqrt N\rceil\). For every \(\varepsilon>0\) ask for the same integer inequality with \(K N^2\) replaced by \(\lceil N^{2+\varepsilon}\rceil\), along a sequence which may depend on \(\varepsilon\). The equivalence with RH follows from the two sign exponents: after division by \(X\) the allowed deficit is \(O(N^{1/2+\varepsilon})\). Under RH the bound at \(\varepsilon/2\) absorbs every fixed constant. Rounding and proper powers each cost \(O(N^2)\) before division. At every right zero of real part \(\beta\), the integer loss \(X|I_N|\log 2-\sum_{M\in I_N}\log\min(2^X,Q_M(X))\) is \(\gg_\rho XN^\beta\) for all late \(N\). This lower bound holds for any positive integer \(X\) by the one-sided rounding inequality. Thus the integer loss needed at half power has the same quadratic exponent, with a longer common horizon. This bound remains open.

More generally let \(D_X(N)=X|I_N|\log2-\sum_{M\in I_N}\log\min(2^X,Q_M(X))\). For \(X\asymp N^\alpha\), \(0<\alpha\le3/2\), the quadratic floor and the two sign estimates give
\[
 \lim_{N\to\infty}\frac{\log(N^2+D_X(N))}{\log N}=\max(2,\alpha+\Theta).
\]
At \(\alpha=3/2\) the exponent of quadratic size plus the product loss is \(3/2+\Theta\).

## Positive weights from the divisor identity

Write \(A(k)=\Lambda(k)-2\mathbf1_{2\mid k}\Lambda(k/2)-(\log2)\mathbf1_{k=1}\), \(g(k)=(-1)^{k-1}\log(k/2)\). Then \(e_n=\sum_{k\le n}A(k)/k\) and \(g(k)=\sum_{d\mid k}A(d)\). For integers \(1\le n<X\), set
\[
 w_X(n)=\sum_{d\le X}(-1)^{d-1}\min(1,(X/d-n)^+).
\]
The unsigned terms decrease in \(d\) from one to zero. Hence \(0\le w_X(n)\le1\), and \(w_X(n)=1\) for \(X/2\le n<X\). Summing the clipped lengths over \(n\ge k\) gives \((X/d-k)^+\). Grouping by \(m=dk\) gives the exact signed mean
\[
 \sum_{n<X}e_n w_X(n)
 =\sum_{m\le X}(X/m-1)[g(m)-2\mathbf1_{2\mid m}g(m/2)]
 =\sum_{m\le X}g(m)\min(1,X/m-1).
\]
Here \(n\) starts at one. The multiplier on the right is one through \(X/2\) and decreases to zero thereafter. Partial sums of \(g\) cost \(O(\log(2X))\) by alternating summation against the increasing logarithm. Lean verifies the exact positive mean, the bound \(\log X+\log 2\), and the upper bound for the last-half absolute mass by twice either sign's prefix mass plus this logarithm. [Exact parity mean](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/PositiveWeightsForTheReciprocalPrimeOctave.lean#L143) · [Last-half bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/PositiveWeightsForTheReciprocalPrimeOctave.lean#L240)

The same weights admit a power wave of either sign at each right zero. In fact \(w_X(n)=\int_n^{n+1}\mathbf1_{\lfloor X/t\rfloor\text{ odd}}\,dt\). For \(0<\Re s<1\), replacing \(n^{s-1}\) by \(t^{s-1}\) on each unit interval costs \(O_s(1)\) in total. Including \((0,1)\) also costs \(O_s(1)\). The substitution \(t=X/y\) and alternating summation then give
\[
 \sum_{1\le n<X} n^{s-1}w_X(n)=X^s\frac{(1-2^{1-s})\zeta(s)}{s}+O_s(1).
\]
Consequently the logarithmic signed mean permits a wave of size \(n^{\Re s-1}\) at a zeta zero. The open deficit estimate concerns its individual signs. [Parity symbol in the strip](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/ThePowerModesOfTheOddQuotientMean.lean#L330)

## Each right zero forces both signs on every late window

Let \(\rho\) be any right zero and \(\beta=\Re\rho\). The project supplies an alternating divisor test \(H\), zero below one, with logarithmic increments bounded by \(C\log(y/x)\) for \(1\le x\le y\). Its prime excess test is \(G(X)=\sum_{n\le X}(\Lambda(n)-1)H(X/n)=dX^\rho+O_\rho(\sqrt X)\), \(d\ne0\). Put \(J(y)=H(y)-H(y/2)\). Then \(|J|\le C\log2\) and its logarithmic increments cost at most \(2C\log(y/x)\), also across one by clamping the lower argument there. Write \(G_1(X)=G(X)-G(X/2)\). Expanding the actual atoms gives
\[
 \sum_{k\le X}A(k)J(X/k)=G_1(X)-2G_1(X/2)
 +\sum_{m\le X}(-1)^{m-1}J(X/m)-(\log2)J(X).
\]
The last sum costs \(O_\rho(1+\log X)\) by alternating summation and the logarithmic increment bound. Thus the left side equals \(d(1-2^{-\rho})(1-2^{1-\rho})X^\rho+O_\rho(\sqrt X)\). Neither factor vanishes for \(0<\beta<1\). Abel summation writes the same left side as \(\sum_{n\le X}e_n[nJ(X/n)-(n+1)J(X/(n+1))]\). Each coefficient has modulus at most \(C(\log2+2)\) since \(n\log(1+1/n)\le1\). Consequently \(\sum_{n\le X}|e_n|\gg_\rho X^\beta\) at every sufficiently late endpoint. [Finite wave at any right zero](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/ALocalPrimeWaveAtEveryRightZero.lean#L143)

To separate the signs, average the positive means over all integer terminals \(1\le Y\le N\). Fix \(\sqrt{2N}\le n\le N/2\), \(n\ge2\), and put \(K=\lfloor N/(2n)\rfloor\). For \(0\le k<K\), set \(j=2k+1\). Each \(Y=jn+r\) with \(\lceil n/2\rceil\le r<n\) satisfies \(j(n+1)\le Y<(j+1)n\le N\), since \(j<N/n\le n/2\). The clipped row consists of \(j\) ones followed by zeros, so \(w_Y(n)=1\). Quotient and remainder recover the pair \((k,r)\). The number of these terminals is \(K\lfloor n/2\rfloor\ge N/16\) since \(K\ge N/(4n)\) and \(\lfloor n/2\rfloor\ge n/4\). Thus every such \(n\) receives average weight at least \(1/16\). Positivity of all other weights and the logarithmic signed mean bound the absolute mass from \(\sqrt{2N}\) to \(N/2\) by a constant times either sign's mass through \(N\), plus \(O(\log(2N))\). Since \(e_n=O(1)\) by Chebyshev on one octave, the omitted small indices and the beginning of the target window cost \(O(\sqrt N)\). Both signs thus satisfy
\[
 \sum_{\sqrt N<n\le N}e_n^\pm\gg_\rho N^\beta
\]
for all sufficiently large integers \(N\), including when the off-line zero divisor is infinite. Lean verifies the finite lower bound for each sign with additive error \(O_\rho(\sqrt N+\log(2N))\) and the resulting cofinal implication for \(\Theta\). Taking the supremum over right zeros gives the lower exponent. [Both signs](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/BothSignsOfTheReciprocalPrimeOctave.lean#L579) · [Cofinal width bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/BothSignsOfTheReciprocalPrimeOctave.lean#L633)

For the upper exponent partial summation of \(\psi(n)-n=O_t(n^t)\) on \((n/2,n]\) gives \(e_n=O_t(n^{t-1})\) for every \(\Theta<t<1\). The added \(\sqrt N\) covers \(\Theta=1/2\). At \(\Theta=1\) the uniform octave bound gives the upper exponent directly. [Conductor width equivalence](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheSeventeenNinthsConductorPrefix.lean#L914)

A separate finite transfer uses only the two integer children. For \(D(n)=\psi(n)-n\), \(U_m=\sum_{k\le m}A(k)=me_m-\sum_{1\le j<m}e_j\), one has \(2D(n)=D(2n+r)-U_{2n+r}+r-\log 2\), \(r=0,1\). Averaging gives the harmonic absolute prime mass below \(Y\) at most half its mass below \(2Y\) plus half of \(\sum_{m<2Y}(|U_m|+1+\log 2)/(m+1)\), using weights \(1/(n+1)\). Lean verifies the Abel identity, both children and the harmonic inequality. [Two-child transfer](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/PositiveWeightsForTheReciprocalPrimeOctave.lean#L349)

Sampling only at squares or sixth powers costs one grid interval in total variation. The resulting unweighted criterion is derived in [sparse prime octaves](acs-pvc-sparse-square-and-sixth-power-prime-octaves.md).

Lean verifies the positive linear contribution from distinct noncoprime integers in the corresponding pair sum. Its coefficient and the remaining coprime estimate appear in [the ordinary prime pair sum](acs-pvc-the-noncoprime-part-of-the-ordinary-prime-pair-sum.md).
