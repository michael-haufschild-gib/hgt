# A smooth midpoint on products with many distinct prime factors

There is a single smooth signed weight \(W(k/n)\) supported inside the two original intervals. For **every fixed** \(m\ge2\), the corresponding prime midpoint is a price on coprime composites with more than \(m\) distinct primes and no dominant prime-power block, less an explicit arithmetic center, to \(O_{m,\varepsilon}(n^{1/2+\varepsilon})\). Its upper exponent at every integer has the same zero-abscissa criterion as the sharp midpoint. The comparison between the sharp and smooth observables is a spectral equivalence.

**Weight and visibility.** Take \(a=9/4,b=3,c=15/4\), \(h=\log(65/64)\), and let \(U\) be the sum of independent uniform variables on \([-h/2^i,h/2^i]\), \(i\ge1\). Set
\[
 W(y)=\mathbb E[\mathbf1_{(b e^U,c e^U]}(y)-\mathbf1_{(a e^U,b e^U]}(y)],\qquad
 D_W(x)=-\sum_p\log p\,W(p/x).
\]
The transition intervals about \(a,b,c\) are disjoint and lie inside \((2,4)\). Symmetry of \(U\) gives \(W\le0\) left of 3 and \(W\ge0\) right of 3. Its Mellin transform is
\[
 \widehat W(s)=\frac{c^s-2b^s+a^s}{s}
 \prod_{i\ge1}\frac{\sinh(hs/2^i)}{hs/2^i}.
\]
The product converges locally uniformly and has no zero for \(\Re s>0\), since the tail differs from one by a summable quadratic error. Any fixed number of initial factors yields that many powers of vertical decay, with the remaining product bounded by \(e^{h|\Re s|}\). Fourier inversion in \(\log y\) gives \(W\in C_c^\infty\). Strict concavity gives \(2b^\sigma>a^\sigma+c^\sigma\) for \(0<\sigma<1\). Thus \(\widehat W(1)=0\) and every strip zero is visible. [Sharp midpoint multiplier](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L363)

**One-sided transfer.** The derivative of \(D_W(x)\) is bounded for \(x\ge1\), by \(\theta(4x)\ll x\) and bounded \(W'\). An upper bound at integers therefore holds at real scales. For \(\Re s>1\) the Mellin integral of \(D_W(x)x^{-s}\,dx/x\) on \([1,\infty)\) equals \(-\widehat W(s)\sum_p(\log p)p^{-s}\) up to an entire correction from \(x<1\). Proper powers give a holomorphic correction to the logarithmic derivative for \(\Re s>1/2\). The real pole at one is canceled and every nonreal zero in this half-strip gives a pole. If \(D_W(x)\le Cx^t\), apply the Mellin integral to \(Cx^t-D_W(x)\ge0\). Its real abscissa cannot exceed \(t\): at a larger finite abscissa the continuation is regular, and Taylor expansion at a nearby point to its right integrates nonnegative powers of \(\log x\) term by term, giving convergence to its left. This excludes all poles with \(\Re s>t\). Conversely the usual prime-error bound at every exponent above the zero abscissa gives the smooth estimate by partial summation, using \(\int W=0\). Thus for \(1/2\le\beta<1\) the upper estimates for every \(\beta<t<1\) are equivalent to \(\Theta\le\beta\). [Sharp all-endpoint criterion](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L319)

**Arithmetic support and center.** Use the integer weight \(V_m(k)\) below. Its first term is a fixed linear combination of \(j^{\omega(k)-1}\), \(1\le j\le m\). Its second term counts small unitary divisors with weight \(K_m(\omega(d))\). Primes and pure powers have weight one. Every mixed dominant product and every product with \(2\le\omega(k)\le m\) has weight zero. Every balanced product of exactly \(m+1\) blocks has weight \((-1)^{m-1}m!\). Subtracting the all-coprime center from the weighted composite price gives \(D_W(n)\) exactly. All primes in support exceed \(2n\). Removing pure composite powers costs \(O(\sqrt n\log(4n))\). [Integer weight and support proof](acs-pvc-the-smooth-composites-opposite-the-large-prime-source.md#an-integer-weight-constant-on-the-first-surviving-class)

For the small unitary divisors use the progression densities on \(x>d^2\) with the smooth factor \(W(x/n)\log x\). Bounded variation costs one logarithm per divisor row, hence \(O_{m,\varepsilon}(n^{1/2+\varepsilon})\) after summation. For a positive arity \(j\), the coefficients \(\mathbf1_{(k,n)=1}j^{\omega(k)}\) are \(h_{j,n}*\tau_j\), where \(\tau_j\) counts unrestricted ordered products of \(j\) integers. The local polynomials for \(h_{j,n}\) are \((1+(j-1)z)(1-z)^{j-1}\) at \(p\nmid n\), and \((1-z)^j\) at \(p\mid n\). The former have zero linear coefficient. Hence \(\sum_d|h_{j,n}(d)|d^{-1/2-\delta}\ll_{j,\delta,\epsilon}n^\epsilon\) by absolute Euler products; at primes dividing \(n\), compare the large local factors with \(p^\epsilon\).

For each coefficient \(h_{j,n}(d)\), write \(Y=n/d\). In an ordered product \(v_1\cdots v_j\asymp Y\) distribute weight among the coordinates using
\[
 \eta_i=\frac{\chi(v_i/(\prod v_l)^{1/j})}{\sum_l\chi(v_l/(\prod v_l)^{1/j})},
\]
where \(0\le\chi\le1\) is smooth, zero through \(1/2\) and one from 1 onward. The denominator is at least one. Fix the other factors with product \(e\). Replace the sum over the selected coordinate \(v_i\) by its real integral, retaining \(\eta_i W(dev_i/n)\log(dev_i)\). This specifies the arithmetic center. Here \(e\ll_jY^{1-1/j}\). Every logarithmic derivative of \(\eta_i\) is bounded uniformly in the other factors. Euler summation of order \(B\ge2\) costs \(O_{j,B}(\log(2n)(Y/e)^{1-B})\), by the integral of the absolute \(B\)-th derivative of the compactly supported row. The other factors have \(O_{j,\delta}(e^\delta)\) choices. Summing costs \(O_{j,B,\delta}(\log(2n)Y^{1-B/j+\delta})\) for \(Y\ge1\); \(1/4\le Y<1\) costs \(O_j(\log(2n))\). Choose \(B\ge j\), then apply the absolute coefficient bound. The total error is half-plus for each fixed arity, uniformly in the midpoint. This center uses no prime-error estimate.

### A price on entirely smooth integers

Fix \(0<\delta<1/2\). Put \(X=4n,\ y=X^\delta,\ L=\lceil1/\delta\rceil,\ D=X/y\). There is a second reading whose actual products have **every** prime factor at most \(y\). It has an explicit center depending only on small primes and the Laurent coefficients of \(\zeta\) at one.

Let \(R(k)\) indicate integers all of whose primes exceed \(y\), including the unit. Use Dirichlet convolution \(*\) and its unit \(\mathbf1_*\). On \(k\le X\) the convolution logarithm of \(R\) truncates at order \(L\): every nonunit in \(R\) exceeds \(y\). Its price times \(\log k\) equals \(\Lambda(k)\) on powers of primes above \(y\), zero elsewhere, by the Euler factors. For \(k>1\), expansion of the logarithm gives
\[
 (\log_*R)(k)=\sum_{j=1}^L b_jR^{*j}(k),\qquad
 b_j=(-1)^{j-1}\binom Lj/j.
\]
Indeed \(\sum_{l=j}^L\binom lj/l=\binom Lj/j\). Write \(R^{*j}=B_{j,y}*\tau_j\), where \(B_{j,y}(d)=\mu^{*j}(d)\) on \(y\)-smooth integers and zero elsewhere. This follows by multiplying the local Euler polynomials \((1-z)^j\) at the primes through \(y\).

For \(d\le D\) replace the complete inner sum over \(r\) by
\[
 M_j(n,d)=\operatorname*{Res}_{s=1}
 (n/d)^s\zeta(s)^j[\widehat W(s)\log n+\widehat W'(s)].
\]
Mellin inversion gives an error \(O_{j,B,W}((n/d)^{-B}\log(2n))\) for any fixed \(B>0\). Shift to \(\Re s=-B\), using rapid vertical decay of both transforms and polynomial growth of \(\zeta\) in a fixed strip. Here \(n/d\ge y/4\) and \(|B_{j,y}(d)|\le\tau_j(d)\ll_{j,\epsilon}d^\epsilon\). The summed replacement error is \(O_{\delta,A}(n^{-A})\) for any fixed \(A>0\) by taking \(B\) sufficiently large. For \(d>D\), a contributing product \(k=dr\le X\) has \(r<y\). Both factors and hence \(k\) itself are \(y\)-smooth. With \(P^+(1)=1\), this gives
\[
 -D_W(n)=\sum_{j=1}^L b_j\left[
 \sum_{d\le D}B_{j,y}(d)M_j(n,d)+
 \sum_{\substack{2n<k<4n\\P^+(k)\le y}} W(k/n)\log k
 \sum_{\substack{d\mid k\\ d>D}} B_{j,y}(d)\tau_j(k/d)\right]
 +O_{\delta,W}(\sqrt n).
\]
The last error pays for proper prime powers, priced by \(\log p\). This is a signed identity on actual integers; the center retains the contributions of all completed divisor rows with their signs.

**Coprime products and every endpoint.** At a sufficiently large prime center \(n\), one has \(y<n\), so every surviving smooth product is automatically coprime to \(n\). Such centers suffice for the full criterion. Differentiating twice gives \(|D_W''(x)|\ll_W1/x\) by the Chebyshev upper bound. Bracket each large \(x\) by primes in \([x-O(x^{2/3}),x+O(x^{2/3})]\), applying the prime-gap theorem above and below \(x\). Linear interpolation of the two measured values incurs \(O_W(x^{1/3})\), since the second derivative is bounded on the intervening interval. The interpolant is a convex combination, so one-sided upper estimates transfer to every scale. This step retains the half-power gate. [Prime-gap theorem](../../../../formal/GaloisForLFunctions/RHTower/PrimeShortIntervalsSevenTwelfths.lean#L63)

**Open input.** At every prime center bound the negative of the displayed smooth-integer sum plus its prescribed signed center. For any one fixed \(\delta\) this suffices for the \(11/3\) criterion at exponents above \(5/6\), or for RH at every exponent above \(1/2\). The ability to take arbitrarily small fixed \(\delta\) changes the available prime factors; it supplies no sign estimate on the smooth products. The smooth transfer and center estimates are paper proofs. [First strip equivalence](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L337)
