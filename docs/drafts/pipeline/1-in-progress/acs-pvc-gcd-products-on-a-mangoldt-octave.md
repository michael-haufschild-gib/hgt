# Gcd products on a Mangoldt octave

**Finite gcd identity (Lean verified).** Set \(L_j=\operatorname{lcm}(1,\ldots,j)\). For any integers \(M,X\ge1\) define
\[
 Q_M(X)=\prod_{u=1}^X\frac{\gcd(u,L_{2M})}{\gcd(u,L_M)},\qquad
 \log Q_M(X)=\sum_{M<d\le2M}\Lambda(d)\lfloor X/d\rfloor.
\]
Write \(E(M)=\sum_{M<d\le2M}\Lambda(d)/d-\log2\). Subtract the two finite gcd logarithms and count multiples. At \(X=2M\), every floor is one and the product reduces to \(L_{2M}/L_M\). At \(X=M^2\), each divisor keeps its actual multiplicity. The discrepancy \(X(E(M)+\log2)-\log Q_M(X)\) lies between zero and \(\psi(2M)-\psi(M)\ll M\). [Exact finite product](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheGcdProductOnOneMangoldtOctave.lean#L69) · [Rounding and proper-power bounds](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheGcdProductOnOneMangoldtOctave.lean#L90)

**Arithmetic target (paper reduction).** A lower bound \(\log Q_M(M^2)\ge M^2\log2-A M^{11/6}\) would give the whole-prefix \(11/3\) estimate by the Mellin transform below, without any prior strip bound. At every exponent \(3/2+\varepsilon\), the analogous lower bounds characterize RH. For the \(11/3\) implication one may already take \(X=\lceil M^{7/6}\rceil\) and ask for \(\log Q_M(X)\ge X\log2-A M\). Division by \(X\) gives the same one-sided \(M^{-1/6}\) tolerance. [Whole-prefix width equivalence](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheSeventeenNinthsConductorPrefix.lean#L914)

At this shorter horizon proper powers cost \(O(X/\sqrt M)=O(M^{2/3})\): their total Mangoldt weight in the octave is \(O(\sqrt M)\) and each has at most \(X/M\) multiples. Removing them leaves the nonnegative ordinary-prime sum
\[
 \sum_{1\le v\le X/M}\big[\theta(\min(2M,X/v))-\theta(M)\big].
\]
Each cofactor \(v\) is at most \(\lceil M^{1/6}\rceil\), and the common lower prime endpoint is retained. Its lower bound by \(X\log2-O(M)\) would suffice for §2.18.

The endpoint identities distinguish ordinary factorization from edited weights. For \(M<u\le2M\), the only divisor of \(u\) in the octave is \(u\) itself. Hence \(\log Q_M(u)-\log Q_M(u-1)=\Lambda(u)\). Preserving the integer products through \(2M\) fixes every weight in the octave. The rounding inequality alone holds for any nonnegative weights.

For an actual right zero \(\rho\), a lone quartet of multiplicity \(m\) is equivalent to
\[
 \log Q_M(M^2)-M^2\log2 =
 -2m\Re\!\left(\frac{2^{\rho-1}-1}{\rho-1}M^{1+\rho}\right)
 +O( M^{3/2}\log^2 M).
\]
For \(D(t)=\psi(t)-t\), partial summation gives \(E(x)=D(2x)/(2x)-D(x)/x+\int_x^{2x}D(t)/t^2\,dt\). Insert the single Chebyshev wave and use the finite floor bound. Conversely divide by \(M^2\) to recover the octave wave. Passing to real lower endpoints adds at most one upper prime-power term of size \(O(\log M/M)\). Put \(R_\Lambda(x)=\sum_{d\le x}\Lambda(d)/d-\log x+\gamma\). Partial summation of the known Chebyshev error gives convergence of \(R_\Lambda\); the Laurent constant \(-\gamma\) of \(-\zeta'/\zeta\) at one fixes its limit at zero by Abel summation. Since \(E(x)=R_\Lambda(2x)-R_\Lambda(x)\), summing forward along the doublings recovers \(R_\Lambda(x)=-2m\Re(x^{\rho-1}/(\rho-1))+O(x^{-1/2}\log^2x)\). Both the trial wave and the error have summable geometric tails. Abel summation gives \(\psi(x)-x=xR_\Lambda(x)-\int_1^x R_\Lambda(t)\,dt+O(1)\), restoring the single Chebyshev wave with its original multiplicity and \(O(\sqrt x\log^2x)\) error. This formulation uses only integer gcds in the observation. Neither the lower bound nor exclusion of the displayed wave follows from the floor estimate.

**The universal baseline on square horizons (paper).** For \(M\ge4\) set \(L=\operatorname{lcm}(1,\dots,M)\) and
\[
 P_M=\prod_{\substack{u\le M^2,\ u\ {\rm odd}\\\gcd(u,L)>1}}\frac{u}{\gcd(u,L)},\quad
 F(M)=\tfrac12 M^2\log M+\tfrac12(\gamma+\log2-3)M^2,\quad
 R_\Lambda(M)=\sum_{d\le M}\frac{\Lambda(d)}d-\log M+\gamma .
\]
Let \(C_{M^2}\) sum the logarithm of the prime divisor above \(M\) on odd composites through \(M^2\), counting zero when there is none. Ordinary factorization gives
\[
 \log P_M-F(M)=-\tfrac12M^2R_\Lambda(M)-\{\theta(M^2)-M^2\}+O(M),\qquad
 \log P_M-C_{M^2}=\tfrac12M^{3/2}+O(M^{13/9}).
\]
For the first identity, \(\log\gcd(u,L)=\sum_{d\mid u,\ d\le M}\Lambda(d)\). The only odd integers through \(M^2\) coprime to \(L\) are one and primes above \(M\). Each odd \(d\) has \(M^2/(2d)+O(1)\) odd multiples, with total rounding cost at most \(\psi(M)\). The dyadic reciprocal terms through \(M\) sum to \(\log2+O(1/M)\). The odd factorial logarithm is \(M^2(\log M^2-1)/2+O(\log(2M))\).

For the second identity the excess counts odd multiples of proper powers \(M<p^k\le M^2\) with weight \(\log p\). Rounding costs \(O(M)\). For squares the main contribution is \(M^2/2\) times \(\sum_{\sqrt M<p\le M}(\log p)/p^2=M^{-1/2}+O(M^{-5/9})\), by partial summation of \(\theta(t)=t+O(t^{8/9})\). The cumulative weight from \(k\ge3\) up to \(t\) is \(O(t^{1/3}\log(2t))\) by Chebyshev, giving \(O(M^{4/3}\log(2M))\) after partial summation. The square term describes the cost of using one power of the lcm in the positive composite count. [Odd composite definition and sharp comparison](acs-pvc-ordinary-primes-on-a-finite-dyadic-product-fibre.md)

For \(1/2<b<1\), an **upper** bound
\[
 \log(P_{2M}/P_M^4)-2M^2\log2\le A M^{1+b}
\]
for all large \(M\) implies \(\Theta\le b\). To prove this, subtract the first comparison at \(2M\) and four times that at \(M\). The result is \(-2M^2 E(M)-\theta(4M^2)+4\theta(M^2)+O(M)\), where \(E(x)=\sum_{x<d\le2x}\Lambda(d)/d-\log2\) denotes the centered octave mass. If \(\Theta>b\), use the project bound \(\Theta<1\) to choose \(\max(b,2\Theta-1)<t<\Theta\). The theta errors are \(O_\varepsilon(M^{2\Theta+\varepsilon})\), so the octave mass is bounded below by \(-K M^{t-1}\). Between integer lower endpoints the octave mass can only increase. For \(\Re z>1\), direct integration on \([d/2,d)\) gives
\[
 \int_1^\infty E(x)x^{-z}\,dx
 =\frac{2^{z-1}-1}{z-1}\frac{-\zeta'(z)}{\zeta(z)}-\frac{\log2}{z-1}.
\]
The real pole at one cancels. The multiplier is nonzero at every right zero since \(\lvert 2^{\rho-1}\rvert<1\). Landau's theorem applied on a late tail to \(E(x)+Kx^{t-1}\) forces convergence on \(\Re z>t\), contradicting a zero there. At \(b=5/6\) the known theta errors already cost \(O(M^{16/9})\), below \(M^{11/6}\). Thus a lower error of \(M^{-1/6}\) in one reciprocal Mangoldt octave suffices for the whole-prefix \(11/3\) estimate.

An all-square lower bound \(C_{M^2}\ge F(M)-A M^{1+b}\) also forces \(\Theta\le b\). The two comparisons bound \(R_\Lambda(M)\) above by \(O(M^{t-1})\) with the same choice of \(t\). Its Mellin transform is \([ -\zeta'/\zeta(z)-1/(z-1)+\gamma]/(z-1)\), regular at one with residue \(-m/(\rho-1)\) at each right zero. The same Landau argument applies to the upper bound. Under RH, partial summation gives \(R_\Lambda(M)=O(M^{-1/2}\log^2 M)\), so either the product-ratio upper bounds or the composite lower bounds at all exponents \(1+b>3/2\) characterize RH. A lone quartet gives the identifiable wave
\[
 C_{M^2}-F(M)=m\Re\!\left(\frac{M^{1+\rho}}{\rho-1}\right)
 +O_\rho(M^{3/2}\log^2 M+M^{2\Re\rho})
\]
by partial summation of its single wave in \(\psi\). Both errors have smaller order than its amplitude. The required arithmetic lower bound and exclusion of the lone quartet remain open. [Single-wave characterization for the ordinary primes](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/SingleQuartetSecularAndWallRigidity.lean#L1931)

**Divisor inversion inside the reciprocal octave (§2.3).** Put \(A(n)=\Lambda(n)-2\mathbf1_{2\mid n}\Lambda(n/2)-(\log2)\mathbf1_{n=1}\). Summing over divisors gives exactly
\[
 \sum_{d\mid n}A(d)=(-1)^{n-1}\log(n/2)\qquad(n\ge1).
\]
The first divisor sum is \(\log n\), and the even divisors contribute \(-2\log(n/2)\) when \(n\) is even. The singleton supplies \(-\log2\) in every fibre. Write \(F(t)=\sum_{j\le t}(-1)^{j-1}\log(j/2)/j\). Möbius inversion and summation through \(N\ge1\) give the sharp identity
\[
 \sum_{N/2<n\le N}\frac{\Lambda(n)}n-\log2
 =\sum_{d\le N}\frac{\mu(d)}d F(N/d).
\]
The inner endpoint is \(j=\lfloor N/d\rfloor\). The finite identity \(\sum_{d\le N}\mu(d)\lfloor N/d\rfloor=1\) allows the exact subtraction
\[
 E(N/2)=\frac{F(N)}N+
 \sum_{d\le N}\frac{\mu(d)}d
 \left(F(\lfloor N/d\rfloor)-F(N)\frac{d\lfloor N/d\rfloor}{N}\right).
\]
The divisor identity, both finite sums and the quotient-cell grouping below passed the Lean axiom audit. [Finite inversion and sharp cells](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/DivisorInversionOnTheReciprocalPrimeOctave.lean#L83)

For \(1\le j\le N\), \(|F(j)-F(N)|\ll\log(2j)/j\) by the alternating-series bound, since \(\log(k/2)/k\) decreases for \(k\ge6\). The floor changes the subtracted coefficient by at most \(d/N\), and \(F(N)\) is bounded. Thus all \(d\le D\) cost \(O((D/N)(1+\log(2N/D)))\) absolutely, by summing \(\log(2N/d)\) through \(D\). Taking \(D=\lfloor N^{5/6}/\log(2N)\rfloor\) pays this part at \(N^{-1/6}\).

The only remaining signed terms are the finite quotient cells \(1\le j\le\lfloor N/(D+1)\rfloor\), with \(I_j=(\max(D,\lfloor N/(j+1)\rfloor),\lfloor N/j\rfloor]\). Their exact sum is
\[
 \sum_j\left(F(j)\sum_{d\in I_j}\frac{\mu(d)}d
   -\frac{j F(N)}N\sum_{d\in I_j}\mu(d)\right).
\]
A lower bound by \(-A N^{-1/6}\) for this combined sum at every large even \(N\) suffices for the whole-prefix \(11/3\) estimate. The two terms use the same Möbius values at both sharp endpoints. This lower bound remains open.

On paper it suffices to bound the sum of the negative parts of these cell totals by \(O(T^{5/6})\) for even \(N\) in \((\sqrt T,T]\) along an unbounded sequence of \(T\). The small-divisor errors sum to \(O(T^{5/6})\), and the odd endpoint adds the nonnegative term \(\Lambda(2M+1)/(2M+1)\) to \(e_{2M}\). The required deficit bound remains open. [Positive mean and cofinal deficit criterion](acs-pvc-one-sided-mass-in-the-reciprocal-prime-octave.md)

At the sparse horizons \(M=m^r, X=m^{r+1}\), let the deficit be \((\log 2-\log Q_M(X)/X)^+\). A subpower bound for its sum on cofinal prefixes characterizes RH at \(r=2\) and implies the absolute \(N^{11/3}\) conductor bound at \(r=6\). Both transfers are formalized. [Sparse integer products](acs-pvc-sparse-square-and-sixth-power-prime-octaves.md)
