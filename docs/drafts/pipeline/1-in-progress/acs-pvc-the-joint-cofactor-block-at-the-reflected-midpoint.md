# The joint cofactor block at the reflected prime midpoint

For every integer \(n>1\), put \(P=\lfloor2\sqrt n\rfloor\), \(I_-=(2n,3n]\), \(I_+=(3n,4n]\), and \(c=10\log2-6\log3\). The target is a one-sided upper bound for the log price of the unique prime \(p>P\) in the coprime composites, right minus left, less \(c\varphi(n)\). It must hold for every endpoint and every exponent above \(5/6\) for the first milestone, or above \(1/2\) for RH. [November 19 programme, §2.18](../../../reports/review-1911/obstacles-summary.md#218-best-prospect-for-a-full-proof) · [Midpoint gate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L319)

Lean verified \(D(n)=C(n)-A(n)\) and \(\lvert A(n)-c\varphi(n)\rvert\le\sum_{d\mid n}|\mu(d)|/(n/d)\), with both intervals open on the left and closed on the right. [Exact orientation and totient error](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheTotientTermInTheReflectedCompositePrice.lean#L121)

**Exact cancellation for a large prime divisor of the center.** Suppose \(p>P\) divides \(n\), and put \(a=n/p\). Then \(4a<p\), since \(p^2>4n\). All candidate cofactors lie in \((2a,4a]\), so they are smaller than \(p\) and \((v,n)=1\) is exactly \((v,a)=1\). Translation \(v\mapsto v+a\) pairs the entire left cofactor interval with the right one, preserving coprimality and the log weight. Each interval has exactly \(\varphi(a)\) partners. Thus the restriction \(p\nmid n\) can be dropped from the recombined price while retaining \((v,n)=1\). Up to a partial cofactor cut \(K\) its signed count lies in \([-\varphi(a),0]\), attains its minimum at \(3a\) and returns to zero at \(4a\). This identifies the exact boundary correction when a block cuts the translation pair. There is at most one such prime. Lean verified the signed count at every cut and both terminal values. [Sharp cofactor counts](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheForbiddenLargePrimeInTheReflectedCofactorIntervals.lean#L103)

**The continuous center at the integer cutoff.** For fixed cofactor \(v\), replacing log prime mass by length gives
\[
 L(v)=(4n/v-P)_+-2(3n/v-P)_++(2n/v-P)_+ .
\]
It vanishes outside \([2n/P,4n/P]\), peaks at \(P/3\) at \(3n/P\), and has integral \(cn\). The omitted unit has zero length when \(P\le2n\). The exact discrepancy from \(c\varphi(n)\) is \(\sum_{d\mid n}\mu(d)E(n/d,P)\), where
\[
 E(m,P)=\int_0^{P/3}\!\left(\left\{\frac{2m}{P-y}\right\}-\left\{\frac{4m}{P+y}\right\}\right)\,dy .
\]
Indeed the cofactors above height \(y\) lie between those two moving endpoints before taking fractional parts. Counting the lattice points by the difference of floors and integrating gives the formula. Including an endpoint at its own height leaves its integral unchanged. Hence \(|E(m,P)|\le P/3\). More precisely \(|E(m,P)|\ll\min(m,P^2/m)\). The discrete clipped sum has at most \(4m/P\) terms of height at most \(P/3\), and its integral is \(cm\). For the second bound write \(s(u)=\{u\}-1/2\). The two means cancel, and substitution gives \(2m\int_{2m/P}^{3m/P}s(u)u^{-2}du-4m\int_{3m/P}^{4m/P}s(u)u^{-2}du\). Integration by parts uses the bounded primitive \((\{u\}^2-\{u\})/2\). At the report's cutoff, prime centers therefore have \(O(1)\) discrete clipping error. The divisor bound and its prime-center specialization are proved on paper. [Lean formalization in progress](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheClippedCofactorDensityAtThePrimeMidpoint.lean#L177)

**Moving cofactor cutoff.** Lean verified that at the original prime cut the signed factorial remainder can discard all proper cofactors through \(\lfloor n^{1/3}\rfloor\) at the first milestone, at every integer. The verified uniform range theorem gives five disjoint ordinary prime ranges at the same exponent. [Disjoint-range theorem](../3-formalized/acs-pvc-disjoint-prime-ranges-at-the-same-midpoint.md) [Factorial projection and range estimates](acs-pvc-factorial-completion-of-divisible-cofactor-rows.md)

**A signed partner at the cube root.** At \(Y=\lfloor(3n)^{1/3}\rfloor\), triples entirely below the cut lie on the left and triples entirely above it lie on the right. Both carry \(\log(pqr)/3\) per ordered tuple, apart from pure cubes on the left. The other surviving products are \(Y\)-smooth with at least four prime factors. The explicit center uses only Möbius coefficients and the ordinary divisor estimate. The sharp first gate still requires an upper bound on their combined signed price. [Triple identity at the original endpoints, on paper](acs-pvc-opposite-prime-triples-at-the-cube-root-of-the-midpoint.md)

**Disjoint composite support.** A second paper reduction puts the first milestone on actual composites with at least seven distinct prime factors, every prime-power block smaller than the product of the others. These composites carry none of the original primes above \(2\sqrt n\). The integer weight is exactly \(-720\) on every balanced seven-block product. Bounding the recombined signed price relative to its factorial center remains open. [Weights, centers, and sharp first surviving class](acs-pvc-the-smooth-composites-opposite-the-large-prime-source.md#an-integer-weight-constant-on-the-first-surviving-class) A smooth weight inside the same intervals gives an equivalent half-power criterion after removing any fixed number of prime-power blocks. [Smooth midpoint and arithmetic center, on paper](acs-pvc-a-smooth-midpoint-on-products-with-many-prime-factors.md)

**One boundary term for an arbitrary chain of partial cofactor blocks.** For an integer \(V\ge1\) define
\[
 T_V(p)=(4n/p-V)_+-2(3n/p-V)_++(2n/p-V)_+ .
\]
It is nonnegative, supported on \([2n/V,4n/V]\), and has integral \(cn\) in \(p\). Let \(H_{>V}\) be the actual cofactor price above \(V\), after dropping the forbidden-prime condition from the full sum as above. At a partial cut this convention allocates each forbidden row between the two neighbors with opposite signs. For any lower prime cutoff \(P\),
\[
 H_{>V}=\rho_n\sum_{P<p\le4n/V}(\log p)T_V(p)+e_V,
 \qquad |e_V|\ll (n/V)M(n).
\]
Indeed counting cofactors \(V<v\le kn/p\) incurs at most \(2M(n)\) error from \(\rho_n(kn/p-V)_+\), for each \(k=2,3,4\), including an empty interval. Sum only through \(4n/V\) and apply the elementary Chebyshev upper mass. On a block \(V<v\le W\) the profile is \(T_V-T_W\) and the error is exactly \(e_V-e_W\). Any number of consecutive blocks therefore retains only its first and last endpoint error. The same proof holds for any fixed selection of the primes. If \(P\le2n/V\), the positive profile carries the full continuous center at this boundary. For the unrestricted row, shifting the cutoff to \(V+1/2\) isolates three sharp sawtooth sums. The centered prime sum against the resulting profile is still unpaid. [Half-integer correction](acs-pvc-reciprocal-prime-cancellation-in-the-midpoint-floor-row.md)

**Verified reduction at both milestones.** For \(1/2\le b\le1\) use \(P_b=\lfloor 2n^b\rfloor\). Lean proves, for every \(n>1\), that the primitive large-prime price \(H(n,P_b)\) satisfies
\[
 |H(n,P_b)-c\varphi(n)-D(n)|\ll_{b,\varepsilon} n^{b+\varepsilon},
 \qquad 2\le v<2n^{1-b}.
\]
Möbius inversion makes each signed three-floor count at most \(M(n)\). The small factors cost \(7P_b M(n)\), and the proper powers cost \((\psi(4n)-\theta(4n))M(n)\). At \(b=5/6\) only cofactors below \(2n^{1/6}\) are required by this primitive reduction. [Exact split and all-center estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheTotientTermInTheReflectedCompositePrice.lean#L415)

**Removing cofactor coprimality.** Let \(H^*(n,P)\) count every cofactor \(v\ge2\) and ordinary prime \(p>P\), with the same two sharp product intervals. Write \(F(n)=\log((4n)!(2n)!/(3n)!^2)\) and \(k_n(q)=\lfloor4n/q\rfloor-2\lfloor3n/q\rfloor+\lfloor2n/q\rfloor\). Unique factorization gives \(F(n)=\sum_{q\le4n}\Lambda(q)k_n(q)\). Removing the unit cofactor adds \(D(n)\) because each endpoint prime has the opposite orientation. Every \(|k_n(q)|\le1\). Consequently for \(1\le P\le2n\),
\[
 |H^*(n,P)-F(n)-D(n)|\le\psi(P)+\psi(4n)-\theta(4n).
\]
Lean verified this factorial error bound. It also verified the same center to \(O(\sqrt n)\) after every further prime cut through \(n^{500/999}\). [Unrestricted factorial identity and sharp cutoff theorem](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeFloorRowBeyondTheSquareRoot.lean#L302)

Lean also verifies the explicit Stirling endpoint correction. [Factorial center](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheTotientTermInTheReflectedCompositePrice.lean#L454) The center satisfies \(F(n)=cn+\tfrac12\log(8/9)+O(1/n)\). Comparing with the primitive identity gives \(H^*(n,P)-H(n,P)=c(n-\varphi(n))+O((P+\sqrt n)M(n))\). At the report's cutoff the unrestricted row alone recovers the midpoint with \(O(\sqrt n)\) error at every endpoint. Its price is precisely
\[
 H^*(n,P)=\sum_{P<p\le2n}(\log p)\,k_n(p).
\]
For \(x=\{n/p\}\), the weight is \(+1,-1,+1,-1\) on \([1/4,1/3),[1/3,1/2),[1/2,2/3),[2/3,3/4)\), respectively, and zero elsewhere. Both opposite intervals must stay in this one weight.

The continuous log-prime replacement for the last display gives \(cn+O(P^2/n)\), hence \(cn+O(1)\) at \(P=\lfloor2\sqrt n\rfloor\). Indeed the period-one function \(k(t)=\lfloor4t\rfloor-2\lfloor3t\rfloor+\lfloor2t\rfloor\) has mean zero and bounded primitive. Substituting \(t=n/x\) shows \(\int_0^P k(n/x)\,dx=O(P^2/n)\) by integration by parts. On \((2n,4n]\) the integral is zero. Integrating the three floors from \(\delta>0\) to \(4n\) gives the three harmonic sums \(kn H_{\lfloor kn/\delta\rfloor}-\delta\lfloor kn/\delta\rfloor\) for \(k=4,3,2\). Their signed combination tends to \(cn\). The remaining research target is cancellation against the actual ordinary-prime measure in those four bands.

**Which cofactors remain?** The ordinary-prime reciprocal Vaughan bound gives, on paper, \(O_\varepsilon(n^{5/6+\varepsilon})\) for every partial prime shell between \(n^{5/6}\) and \(n^{8/9}\). The corresponding half-plus estimate pays through \(n^{18/35}\). The joint upper bounds still needed therefore involve \(2\le v<4n^{1/9}\) and \(2\le v<4n^{17/35}\), respectively, with the unrestricted linear center. [Signed shell estimates and proof](acs-pvc-reciprocal-prime-cancellation-in-the-midpoint-floor-row.md)

Lean verified that the primitive sum admits a reduction removing **every fixed cofactor**. It suffices to sample centers divisible by all primes through \(y=\lfloor\log n/(4\log4)\rfloor\). Every integer lies within \(n^{1/4}\) above such a center, at one-sided midpoint cost \(O(\sqrt n)\). The remaining primitive cofactors have least prime factor above \(y\) and satisfy \(v<2n^{1/6}\) at the first milestone. [Proof and exact sampling criterion](../3-formalized/acs-pvc-rough-cofactors-on-primorial-midpoints.md)

**Pair the integers before subtracting the center.** For \(n>1\) use the same \(1\le j<n\), \((j,n)=1\), on both sides, with \(x=3n+j\), \(y=3n-j\). The original unpaired endpoints \(3n,4n\) both fail coprimality. For \(Q\ge P\), put \(r_Q(x)=x/p\) if \(x\) is composite with a prime \(p>Q\), and \(r_Q(x)=x\) otherwise. Uniqueness and subtraction of the exact integer center give
\[
 H(n,Q)-A(n)=\sum_{\substack{1\le j<n\\(j,n)=1}}\log\frac{r_Q(y)}{r_Q(x)}.
\]
When \(x=ap\) and \(y=bq\) both have a selected factor, the centered price is exactly \(\log(b/a)\). For \(p,q>6\), \(\gcd(a,b)=\gcd(x,6)\). Indeed every common divisor of \(x,y\) divides \(6n\) and is coprime to \(n\), and each divisor of \(\gcd(x,6)\) divides both cofactors. If only \(x\) supplies a large factor the price is \(\log(y/a)>0\). If only \(y\) does, it is \(\log(b/x)<0\). If neither does, it is \(\log(y/x)<0\). The open estimate asks whether the negative single-factor terms and the unselected pairs pay the positive single-factor terms and the signed cofactor ratios after summation. The identity is proved on paper. [Exact residual-factor formulation](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheRemainingFactorsOfOppositePrimitiveIntegers.lean#L152) · [Paired ordinary factors](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/OppositeCofactorPricesAcrossTheFirstRemainingPrimeOctave.lean#L277)

**Which zero signal reaches the small cofactors?** For a test density \(x^{s-1}dx\), \(0<\sigma=\Re s<1\), put \(m(s)=4^s-2\cdot3^s+2^s\). The unrestricted row above any \(0<Q\le2n\) has moment
\[
 \int_Q^{2n} k(n/x)x^{s-1}\,dx
 = n^s\frac{m(s)}s(\zeta(s)-1)+O_s(Q^{\sigma+1}/n).
\]
Indeed \(k(t)=2\{3t\}-\{4t\}-\{2t\}\). Scaling the fractional-part Mellin integral gives \(m(s)\zeta(s)/s\) for the full kernel. Removing unit cofactors on \((2n,4n]\) subtracts \(n^sm(s)/s\). After \(t=n/x\), the omitted lower prime range is \(n^s\int_{n/Q}^\infty k(t)t^{-s-1}\,dt\). Integration by parts with the bounded periodic primitive of \(k\) gives the stated error. Thus at an actual strip zero \(\rho\), every sublinear prime cut \(Q=o(n)\) leaves the same nonzero normalized coefficient \(-m(\rho)/\rho\) in the remaining cofactors. This locates the obstruction to a pairing based only on lengths or truncation. An estimate for the ordinary-prime weights is still needed. This localized moment is proved on paper. [Fractional-part transform](../../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/TheColumnsOfTheChainInMellinCoordinates.lean#L664) · [Midpoint nonvanishing](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L363)
