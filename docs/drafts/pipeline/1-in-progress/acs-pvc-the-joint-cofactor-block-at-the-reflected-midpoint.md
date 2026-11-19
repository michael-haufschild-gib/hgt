# The joint cofactor block at the reflected prime midpoint

For every integer \(n>1\), put \(P=\lfloor2\sqrt n\rfloor\), \(I_-=(2n,3n]\), \(I_+=(3n,4n]\), and \(c=10\log2-6\log3\). The target is a one-sided upper bound for the log price of the unique prime \(p>P\) in the coprime composites, right minus left, less \(c\varphi(n)\). It must hold for every endpoint and every exponent above \(5/6\) for the first milestone, or above \(1/2\) for RH. [November 19 programme, §2.18](../../../reports/review-1911/obstacles-summary.md#218-best-prospect-for-a-full-proof) · [Midpoint gate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L319)

Lean verified \(D(n)=C(n)-A(n)\) and \(\lvert A(n)-c\varphi(n)\rvert\le\sum_{d\mid n}|\mu(d)|/(n/d)\), with both intervals open on the left and closed on the right. [Exact orientation and totient error](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheTotientTermInTheReflectedCompositePrice.lean#L118)

**A forbidden large prime cancels exactly on paper.** Suppose \(p>P\) divides \(n\), and put \(a=n/p\). Then \(4a<p\), since \(p^2>4n\). All candidate cofactors lie in \((2a,4a]\), so they are smaller than \(p\) and \((v,n)=1\) is exactly \((v,a)=1\). Translation \(v\mapsto v+a\) pairs the entire left cofactor interval with the right one, preserving coprimality and the log weight. Each interval has exactly \(\varphi(a)\) partners. Thus the restriction \(p\nmid n\) can be dropped from the recombined price while retaining \((v,n)=1\). Up to a partial cofactor cut \(K\) its signed count lies in \([-\varphi(a),0]\), attains its minimum at \(3a\) and returns to zero at \(4a\). This identifies the exact boundary correction when a block cuts the translation pair. There is at most one such prime.

**The continuous center at the integer cutoff.** For fixed cofactor \(v\), replacing log prime mass by length gives
\[
 L(v)=(4n/v-P)_+-2(3n/v-P)_++(2n/v-P)_+ .
\]
It vanishes outside \([2n/P,4n/P]\), peaks at \(P/3\) at \(3n/P\), and has integral \(cn\). The omitted unit has zero length when \(P\le2n\). The exact discrepancy from \(c\varphi(n)\) is \(\sum_{d\mid n}\mu(d)E(n/d,P)\), where
\[
 E(m,P)=\int_0^{P/3}\!\left(\left\{\frac{2m}{P-y}\right\}-\left\{\frac{4m}{P+y}\right\}\right)\,dy .
\]
Indeed the cofactors above height \(y\) lie between those two moving endpoints before taking fractional parts. Counting the lattice points by the difference of floors and integrating gives the formula. Including an endpoint at its own height leaves its integral unchanged. Hence \(|E(m,P)|\le P/3\). More precisely \(|E(m,P)|\ll\min(m,P^2/m)\). The discrete clipped sum has at most \(4m/P\) terms of height at most \(P/3\), and its integral is \(cm\). For the second bound write \(s(u)=\{u\}-1/2\). The two means cancel, and substitution gives \(2m\int_{2m/P}^{3m/P}s(u)u^{-2}du-4m\int_{3m/P}^{4m/P}s(u)u^{-2}du\). Integration by parts uses the bounded primitive \((\{u\}^2-\{u\})/2\). At the report's cutoff, prime centers therefore have \(O(1)\) discrete clipping error. This calculation is proved on paper.

**One boundary term for an arbitrary chain of partial cofactor blocks.** For an integer \(V\ge1\) define
\[
 T_V(p)=(4n/p-V)_+-2(3n/p-V)_++(2n/p-V)_+ .
\]
It is nonnegative, supported on \([2n/V,4n/V]\), and has integral \(cn\) in \(p\). Let \(H_{>V}\) be the actual cofactor price above \(V\), after dropping the forbidden-prime condition from the full sum as above. At a partial cut this convention allocates each forbidden row between the two neighbors with opposite signs. For any lower prime cutoff \(P\),
\[
 H_{>V}=\rho_n\sum_{P<p\le4n/V}(\log p)T_V(p)+e_V,
 \qquad |e_V|\ll (n/V)M(n).
\]
Indeed counting cofactors \(V<v\le kn/p\) incurs at most \(2M(n)\) error from \(\rho_n(kn/p-V)_+\), for each \(k=2,3,4\), including an empty interval. Sum only through \(4n/V\) and apply the elementary Chebyshev upper mass. On a block \(V<v\le W\) the profile is \(T_V-T_W\) and the error is exactly \(e_V-e_W\). Any number of consecutive blocks therefore retains only its first and last endpoint error. The same proof holds for any fixed selection of the primes. If \(P\le2n/V\), the positive profile carries the full continuous center at this boundary. The centered prime sum against that profile is still unpaid.

**All-endpoint cut at the first milestone.** Up to any \(P'\le2n\), the absolute magnitude of each fully recombined prime row is at most \(M(n)\log p\), since Möbius inversion gives a second difference of three equally spaced floors of magnitude at most one per divisor. The unit cofactor lies outside these rows. Thus moving the prime cutoff to \(\max(P,\lfloor n^{5/6}\rfloor)\) costs \(O_\varepsilon(n^{5/6+\varepsilon})\) at every \(n\). All remaining proper cofactors satisfy \(2\le v<4n^{1/6}\). At the half-power milestone the original cut gives \(v<2\sqrt n\). Bounding the joint signed sum after subtracting \(c\varphi(n)\) remains open at both milestones. Lean verified the three-floor inversion, its uniform bound for small factors, the proper-power bound, and the removal of the unit cofactor at each prime. [Factor count and small-factor bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheSmallPrimeFactorsOfTheReflectedComposites.lean)

**Removing cofactor coprimality.** Let \(H^*(n,P)\) count every cofactor \(v\ge2\) and ordinary prime \(p>P\), with the same two sharp product intervals. Write \(F(n)=\log((4n)!(2n)!/(3n)!^2)\) and \(k_n(q)=\lfloor4n/q\rfloor-2\lfloor3n/q\rfloor+\lfloor2n/q\rfloor\). Unique factorization gives \(F(n)=\sum_{q\le4n}\Lambda(q)k_n(q)\). Removing the unit cofactor adds \(D(n)\) because each endpoint prime has the opposite orientation. Every \(|k_n(q)|\le1\). Consequently for \(1\le P\le2n\),
\[
 |H^*(n,P)-F(n)-D(n)|\le\psi(P)+\psi(4n)-\theta(4n).
\]
Lean verified this factorial error bound. It also verified the same center to \(O(\sqrt n)\) after every further prime cut through \(n^{500/999}\). [Unrestricted factorial identity and sharp cutoff theorem](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeFloorRowBeyondTheSquareRoot.lean#L278)

The center satisfies \(F(n)=cn+\tfrac12\log(8/9)+O(1/n)\). Comparing with the primitive identity gives \(H^*(n,P)-H(n,P)=c(n-\varphi(n))+O((P+\sqrt n)M(n))\). At the report's cutoff the unrestricted row alone recovers the midpoint with \(O(\sqrt n)\) error at every endpoint. Its price is precisely
\[
 H^*(n,P)=\sum_{P<p\le2n}(\log p)\,k_n(p).
\]
For \(x=\{n/p\}\), the weight is \(+1,-1,+1,-1\) on \([1/4,1/3),[1/3,1/2),[1/2,2/3),[2/3,3/4)\), respectively, and zero elsewhere. Both opposite intervals must stay in this one weight.

The continuous log-prime replacement for the last display gives \(cn+O(P^2/n)\), hence \(cn+O(1)\) at \(P=\lfloor2\sqrt n\rfloor\). Indeed the period-one function \(k(t)=\lfloor4t\rfloor-2\lfloor3t\rfloor+\lfloor2t\rfloor\) has mean zero and bounded primitive. Substituting \(t=n/x\) shows \(\int_0^P k(n/x)\,dx=O(P^2/n)\) by integration by parts. On \((2n,4n]\) the integral is zero. Integrating the three floors from \(\delta>0\) to \(4n\) gives the three harmonic sums \(kn H_{\lfloor kn/\delta\rfloor}-\delta\lfloor kn/\delta\rfloor\) for \(k=4,3,2\). Their signed combination tends to \(cn\). The remaining research target is cancellation against the actual ordinary-prime measure in those four bands.

**Which cofactors remain?** The ordinary-prime reciprocal Vaughan bound gives, on paper, \(O_\varepsilon(n^{5/6+\varepsilon})\) for every partial prime shell between \(n^{5/6}\) and \(n^{8/9}\). The corresponding half-plus estimate pays through \(n^{18/35}\). The joint upper bounds still needed therefore involve \(2\le v<4n^{1/9}\) and \(2\le v<4n^{17/35}\), respectively, with the unrestricted linear center. [Signed shell estimates and proof](acs-pvc-reciprocal-prime-cancellation-in-the-midpoint-floor-row.md)

**Which zero signal reaches the small cofactors?** For a test density \(x^{s-1}dx\), \(0<\sigma=\Re s<1\), put \(m(s)=4^s-2\cdot3^s+2^s\). The unrestricted row above any \(0<Q\le2n\) has moment
\[
 \int_Q^{2n} k(n/x)x^{s-1}\,dx
 = n^s\frac{m(s)}s(\zeta(s)-1)+O_s(Q^{\sigma+1}/n).
\]
Indeed \(k(t)=2\{3t\}-\{4t\}-\{2t\}\). Scaling the fractional-part Mellin integral gives \(m(s)\zeta(s)/s\) for the full kernel. Removing unit cofactors on \((2n,4n]\) subtracts \(n^sm(s)/s\). After \(t=n/x\), the omitted lower prime range is \(n^s\int_{n/Q}^\infty k(t)t^{-s-1}\,dt\). Integration by parts with the bounded periodic primitive of \(k\) gives the stated error. Thus at an actual strip zero \(\rho\), every sublinear prime cut \(Q=o(n)\) leaves the same nonzero normalized coefficient \(-m(\rho)/\rho\) in the remaining cofactors. This locates the obstruction to a pairing based only on lengths or truncation. An estimate for the ordinary-prime weights is still needed. This localized moment is proved on paper. [Fractional-part transform](../../../../formal/GaloisForLFunctions/SignedArithmeticEnergyIncidence/TheColumnsOfTheChainInMellinCoordinates.lean#L664) · [Midpoint nonvanishing](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L363)
