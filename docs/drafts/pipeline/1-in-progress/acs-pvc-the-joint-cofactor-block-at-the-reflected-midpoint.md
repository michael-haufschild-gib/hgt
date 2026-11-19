# The joint cofactor block at the reflected prime midpoint

For every integer \(n>1\), put \(P=\lfloor2\sqrt n\rfloor\), \(I_-=(2n,3n]\), \(I_+=(3n,4n]\), and \(c=10\log2-6\log3\). The target is a one-sided upper bound for the log price of the unique prime \(p>P\) in the coprime composites, right minus left, less \(c\varphi(n)\). It must hold for every endpoint and every exponent above \(5/6\) for the first milestone, or above \(1/2\) for RH. [November 19 programme, §2.18](../../../reports/review-1911/obstacles-summary.md#218-best-prospect-for-a-full-proof) · [Midpoint gate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L319)

**A forbidden large prime cancels exactly on paper.** Suppose \(p>P\) divides \(n\), and put \(a=n/p\). Then \(4a<p\), since \(p^2>4n\). All candidate cofactors lie in \((2a,4a]\), so they are smaller than \(p\) and \((v,n)=1\) is exactly \((v,a)=1\). Translation \(v\mapsto v+a\) pairs the entire left cofactor interval with the right one, preserving coprimality and the log weight. Each interval has exactly \(\varphi(a)\) partners. Thus the restriction \(p\nmid n\) can be dropped from the recombined price while retaining \((v,n)=1\). Up to a partial cofactor cut \(K\) its signed count lies in \([-\varphi(a),0]\), attains its minimum at \(3a\) and returns to zero at \(4a\). This identifies the exact boundary correction when a block cuts the translation pair. There is at most one such prime.

**The continuous center at the integer cutoff.** For fixed cofactor \(v\), replacing log prime mass by length gives
\[
 L(v)=(4n/v-P)_+-2(3n/v-P)_++(2n/v-P)_+ .
\]
It vanishes outside \([2n/P,4n/P]\), increases to \(P/3\) at \(3n/P\), then decreases to zero. Its integral is \(cn\). Möbius inversion of the primitive count on each real prefix has discrepancy at most \(M(n)=\sum_{d\mid n}|\mu(d)|\) from density \(\rho_n=\varphi(n)/n\). Partial summation against this triangle yields \(|\sum_{v\ge2,(v,n)=1}L(v)-c\varphi(n)|\le (2P/3)M(n)\). The integer endpoint at the corner is included, and \(P\le2n\) makes the omitted unit cofactor have zero length.

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

**Removing the cofactor coprimality with its signed center (paper).** Let \(H^*(n,P)\) count every cofactor \(v\ge2\) and ordinary prime \(p>P\), with the same two sharp product intervals. Write \(F(n)=\log((4n)!(2n)!/(3n)!^2)\) and \(k_n(q)=\lfloor4n/q\rfloor-2\lfloor3n/q\rfloor+\lfloor2n/q\rfloor\). Unique factorization gives \(F(n)=\sum_{q\le4n}\Lambda(q)k_n(q)\). Removing the unit cofactor adds \(D(n)\) because each endpoint prime has the opposite orientation. Every \(|k_n(q)|\le1\). Consequently for \(1\le P\le2n\),
\[
 |H^*(n,P)-F(n)-D(n)|\le\psi(P)+\psi(4n)-\theta(4n).
\]
The center satisfies \(F(n)=cn+\tfrac12\log(8/9)+O(1/n)\). Comparing with the primitive identity gives \(H^*(n,P)-H(n,P)=c(n-\varphi(n))+O((P+\sqrt n)M(n))\). At the report's cutoff the unrestricted row alone recovers the midpoint with \(O(\sqrt n)\) error at every endpoint. Its price is precisely
\[
 H^*(n,P)=\sum_{P<p\le2n}(\log p)\,k_n(p).
\]
For \(x=\{n/p\}\), the weight is \(+1,-1,+1,-1\) on \([1/4,1/3),[1/3,1/2),[1/2,2/3),[2/3,3/4)\), respectively, and zero elsewhere. Both opposite intervals must stay in this one weight.

The continuous log-prime replacement for the last display gives \(cn+O(P^2/n)\), hence \(cn+O(1)\) at \(P=\lfloor2\sqrt n\rfloor\). Indeed the period-one function \(k(t)=\lfloor4t\rfloor-2\lfloor3t\rfloor+\lfloor2t\rfloor\) has mean zero and bounded primitive. Substituting \(t=n/x\) shows \(\int_0^P k(n/x)\,dx=O(P^2/n)\) by integration by parts. On \((2n,4n]\) the integral is zero. Integrating the three floors from \(\delta>0\) to \(4n\) gives the three harmonic sums \(kn H_{\lfloor kn/\delta\rfloor}-\delta\lfloor kn/\delta\rfloor\) for \(k=4,3,2\). Their signed combination tends to \(cn\). The remaining research target is cancellation against the actual ordinary-prime measure in those four bands.

**Which cofactors remain?** The ordinary-prime reciprocal Vaughan bound gives, on paper, \(O_\varepsilon(n^{5/6+\varepsilon})\) for every partial prime shell between \(n^{5/6}\) and \(n^{8/9}\). The corresponding half-plus estimate pays through \(n^{18/35}\). The joint upper bounds still needed therefore involve \(2\le v<4n^{1/9}\) and \(2\le v<4n^{17/35}\), respectively, with the unrestricted linear center. [Signed shell estimates and proof](acs-pvc-reciprocal-prime-cancellation-in-the-midpoint-floor-row.md)
