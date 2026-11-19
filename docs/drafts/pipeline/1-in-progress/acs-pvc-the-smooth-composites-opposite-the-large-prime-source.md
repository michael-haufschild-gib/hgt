# A complementary price on smooth composites

For \(k>1\) set \(h(k)=\sum_{d\mid k,\,d^2\le k}\mu(d)\). A prime has \(h(k)=1\). If \(k=pu\) with \(p\) prime and \(1<u<p\), every divisor through \(\sqrt k\) divides \(u<\sqrt k\), so \(h(k)=0\). A composite with nonzero weight therefore has no prime factor above its own square root. In particular its support is disjoint from the report's composites carrying a prime above \(2\sqrt n\) on \((2n,4n]\).

There is a second exact cancellation. If \(k>1\) is squarefree, the complementary divisors \(d,k/d\) are distinct, and \(\mu(d)\mu(k/d)=\mu(k)\). When \(\mu(k)=1\), paired divisors have the same sign. Their full sum is zero, hence \(h(k)=0\). Every squarefree composite that survives has an odd number of prime factors, at least three. If \(k=pqr\) with \(p<q<r\) prime, \(h(k)=-2\) for \(r<pq\) and zero for \(r>pq\). In the first case the divisors through \(\sqrt k\) are precisely \(1,p,q,r\).

**Exact center at the three original endpoints.** Write \(H_n(T)=\sum_{k\le T,\,(k,n)=1}h(k)\log k\), and let \(J_n(T)\) be the same sum on composites. For \(n>1\),
\[
 D(n)=\big[J_n(4n)-2J_n(3n)+J_n(2n)\big]
      -\big[H_n(4n)-2H_n(3n)+H_n(2n)\big].
\]
The deterministic term has a finite factorial formula. For \(e^2\le T,\ d\mid n\), put \(l=[e,d]\), \(u=\lfloor T/l\rfloor,\ v=\lfloor(e^2-1)/l\rfloor\). Then
\[
 H_n(T)=\sum_{1\le e\le\sqrt T}\mu(e)\sum_{d\mid n}\mu(d)
 \big[(u-v)\log l+\log(u!)-\log(v!)\big].
\]
Indeed \(e\mid k,\ d\mid k,\ e^2\le k\le T\) selects exactly \(k=lj\), \(v<j\le u\). Lean verifies this factorial formula, including the square at equality, and its unitary counterpart for any weight depending on the number of blocks of the smaller divisor. An estimate of the signed smooth-composite price relative to that center remains open. [Ordinary and unitary factorial centers](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheFactorialCenterOfTheSmallUnitaryDivisors.lean)

**Removing even parity without a squarefree restriction.** A unitary divisor \(d\parallel k\) contains whole prime-power factors, equivalently \(d\mid k\) and \((d,k/d)=1\). Define
\[
 u(k)=\sum_{d\parallel k,\, d^2\le k}(-1)^{\omega(d)}.
\]
Primes and pure prime powers have weight one. The prime-power blocks \(p^{v_p(k)}\) are pairwise coprime. Unitary divisors are their subset products. For \(k>1\) no subset equals its complementary product, since the products are coprime. If \(\omega(k)\) is even, the paired signs are equal and the full sum \((1-1)^{\omega(k)}\) vanishes. If one block exceeds \(\sqrt k\) and at least one other block exists, the selected divisors are exactly all subsets of the other blocks. Their sum also vanishes. Thus, apart from pure powers, **only odd numbers of at least three distinct primes survive, and every prime-power block is smaller than \(\sqrt k\)**. Balanced triples of blocks have weight exactly \(-2\).

Lean verifies the exact midpoint identity at every \(n\ge1\). After removing pure composite powers, the error is at most \((\log(4n)/\log 2)(\psi(4n)-\theta(4n))\). Each remaining composite has an odd number of at least three prime-power blocks and no prime above \(2\sqrt n\). Lean also verifies that the error fits every exponent above one half. For \(1/2\le b<1\), upper bounds for this centered price at every exponent \(b<t<1\) are equivalent to \(\Theta\le b\). [Exact identity and error bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheOddSmoothCompositesAtThePrimeMidpoint.lean)

The unitary center is explicit. For each \(e\le\sqrt T,\ (e,n)=1\), put \(k=em\) and expand \((m,en)=1\) using \(\mu(d)\) over \(d\mid en\). Now \(e^2\le k\le T\) and \(d\mid m\) select \(k=edj\) with \(\lfloor(e^2-1)/(ed)\rfloor<j\le\lfloor T/(ed)\rfloor\). The same factorial difference applies with \(l=ed\), multiplied by \((-1)^{\omega(e)}\mu(d)\). Lean bounds the error at an endpoint \(T\) by \(3+4\log T\) per progression and by \(\tau(en)(3+4\log T)\) for the primitive row. There are \(O_\varepsilon(n^{1/2+\varepsilon})\) divisor rows at these endpoints. The integral density of the \(e\)-row is \(\varphi(en)/(e^2n)\), including the cutoff \(x\ge e^2\).

Balanced triples cannot be removed by another normalized weight on the small unitary divisor while preserving the vanishing at all products of two coprime prime-power blocks. Indeed if \(w(1)=1\), vanishing on \(a q\) for a prime-power block \(a\) and any larger prime \(q\nmid a\) forces \(w(a)=-1\). For a product of three blocks, all below its square root, the small unitary divisors are the unit and the three individual blocks. Their weight is necessarily \(-2\).

**Ordinary factorizations at the quarter-power cut.** An alternative keeps a fixed \(Y=\lceil(4n)^{1/4}\rceil\) and \(\kappa_Y(k)=\sum_{e\mid k,e\le Y}\mu(e)\). Write \(k=s r\), with all prime factors of \(s\) at most \(Y\) and all factors of \(r\) above \(Y\). Then \(\kappa_Y(k)=\kappa_Y(s)\). Replace the composite log by \(\kappa_Y(s)\log r\) and use the all-integer center with the same divisor weight and full log. The signed error is \(O_\varepsilon(n^{1/2+\varepsilon})\). To see this, expand \(\log s\) over \(p^j\mid k,\ p\le Y\). Every combination of \(e\le Y,\ d\mid n,\ p^j\) is one lcm row with signed multiplicity at most one. For each prime \(p\le Y\) the total log price of its powers through \(4n\) is at most \(\log(4n)\). The total error is at most \(2^{\omega(n)}Y^2\log(4n)\). Primes in the moving intervals retain their full logarithm whenever \(Y\le2n\).

Here the only unweighted rough composites (\(s=1\)) have two or three prime factors counted with multiplicity. A surviving mixed composite has \(\operatorname{rad}(s)>Y\), since otherwise the complete Möbius sum vanishes. It carries one or two prime factors above \(Y\), counted with multiplicity. These statements follow from \(k\le4n\le Y^4\). Repeated primes enter through the ordinary multiplicity in \(\log r\).

### Six colors at the first strip milestone

Let \(m\ge2\) and \(\zeta=e^{2\pi i/m}\). Color the distinct prime-power blocks of \(k>1\) with colors \(0,\dots,m-1\). Let \(a_j\) be the product of blocks of color \(j\), with empty product one. Define \(U_m(k)\) as the sum of \(\zeta^{\sum_j j\omega(a_j)}\) over colorings for which \(a_0\) is largest. The largest product is unique because the products are pairwise coprime and at least one exceeds one. Conjugating all colors preserves the sum, so the weight is real. The two-color weight is \(u(k)\).

* Every pure prime power has weight one. Every mixed product with a block greater than its square root has weight zero. The dominant block must have color zero, and all remaining colors can be summed freely.
* If \(m\mid\omega(k)\), the weight is zero. Cyclically shifting all colors preserves their weight. The unrestricted color sum is zero and equals \(m U_m(k)\).
* Every product with \(2\le\omega(k)\le m\) has weight zero, including all multiplicities. Partition its blocks into nonempty color classes. The largest class product fixes color zero. For the remaining \(r\) classes of sizes \(t_1,\ldots,t_r\), the sum over distinct nonzero colors is \((-1)^r r!\). Indeed their total size is less than \(m\). In partition-lattice inclusion–exclusion, each group of colliding labels contributes \(\sum_{c=1}^{m-1}\zeta^{c\sum t_i}=-1\). The factor \((-1)^{s-1}(s-1)!\) for a collision group of size \(s\) then leaves the common sign \((-1)^r\); the sum of the remaining factorial products counts the \(r!\) permutations by cycles. Summing over all original partitions gives \(\sum_j {\omega(k)\brace j}(-1)^{j-1}(j-1)!=0\) for \(\omega(k)>1\), by the Stirling recurrence.

The first surviving class is sharp. If \(k\) has \(m+1\) blocks and the largest block is smaller than the product of the two smallest, then \(U_m(k)=(-1)^{m-1}m!\). For every partition with a nonsingleton winning class, the distinct-label calculation still applies. A singleton can win only when all classes are singletons. This partition has no admissible labeling and removes exactly \((-1)^m m!\) from the zero Stirling sum.

**Arithmetic center.** For fixed losing products \(a_1,\ldots,a_{m-1}\), set \(e=\prod a_i\), \(M=\max a_i\). The remaining factor satisfies \(k/e>M\) and \((k/e,en)=1\), with \((e,n)=1\). At \(k\le X=4n\), this requires \(e\le X^{1-1/m}\). Expanding coprimality over \(d\mid en\) gives ordinary factorial log sums on the progressions \(edj\), retaining the lower endpoint \(eM\) and both original interval signs. Replacing each progression by its log integral costs \(O(\log X)\). The total cost is
\[
 O\!\left(\log X\sum_{e\le X^{1-1/m}}(m-1)^{\omega(e)}2^{\omega(en)}\right)
 =O_{m,\varepsilon}(n^{1-1/m+\varepsilon}).
\]
Each fixed-base power of \(\omega(e)\) satisfies the subpower bound by separating the finitely many primes below a fixed threshold. The same integral calculation uses density \(\varphi(en)/(e^2 n)\) on \(x>eM\), one term per losing-product tuple.

Consequently at \(m=6\) the centered price on **balanced composites with at least seven distinct prime factors**, omitting every multiple of six in the number of factors, recovers \(D(n)\) to \(O_\varepsilon(n^{5/6+\varepsilon})\) at every midpoint. Here balanced means every prime-power block is smaller than the product of the others. These integers are disjoint from all composites carrying the original prime \(p>2\sqrt n\). Seven comparable blocks have weight \(-720\). At \(m=2\) the loss is half-plus and three comparable blocks have weight \(-2\).

### An integer weight constant on the first surviving class

Write \(w=\omega(k)\), \(c_j=(-1)^{j-1}\binom mj\), and
\[
 K_m(t)=\sum_{j=0}^m(-1)^j\binom mj(j-1)^t,\qquad
 V_m(k)=\sum_{j=1}^m c_j j^{w-1}
       +\sum_{d\parallel k,\ d^2<k}K_m(\omega(d)).
\]
Finite differences give \(K_m(t)=0\) for \(t<m\) and \(K_m(m)=(-1)^mm!\). Choose the largest prime-power block \(b\). Expanding \(j^{w-1}=(1+(j-1))^{w-1}\) over subsets of the other blocks gives
\[
 V_m(k)=\mathbf1_{w=1}
  +\sum_{d\parallel k,\ d^2<k}K_m(\omega(d))
  -\sum_{d\parallel k/b}K_m(\omega(d)).
\]
For dominant \(b\) the two divisor sets agree. For \(w\le m\) both sums vanish. When \(w=m+1\) and \(b^2<k\), every divisor formed from \(m\) blocks is larger than \(\sqrt k\). The last sum then consists of the sole nonzero term \(K_m(m)\). Hence **every balanced product with exactly seven distinct prime factors has weight \(-720\) at \(m=6\)**. This applies to arbitrary multiplicities and unequal block sizes.

The small-divisor part has a half-plus progression error as in the two-color center. The integer \(j^{w-1}\) counts colorings into \(j\) colors with the largest class product at color zero. Indeed every coloring has one largest product, and exactly one of its \(j\) cyclic shifts has that property. Enumerating the other products gives the same factorial progressions as above with \(e\le X^{1-1/j}\). Thus \(V_m\) has an integral center at cost \(O_{m,\varepsilon}(n^{1-1/m+\varepsilon})\). Its independent one-sided bound is open. Unlike the cyclic root-of-unity weight, this integer weight makes no assertion of vanishing when \(m\mid w\) for \(w>m\).

**Status.** Lean verifies the two-color cancellations and the integer-weight formulas for dominant blocks, at most \(m\) distinct primes, and every balanced product with exactly \(m+1\) distinct primes. In particular the seven-block weight at \(m=6\) is \(-720\). The cyclic-color construction and integral center estimates are proved on paper. The one-sided bound for the remaining signed composite price is open. [Small unitary divisors](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheParityOfTheSmallUnitaryDivisors.lean) · [Integer block weights](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheFirstSurvivingNumberOfPrimePowerBlocks.lean)
