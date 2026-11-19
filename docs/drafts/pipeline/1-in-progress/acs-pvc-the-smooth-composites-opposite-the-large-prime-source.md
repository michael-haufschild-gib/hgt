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
Indeed \(e\mid k,\ d\mid k,\ e^2\le k\le T\) selects exactly \(k=lj\), \(v<j\le u\). This formula retains the lower endpoint \(e^2\), including a square at equality. The new center is explicit. An estimate of the signed smooth-composite price relative to that center remains open.

**Removing even parity without a squarefree restriction.** A unitary divisor \(d\parallel k\) contains whole prime-power factors, equivalently \(d\mid k\) and \((d,k/d)=1\). Define
\[
 u(k)=\sum_{d\parallel k,\, d^2\le k}(-1)^{\omega(d)}.
\]
Primes and pure prime powers have weight one. The prime-power blocks \(p^{v_p(k)}\) are pairwise coprime. Unitary divisors are their subset products. For \(k>1\) no subset equals its complementary product, since the products are coprime. If \(\omega(k)\) is even, the paired signs are equal and the full sum \((1-1)^{\omega(k)}\) vanishes. If one block exceeds \(\sqrt k\) and at least one other block exists, the selected divisors are exactly all subsets of the other blocks. Their sum also vanishes. Thus, apart from pure powers, **only odd numbers of at least three distinct primes survive, and every prime-power block is smaller than \(\sqrt k\)**. Balanced triples of blocks have weight exactly \(-2\).

The prime midpoint is exactly the composite price minus the all-integer center with weight \(u(k)\log k\). Pure composite powers cost \(O(\sqrt n\log(4n))\): on \(p^j\le4n\) one has \(j\le\log(4n)/\log 2\), and \(\sum_{p^j\le4n,j\ge2}\log p=\psi(4n)-\theta(4n)\ll\sqrt n\). This gives a half-plus criterion on a set of actual composite integers disjoint from the report's ordinary large-prime support.

The unitary center is explicit. For each \(e\le\sqrt T,\ (e,n)=1\), put \(k=em\) and expand \((m,en)=1\) using \(\mu(d)\) over \(d\mid en\). Now \(e^2\le k\le T\) and \(d\mid m\) select \(k=edj\) with \(\lfloor(e^2-1)/(ed)\rfloor<j\le\lfloor T/(ed)\rfloor\). The same factorial difference applies with \(l=ed\), multiplied by \((-1)^{\omega(e)}\mu(d)\). Replacing each progression by its integral costs \(O(\log(4n))\) on the two sharp signed intervals, since the counting discrepancy is bounded and \(\log\) is monotone. There are \(O_\varepsilon(n^{1/2+\varepsilon})\) divisor rows at these endpoints. The integral density of the \(e\)-row is \(\varphi(en)/(e^2n)\), including the cutoff \(x\ge e^2\).

Balanced triples cannot be removed by another normalized weight on the small unitary divisor while preserving the vanishing at all products of two coprime prime-power blocks. Indeed if \(w(1)=1\), vanishing on \(a q\) for a prime-power block \(a\) and any larger prime \(q\nmid a\) forces \(w(a)=-1\). For a product of three blocks, all below its square root, the small unitary divisors are the unit and the three individual blocks. Their weight is necessarily \(-2\).

**Ordinary factorizations at the quarter-power cut.** An alternative keeps a fixed \(Y=\lceil(4n)^{1/4}\rceil\) and \(\kappa_Y(k)=\sum_{e\mid k,e\le Y}\mu(e)\). Write \(k=s r\), with all prime factors of \(s\) at most \(Y\) and all factors of \(r\) above \(Y\). Then \(\kappa_Y(k)=\kappa_Y(s)\). Replace the composite log by \(\kappa_Y(s)\log r\) and use the all-integer center with the same divisor weight and full log. The signed error is \(O_\varepsilon(n^{1/2+\varepsilon})\). To see this, expand \(\log s\) over \(p^j\mid k,\ p\le Y\). Every combination of \(e\le Y,\ d\mid n,\ p^j\) is one lcm row with signed multiplicity at most one. For each prime \(p\le Y\) the total log price of its powers through \(4n\) is at most \(\log(4n)\). The total error is at most \(2^{\omega(n)}Y^2\log(4n)\). Primes in the moving intervals retain their full logarithm whenever \(Y\le2n\).

Here the only unweighted rough composites (\(s=1\)) have two or three prime factors counted with multiplicity. A surviving mixed composite has \(\operatorname{rad}(s)>Y\), since otherwise the complete Möbius sum vanishes. It carries one or two prime factors above \(Y\), counted with multiplicity. These statements follow from \(k\le4n\le Y^4\). Repeated primes enter through the ordinary multiplicity in \(\log r\).

**Status.** Paper identities. The one-sided bound at all integers for either centered price remains open. [Report route](../../../reports/review-1911/obstacles-summary.md#218-best-prospect-for-a-full-proof) · [Divisible cofactor rows](acs-pvc-factorial-completion-of-divisible-cofactor-rows.md)
