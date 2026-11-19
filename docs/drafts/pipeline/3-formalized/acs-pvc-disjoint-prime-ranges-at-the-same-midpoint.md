# Disjoint ordinary prime ranges at the same midpoint

Let \(X=4n\) and \(1/2\le b<1\). For each \(1-b\le a\le b\), put \(Q=\min(2n,\lfloor X^a\rfloor)\), \(V=\lfloor X^{b-a}\rfloor\). Weight each primitive cofactor \(v>V\) by \(\sum_{e\mid v,e\le V}\mu(e)\). Count the ordinary primes \(p>Q\), \(p\nmid n\), in the two original product intervals with this cofactor, right minus left. Subtract the signed factorial center of the completed divisible rows. The resulting price satisfies
\[
 |B_{b,a}(n)-D(n)|\le C_{b,\varepsilon}n^{b+\varepsilon}
 \quad(n\ge1),
 \qquad X^a<p<X^{a+1-b}.
\]
The constant is independent of the choice of \(a\). At \(b=5/6\) the five choices \(a=j/6\), \(1\le j\le5\), use disjoint ordinary primes. An upper bound on one of those five prices at each integer, for every exponent strictly between \(5/6\) and 1, suffices for the full \(11/3\) conductor prefix estimate. Conversely that prefix estimate yields the upper bounds on all five prices.

**Proof.** The unit cofactor contributes \(-D(n)\); all other cofactors through \(V\) have zero Möbius weight. Completing the \(e\)-divisible rows costs \(O(2^{\omega(n)}[VQ+V\log n+\sqrt{nV}])\). For the last term, the prime-power error at row \(e\) is \(O(\sqrt{n/e})\). The chosen cuts make each cost \(O_{b,\varepsilon}(n^{b+\varepsilon})\). A retained cofactor exceeds \(X^{b-a}\) and \(pv\le X\), giving the upper prime endpoint. The uniform error permits the choice of range to depend on \(n\). The required one-sided cancellation remains open.

Lean verified `two_cut_prime_price_error`, `cofactor_prime_band_support`, `ordinary_prime_bands_measure_midpoint`, and `one_prime_range_at_each_midpoint`; their axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. [Uniform estimate and criterion](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/DisjointOrdinaryPrimeRangesAtTheSameMidpoint.lean#L92) · [Factorial center](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimitivePrimePriceBeyondAMovingCofactorCut.lean#L76) · [Conductor prefix equivalence](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L337)
