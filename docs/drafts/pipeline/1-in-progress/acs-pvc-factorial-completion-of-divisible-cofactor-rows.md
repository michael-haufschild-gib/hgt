# Factorial completion of the divisible cofactor rows

At the report's sharp cut \(Q=\lfloor2\sqrt n\rfloor\), every cofactor through \(V\) can be removed at cost \(O_\varepsilon(V\sqrt n\,n^\varepsilon)\), at the original integer \(n\). Set \(V=\lceil\sqrt{4n/Q}\rceil\). The cost is \(O_\varepsilon(n^{3/4+\varepsilon})\). The surviving primitive cofactors satisfy \(V<v\le V^2\). Each is either prime or has all its prime factors at most \(V\) and squarefree radical larger than \(V\).

Write \(A_v\) for the right-minus-left ordinary prime price over \(pv\in(3n,4n],(2n,3n]\), with \(p>Q\) and \(p\nmid n\). Write \(L_v=(4n/v-Q)_+-2(3n/v-Q)_++(2n/v-Q)_+\). For \(n>1,\ 1\le Q\le 2n,\ V\ge1\), put \(\kappa_V(v)=\sum_{e\mid v,\,e\le V}\mu(e)\). The paper deduction gives
\[
 D(n)=\sum_{\substack{V<v\le4n/Q\\(v,n)=1}}\kappa_V(v)(A_v-L_v)
 +O\!\left(V\,2^{\omega(n)}[Q+\sqrt n+\log(4n)]\right).
\]
The implicit constant is absolute. The complete rows include their unit cofactor. Its length vanishes and its prime price equals \(-D(n)\). All other cofactors through \(V\) have coefficient zero.

**One complete divisor row.** For \(r\ge1\) let
\[
 F_r=\log\frac{\lfloor4n/r\rfloor!\,\lfloor2n/r\rfloor!}{\lfloor3n/r\rfloor!^2}.
\]
Legendre's identity gives \(F_r=\sum_s\Lambda(s)[\lfloor4n/(rs)\rfloor-2\lfloor3n/(rs)\rfloor+\lfloor2n/(rs)\rfloor]\). Every bracket has absolute value at most one. Keeping ordinary primes \(p>Q\) with \(p\nmid n\) costs at most \(\psi(Q)+\psi(4n/r)-\theta(4n/r)+\log n\). This prime sum is exactly \(\sum_{r\mid v}A_v\), by writing \(v=rw\) and counting all positive \(w\).

For \(x=n/r\), the factorial ratio satisfies \(F_r=c_0x+O(1+\log(4n))\). Rounding \(x\) down changes each factorial argument by at most three, and the constant in the integer factorial ratio is bounded. For the length sum, the set of \(w\) with \(L_{rw}>y\) has endpoints \(2x/(Q-y)\) and \(4x/(Q+y)\) for \(0<y<Q/3\). Its count differs from its length by at most one, apart from endpoint heights of measure zero. Integrating gives \(\sum_{r\mid v}L_v=c_0x+O(Q/3)\) for every real \(x>0\). The complete centered row therefore costs \(O(Q+\sqrt{n/r}+\log(4n))\), uniformly in \(r\). The existing square-root slice proof uses the same constant for all eligible divisors. [Ordinary prime slice](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ReflectedCompositeWaveTransmission.lean) · [Integer factorial ratio](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheTotientTermInTheReflectedCompositePrice.lean)

**Recombine at the same midpoint.** For \(e\le V\) coprime to \(n\), the primitive \(e\)-divisible row is the sum of the complete \(ed\)-divisible rows with weights \(\mu(d)\) over \(d\mid n\). For other \(e\) the primitive row is empty. Multiply by \(\mu(e)\), sum over \(e\le V\), then remove the unit. This gives the stated bound and preserves all three sharp endpoints. The corresponding discrete center for the uncentered prime prices is \(\sum_{e\le V,(e,n)=1}\mu(e)\sum_{d\mid n}\mu(d)F_{ed}\).

**Survivors.** If \(p>V\) divides \(v\le V^2\), every divisor of \(v\) through \(V\) divides \(v/p\le V\). Hence the coefficient equals one for \(v=p\) and zero otherwise. For smooth \(v\) whose radical is at most \(V\) the complete Möbius sum vanishes. At the first gate, \(V=\lfloor n^{1/3}\rfloor\) also gives an admissible error for every \(t>5/6\). At \(1/2<t<1\), any \(V\ll n^\delta\) with \(\delta<t-1/2\) preserves the target error. The upper bound for the remaining signed prime and smooth cofactor sum is open. [Cofactor classification](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/SignedDivisibilityAveragesOfTheReflectedCofactors.lean)

**Proof status.** Paper reduction. Lean verification of the divisible factorial identity and moving Möbius cutoff is in progress.
