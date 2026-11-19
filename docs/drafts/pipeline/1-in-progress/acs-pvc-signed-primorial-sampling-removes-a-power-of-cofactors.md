# A signed average removes a power of small cofactors

Write \(A_v(n,Q)\) for the right-minus-left ordinary-prime log price on \(pv\in(3n,4n],(2n,3n]\), with \(p>Q\). Its continuous length is \(L_v(n,Q)=(4n/v-Q)_+-2(3n/v-Q)_++(2n/v-Q)_+\). For \(1\le V\le n^{1/3}\), take \(H=\lceil\sqrt{nV}\rceil\), \(Q=2H\), and \(\kappa_V(v)=\sum_{e\mid v,\,e\le V}\mu(e)\). The paper reduction is
\[
 D(n)=\sum_{V<v\le4n/Q}\frac{\varphi(v)}v\,\kappa_V(v)\,[A_v(n,Q)-L_v(n,Q)]
       +O_\varepsilon(n^{1/2+\varepsilon}V^{3/2}).
\]
At \(V=\lfloor n^{2/9}\rfloor\) the error is \(O_\varepsilon(n^{5/6+\varepsilon})\). The surviving cofactors have sizes between \(n^{2/9}\) and \(O(n^{7/18})\), and all contributing primes lie between \(2n^{11/18}(1+o(1))\) and \(4n^{7/9}\). Both ends move by positive powers. Primorial sampling already removes all fixed cofactors at the exact original threshold. [Formalized primorial criterion](../3-formalized/acs-pvc-rough-cofactors-on-primorial-midpoints.md) This sum has an explicit signed divisor weight. The unrestricted prime-shell bound does not estimate it directly.

**Finite divisibility identity.** Write \(M(u)=\sum_{j\le u}\mu(j)\) and \(\alpha_d=M(\lfloor V/d\rfloor)\) for \(1\le d\le V\). Then
\[
 \sum_{e\mid d,\,d\le V}\alpha_d=1\quad(1\le e\le V),\qquad
 \sum_{d\le V}\alpha_d\mathbf 1_{(d,v)=1}=\kappa_V(v).
\]
The first sum is \(\sum_{k\le V/e}\sum_{j\mid k}\mu(j)=1\). Möbius inversion of the coprimality indicator gives the second. In particular \(\sum\alpha_d=1\), and \(\kappa_V(v)=0\) for \(2\le v\le V\). The elementary bounds \(|\alpha_d|\le V/d\) give \(\sum|\alpha_d|\ll V\log(2V)\) and \(\sum d|\alpha_d|\le V^2\).

**Short averaging at an arbitrary integer.** For each \(d\le V\), average uniformly over multiples \(m=dk\) in \((n-H,n]\), then combine these averages with the signed coefficients \(\alpha_d\). Each interval of \(k\)'s has length \(\asymp H/d\) for all sufficiently large \(n\). It has primitive density \(\mathbf1_{(d,v)=1}\varphi(v)/v+O(d\tau(v)/H)\) for the condition \((m,v)=1\), by counting multiples of all squarefree divisors of \(v\) on the same interval. The finitely many remaining \(n\) are absorbed in the constant. The original midpoint changes by \(O(H\log n)\) throughout this window.

At every such \(m\), \(2\sqrt m\le Q\le2m\) for all sufficiently large \(n\). Complete forbidden-prime rows cancel exactly. The small-factor and proper-power estimates give \(D(m)=\sum_{v\ge2,(m,v)=1} A_v(m,Q)-c\varphi(m)+O_\varepsilon(Qn^\varepsilon)\). Replacing the totient center by \(\sum_{v\ge2,(m,v)=1}L_v(m,Q)\) has the same error. Indeed each Möbius divisor scale has absolute clipping error at most \(Q/3\), and the omitted unit length is zero. [Small-factor price](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheTotientTermInTheReflectedCompositePrice.lean#L313) · [Forbidden prime](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheForbiddenLargePrimeInTheReflectedCofactorIntervals.lean#L103) · [Clipping error](acs-pvc-the-joint-cofactor-block-at-the-reflected-midpoint.md)

Freeze the three sharp endpoints at \(n\) before applying the divisibility identity. Their motion in the prime coordinate for a given \(v\) is at most \(4H/v\). Counting all integers in the crossed cells, and including the length motion, costs \(O((H\log(2n)+n/Q)\log(2n))\) after summing over \(v\). The frozen ordinary-prime and length prices have absolute sum against \(\tau(v)\) of order \(O_\varepsilon(n^{1+\varepsilon})\), by the Chebyshev upper mass and \(\sum_{v\le4n/Q}1/v\ll\log(2n)\). The density error therefore costs \(O_\varepsilon(n^{1+\varepsilon}V^2/H)\). All errors together are
\[
 O_\varepsilon\!\left(n^\varepsilon[VQ+VH+Vn/Q+nV^2/H]\right).
\]
The stated \(H,Q\) balance these terms. The argument uses the same centered price and the same middle endpoint throughout. No zero-location estimate enters.

**Surviving ordinary factorizations.** If \(v\le V^2\) has a prime divisor \(q>V\), write \(v=qu\). Then \(u\le V\). Every divisor \(e\le V\) is coprime to \(q\), so \(e\mid v\) is equivalent to \(e\mid u\). Hence \(\kappa_V(v)=\mathbf1_{u=1}\). A cofactor carrying a prime above \(V\) survives only when it is **itself prime**. The other surviving cofactors have every prime factor at most \(V\) and squarefree radical greater than \(V\). On the first octave \(V<v\le2V\), \(\kappa_V(v)=-\mu(v)\) exactly. On the full range the smooth part has the complementary formula \(-\sum_{r\mid v,\,r<v/V}\mu(v/r)\). Taking \(V=\lceil(4n)^{1/5}\rceil\) ensures \(4n/Q\le V^2\) and costs only \(O_\varepsilon(n^{4/5+\varepsilon})\), below the first milestone. Thus the remaining correlation pairs an ordinary prime with either a second ordinary prime or a smooth cofactor carrying the indicated sign. [Finite weight and first octave](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/SignedDivisibilityAveragesOfTheReflectedCofactors.lean)

**Cost of removing prime cofactors.** For any normalized signed weights \(w_m\) on positive integers \(m\le n\), exact vanishing of every coprime-prime reading through \(V\) implies \(\sum_{m:\,p\mid m}w_m=1\) for each such prime. Multiplying by \(\log p\) and summing gives
\[
 \theta(V)\le\sum_m |w_m|\log m\le(\log n)\sum_m|w_m|.
\]
The first inequality uses \(\prod_{p\le V,\,p\mid m} p\mid m\). Positive averaging requires every center of positive weight to be divisible by the full primorial. General signed weights require variation \(\gg V/\log n\). This explains why multiplying separate \(O(Q)\) endpoint bounds by total variation ceases to give a power saving when \(VQ\asymp n\). It leaves the signed joint error as the object to control. The arithmetic identity and the variation obstruction have Lean source pending audit. [Signed sampling cost](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/SignedDivisibilityAveragesOfTheReflectedCofactors.lean)

**Remaining estimate.** Bound the displayed joint sum from above by \(O_t(n^t)\) at all integers for every \(5/6<t<1\). For the half-power gate choose a positive power \(V=n^\delta\) with \(1/2+3\delta/2<t\). The center still lies in the clipped region near \(v\asymp n/Q\). The outstanding signed correlation involves \(\kappa_V(v)\) and the three actual ordinary-prime endpoint readings. The full reduction is proved on paper and awaits Lean verification. At the original midpoint, direct factorial completion preserves the primitive restriction and gives a smaller cutoff cost. [Divisible cofactor rows](acs-pvc-factorial-completion-of-divisible-cofactor-rows.md)
