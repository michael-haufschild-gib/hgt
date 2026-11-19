# Ordinary primes on a finite dyadic product fibre

For the cap-free ACS/PVC row let \(c_P(q)=\sum_{p\mid q,\ p>\max(4,P)}(\log p)g(q/p)\), with ordinary primes and \(g(v)=\mathrm{innerJump}(1,v)\). For odd \(u\), let \(L_P(u)\) be the sum of the same divisor logarithms without the cofactor weight and let \(\lambda_P(u)\) be \(\log u\) if \(u\) itself is a prime above the cutoff, zero otherwise. With \(c=\mathrm{cofactorDyadicCoefficient}\),
\[
 c_P(u)=\lambda_P(u)-L_P(u),\qquad
 c_P(2u)=(1-c)L_P(u),\qquad c_P(4u)=(1+c)L_P(u).
\]
Indeed every retained prime is odd, so the divisor list is unchanged under doubling. For each odd cofactor \(v\), the three weights are \(\mathbf1_{v=1}-1,1-c,1+c\). Thus \(c_P(u)+(c_P(2u)+c_P(4u))/2=\lambda_P(u)\) on **every odd product**. Summing through odd \(L<u\le H\) against any test recovers the ordinary prime sum on the exact interval from the three product ranges with endpoints multiplied by \(1,2,4\). The same identity applies with \(P\) chosen separately at each conductor. [Actual product coefficient](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheFiniteMeshAtAnOrdinaryFirstPrime.lean#L19) · [Cofactor weights](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/FourCofactorCapsAtAZetaZero.lean#L57)

Lean verified the three coordinates, pointwise inversion, and the weighted interval identity with both endpoints. [Three-product identity](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/OrdinaryPrimesOnThreeDyadicProducts.lean#L101) · [Weighted interval](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/OrdinaryPrimesOnThreeDyadicProducts.lean#L110)

**Including the outer quotient (paper).** Put \(Q(0)=0,\ Q(j)=W(j)\) for \(j>0\), and \(d(j)=Q(j)-Q(j-1)\). The coefficient of the single spline sample at index \(m\), after both finite sums are transposed and the full positive quotient is retained, is \(b_P(m)=(\lambda_P*g*d)(m)\), with Dirichlet convolution. The positive first quotient supplies the unit term of \(d\). For every odd \(u\),
\[
 \sum_{k=0}^{8}2^{-k}b_P(2^k u)+2^{-8} b_P(2^{10}u)=\lambda_P(u).
\]
To see this, for any coefficient \(a\) form \(A_u(z)=\sum_{k\ge0}a(2^ku)z^k\). On an odd core, Dirichlet convolution becomes convolution over the odd divisors and multiplication of the power series in \(z\). For \(g\), its value at \(z=1/2\) is \(\mathbf1_{u=1}\) by the three cofactor values above. The quotient increment is a unit mass plus a finite linear combination of \(\mathbf1_{a\mid j}-2\mathbf1_{2a\mid j}\) with \(a=1,64,129,64\cdot129\). This follows by differencing each parity \(\lfloor j/a\rfloor\bmod2\) and retaining \(W(0)=1\) in the unit correction. Each such difference has dyadic sum zero on every odd core, including when the odd part of \(a\) divides \(u\). Consequently \(D_u(1/2)=\mathbf1_{u=1}\) as well. The \(g\)-sequence is constant from \(k=2\) on, the \(d\)-sequence from \(k=7\) on. Their convolution is affine in \(k\) for \(k\ge9\), since the product of their generating functions has denominator \((1-z)^2\) and numerator of degree at most nine. For any affine tail beginning at nine, its weighted sum is \(2^{-8}b_P(2^{10}u)\). This gives the finite formula with no exchange of an infinite sum over odd cores. [Centered quotient weight](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/CenteringTheFactorialPrimeWeight.lean#L40)

**Both moving cuts (Lean verified).** After the positive quotient is inverted on odd cores, only the doubled and quadrupled product rows survive at or below the strict product cutoff. Above it, the ordinary singleton loses the full logarithms with \(n/2<v\le n\) and a fixed positive fraction of those with \(n/4<v\le n/2\). For \(U\le P\) and \(4u\le nP\) the singleton is recovered exactly. [Formulas, proof and Lean declarations](../3-formalized/acs-pvc-the-two-moving-cuts-on-odd-products.md)

For \(X>0\), any compactly supported test \(K\), and \(P=0\), summing the finite formula against \(K(u/X)\) recovers \(\sum_{p>4}(\log p)K(p/X)\). For the positive band kernel the two primes below five have bounded cost, and the density is \(X\int K\). Proving the required one-sided \(O(X^{5/6})\) estimate on this **specific finite combination** would therefore imply the whole-prefix \(N^{11/3}\) bound. Individual product sums can carry linear density. Their combined centered arithmetic error is open. [Band kernel and prime target](acs-pvc-a-positive-quadratic-band-of-first-primes.md)

The moving first-prime cutoff of §2.18 can be retained in this test. Take \(X=n^2\), \(P=\lfloor X^{19/20}\rfloor\), and write \(K(y)=k_0y\) below its first knot. Every \(p\le P\) lies on that linear segment. Lean verifies for every real scale \(X\ge1\) that
\[
 \sum_{p\le P}(\log p)K(p/X)
 =\frac{k_0 P(P+1)}{2X}+O\bigl(X^{143/180}\bigr).
\]
Indeed \(P^{17/9}/X\le X^{143/180}\), and \(143/180<5/6\). Thus the centered finite combination above may use precisely \(p>n^{19/10}\), provided its density is reduced by \(k_0P(P+1)/(2X)\). At exponent \(5/6\) the discarded first primes are paid on every square scale. The finite identities continue to hold for arbitrary weights on the same odd primes. The missing cancellation concerns their actual logarithms. [Moving prime cutoff in the integrated kernel](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheMovingPrimeCutInThePositiveBandKernel.lean)

**Odd-divisor sums at square-root precision.** Take \(P_0=\max(4,P)\), fix an integer horizon \(H\), and put
\[
 D_P(H)=\sum_{\substack{1\le d\le H,\ d\ {\rm odd}\\d\ {\rm nonprime}\ {\rm or}\ d\le P_0}}\frac{\Lambda(d)}d .
\]
For every terminal \(0\le x\le H\),
\[
 \left|\sum_{u\le x,\ u\ {\rm odd}} L_P(u)
 -\sum_{u\le x,\ u\ {\rm odd}}\log u+\frac{x}{2}D_P(H)\right|
 \le \theta(P_0)+\psi(H)-\theta(H)\ll P_0+\sqrt H .
\]
Indeed \(\log u-L_P(u)\) consists of the omitted divisor weights, by ordinary factorization. Each odd \(d\) has \(x/(2d)+O(1)\) odd multiples up to \(x\), with absolute error at most one even if \(d>x\). Summing their nonnegative weights gives the displayed bound. The baseline uses the same \(D_P(H)\) at every terminal. Lean verifies this estimate and its finite Abel sum for every test, with loss equal to its total variation plus its terminal value. [Uniform endpoint bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheOddDivisorLogarithmOnEveryProductInterval.lean#L104) · [Weighted bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheOddDivisorLogarithmOnEveryProductInterval.lean#L172)

Set \(H=\lfloor bX\rfloor\), \(P=\lfloor\sqrt H\rfloor\), and let \(K\) be the nonnegative integrated band kernel. Partial summation transfers the bound to \(K(u/X)\) at cost \(O_K(\sqrt X)\), since \(K\) has bounded variation. Put
\[
 T(X)=\sum_{u\le H,\ u\ {\rm odd}}(\log u)K(u/X)
       -\tfrac12D_P(H)\sum_{j=1}^H K(j/X)-X\int K .
\]
Then
\[
 \sum_p(\log p)K(p/X)-X\int K
 =T(X)-\sum_{\substack{u\le H,\ u\ {\rm odd\ composite}\\
                p\mid u,\ p>P_0}}(\log p)K(u/X)+O_K(\sqrt X),
\]
with ordinary primes \(p\) in the double sum. For odd \(u\) the signed product coefficient vanishes on primes and equals \(-L_P(u)\) on composites. Every eligible \(p\) exceeds \(\sqrt H\), so it occurs once and is unique. Primes through \(P_0\) cost \(O(1)\) on the linear part of \(K\), by \(\theta(P_0)\ll P_0\). Thus a **lower** bound of \(T(X)-O(X^{5/6})\) for a positive sum over odd composites would give the original \(11/3\) target. Bounds with error \(O_\eta(X^{1/2+\eta})\) for every \(\eta>0\) would give RH. The finite baseline and the square-root error use ordinary factorization. The lower bound remains open.

**Test against edits on the ordinary prime support.** Fix \(P\). If the weights above \(P_0\) change by \(e_p\), the Dirichlet series of the change in \(L_P(u)\) over odd \(u\) is
\[
 (1-2^{-s})\zeta(s)\sum_{p>P_0}e_p p^{-s},\qquad \Re s>1,
\]
by summing odd multiples of each prime. The square-root discrepancy above, with the same ordinary divisor baseline, would make the changed-minus-original series holomorphic in \(\Re s>1/2\) by partial summation. For a trial \(1/2<\Re\rho<1\), \(\Im\rho>0\), put \(e_p=-2m(\log p)\Re(p^{\rho-1})\). Its prime series has residue \(-m\) at \(s=\rho\). Indeed the translated logarithmic prime series has residue one where its argument is one, and its conjugate translate is regular at \(1+2i\Im\rho\). Thus the odd divisor bound rejects this imposed frequency whenever \(\zeta(\rho)\ne0\), even though the three-product identities still hold and the edited prime weights are eventually positive. At an actual right zero the zeta factor cancels this test pole. Excluding the genuine quartet still requires the composite lower bound or another arithmetic input.

**Sharp endpoints without a Mellin test.** With \(P=\lfloor\sqrt H\rfloor\), define the unweighted baseline \(T_H=\sum_{u\le H,\,u\ {\rm odd}}\log u-H D_P(H)/2-H\), and let \(C_H\) be the sum of the eligible prime logarithms on odd composites through \(H\). Taking the cutoff indicator as test gives
\[
 T_H-C_H=\psi(H)-H+O(\sqrt H)\qquad(H\ge1).
\]
One can instead add to \(T_H\) the exact sum of \(\Lambda(d)\) on all ineligible \(d\le H\). Its nonzero terms are the primes through \(P_0\) and proper powers with prime base at most \(\sqrt H\), both of total weight \(O(\sqrt H)\). This corrected baseline is the one used in the Lean formulation. Consequently every right zero \(\rho\) forces a deficit and a surplus of order \(h^{\Re\rho}\) in \(C_h-T_h\), at endpoints of each sufficiently large interval \(\sqrt N<h\le N\). The error above is smaller than half the known prime-error peak there. In particular, a cofinal sequence of such intervals on which \(C_h\ge T_h-Ah^{5/6}\) at every endpoint would suffice for the whole-prefix \(11/3\) bound. Lean verifies the comparison, the two signs, the \(11/3\) implication, and equivalence to RH when the lower bound holds at every exponent above one half. [Sharp comparison and cofinal criteria](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeErrorInOddCompositeProducts.lean#L51) [Both signs on every square-root interval](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/EveryRightZeroForcesBothSignsOfThePrimeError.lean#L237)

**Using only primes through the square root (paper).** Write \(v(u)=\prod_{p\le P_0}p^{\nu_p(u)}\). For \(u\le H\), the ratio \(u/v(u)\) is either one or a single large prime. Consequently
\[
 C_H=\sum_{\substack{u\le H\ {\rm odd}\\ v(u)>1}} \log(u/v(u)).
\]
The summation uses valuations of small primes and the logarithm of the integer \(u\). Replacing the hard indicator by \(1-v(u)^{-k}\) for integer \(k\ge1\) gives a lower bound with a sharp error of order \(H3^{-k}\), uniformly in \(k\) at late horizons. The error sums \(v^{-k}\log p\) over odd \(v\ge3,\ p>P_0,\ pv\le H\), hence is at most \(7H\sum_{v\ge3}v^{-k-1}\ll H3^{-k}\). The single cofactor \(v=3\) and the primes \(H/6<p\le H/3\) give the matching lower bound by the ordinary prime number theorem. At \(k=\lceil\log H/(6\log3)\rceil\) the replacement is accurate to \(O(H^{5/6})\).

At \(H=M^2\), \(M\ge4\), the same positive mass is the logarithm of an integer defined using gcd alone. Take \(L=\operatorname{lcm}(1,\dots,M)\). Then
\[
 C_{M^2}=\log \prod_{\substack{1\le u\le M^2,\ u\ {\rm odd}\\ \gcd(u,L)>1}}
               \frac{u}{\gcd(u,L^3)} .
\]
For a prime power \(p^e\mid u\) with \(p\le M\), if \(e\le2\) then \(p^e\mid L^3\). If \(e\ge3\), then \(p^{\lfloor e/2\rfloor}\le M\) and \(3\lfloor e/2\rfloor\ge e\). Thus the gcd extracts exactly the small-prime part. A surviving large prime has multiplicity one, and the outer gcd excludes its singleton. This formula gives the explicit comparison on squares below without requiring a primality test on the summation variable.

This penalty retains the sign difficulty in its divisor expansion. On odd integers define \(h_k\) by Möbius inversion of \(v(u)^{-k}=\sum_{d\mid u}h_k(d)\). Its local series at \(p\le P_0\) is \((1-z)/(1-p^{-k}z)\), and it is one above the cutoff. Thus \(h_k=\mu_{\le P_0}*(d^{-k}\mathbf1_{d\ {\rm smooth}})\), where \(\mu_{\le P_0}\) vanishes off integers with all prime factors at most \(P_0\). The total absolute difference from \(\mu_{\le P_0}\) through \(H\) is at most \(H\sum_{d\ge3} d^{-k-1}\ll H3^{-k}\) on odd inputs. Discarding the signs in this expansion loses the arithmetic still needed for the lower bound.

**Lone quartet on the same positive count (§2.3).** For an actual right zero \(\rho\) of multiplicity \(m\), a lone quartet is equivalent to
\[
 C_{\lfloor x\rfloor}-T_{\lfloor x\rfloor}
   =2m\Re(x^\rho/\rho)+O(\sqrt x\log^2 x),\qquad x\ge16.
\]
This follows in both directions from the sharp comparison and the single-wave characterization of \(\psi\), since \(\psi(x)=\psi(\lfloor x\rfloor)\). Lean verifies the equivalence without a finiteness premise. [Composite single-wave equivalence](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeErrorInOddCompositeProducts.lean#L175)

On paper a lone quartet has logarithmic period strictly below \(\log2\), so each sufficiently late octave contains both signs with size \(\gg_\rho X^{\Re\rho}\). Both peaks survive restriction to \(h=k^r\) for any fixed positive integer \(r\). Choose an interior subinterval of log length one period, then round each phase maximum to its nearest power. The resulting relative change of \(h\) is \(O_r(X^{-1/r})\), and the phase changes by \(O_{\rho,r}(X^{-1/r})\). Thus a one-sided square-root/logarithmic lower bound for the positive count along squares throughout cofinally many complete octaves would exclude a lone quartet. The independent confined index cap in §2.3 remains necessary for that route. [Single-wave characterization](../../../../formal/GaloisForLFunctions/ExclusionOfTheCriticalState/Index/SingleQuartetSecularAndWallRigidity.lean#L1931) · [Period inside an octave](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/QuadratureOfTwoConsecutivePrimeIntervals.lean#L132)

For a fixed baseline depending only on the square horizon, the positive composite mass admits an integer gcd comparison. The additional prime squares give an explicit secondary term. [Gcd product, octave criterion and quartet wave](acs-pvc-gcd-products-on-a-mangoldt-octave.md)
