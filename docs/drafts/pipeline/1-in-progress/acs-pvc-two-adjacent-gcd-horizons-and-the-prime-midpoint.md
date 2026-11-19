# Two adjacent gcd horizons and the prime midpoint

Let \(L_n=\mathrm{lcm}(1,\ldots,n)\) and let \(Q_M(X)\) be the product of gcd quotients through \(X\). Counting the possible cofactors 1 and 2 gives the exact signed price
\[
 \log\frac{Q_{2n}(6n)^2}{Q_{2n}(4n)^3}
 =\log\frac{L_{3n}^2}{L_{2n}L_{4n}}
 =2\psi(3n)-\psi(2n)-\psi(4n).
\]
A divisor \(2n<d\le3n\) contributes once after subtracting the two horizons, and \(3n<d\le4n\) contributes minus once. For ordinary primes the price is exactly the log ratio of the prime products on these two intervals. The prime-power correction costs \(O(\sqrt n)\). Both adjacent cells have length \(n\). They use the same closed middle endpoint before subtraction. [Gcd factorization](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheGcdProductOnOneMangoldtOctave.lean#L90)

**Transfer of an upper bound.** Write \(V(y)=\psi(y)-y\) or \(\theta(y)-y\) and \(D(y)=2V(y)-V(2y/3)-V(4y/3)\). For \(0<b<1\), put \(q_b=((2/3)^b+(4/3)^b)/2<1\) by strict concavity. If \(D(y)\le A y^b\) for every \(y>0\), then
\[
 V(y)\le\frac{A y^b}{2(1-q_b)}\qquad(y>0).
\]
For \(\eta>0\) let \(H=\sup_{y>0}(V(y)-\eta y)/y^b\). The prime number theorem bounds this supremum at infinity, and \(V(y)=-y\) near zero. The two arguments average to \(y\), so their linear corrections cancel exactly. Thus \(2H\le 2q_b H+A\). Send \(\eta\) to zero. Applying the same argument to \(-V\) transfers a lower bound. An integer midpoint estimate at \(y=3n\) extends to all real \(y\ge3\) with an additive \(O(\log(2y))\), since all three endpoints move by at most four integers. Bounded small arguments cost a constant times \(y^b\).

It follows that for \(1/2\le b<1\), \(\Theta\le b\) is equivalent to a one-sided upper bound by \(C_\varepsilon n^{b+\varepsilon}\), for every \(\varepsilon>0\), on this **single rational product price**. The forward implication sums three Chebyshev errors. In the reverse direction the transfer gives a one-sided Chebyshev estimate. Any zero with real part above \(b\) forces larger positive errors by the project's signed oscillation theorem. The same equivalence holds for the two ordinary-prime products. At \(b=5/6\) it gives the whole-prefix \(11/3\) target. At \(b=1/2\) it gives RH. Establishing the prime-product price bound from ordinary arithmetic remains open. [Prefix equivalences](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheSeventeenNinthsConductorPrefix.lean#L914)

Lean verifies the signed gcd identity, the square-root proper-power error and both one-sided equivalences. Its transfer proof iterates the positive average at the two dilations. The initial sublinear power envelope decays geometrically under iteration. [Whole-prefix criterion](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L337) · [RH criterion](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L342) · [Reflected composites and short cofactors](acs-pvc-the-reflected-composites-at-the-prime-midpoint.md)

The Mellin numerator at a zero \(z\) is \(2\cdot3^z-2^z-4^z\). For \(0<\sigma=\Re z<1\), its modulus is at least \(2\cdot3^\sigma-2^\sigma-4^\sigma>0\). Thus every right zero survives this particular pair and its leading real density cancels exactly. The argument gives a bound independent of the ordinate on each closed substrip. [Mellin numerator bound](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMidpointInTwoAdjacentGcdHorizons.lean#L363)

**Lone-quartet trial, on paper.** Fix an upper right zero \(\rho\) and a positive integer \(m\). Its quartet alone, with multiplicity \(m\), is equivalent to the following single one-sided test on the actual midpoint price \(J(n)=2\psi(3n)-\psi(2n)-\psi(4n)\). For every \(\varepsilon>0\),
\[
 J(n)+2m\Re\!\left(\frac{2\cdot3^\rho-2^\rho-4^\rho}{\rho}n^\rho\right)
 \le C_\varepsilon n^{1/2+\varepsilon}\quad(n\ge1).
\]
The forward implication follows from the single-quartet prime formula. For the converse extend to real arguments with the same logarithmic endpoint cost. For \(\Re s>1\), the Mellin transform over \([1,\infty)\) of the midpoint price is \((-\zeta'/\zeta)(s)(2\cdot3^s-2^s-4^s)/s\) plus a holomorphic term from the finitely many divisors below 4. The pole at 1 is removable and \(\zeta\) has no real zeros in \((0,1)\). Subtracting the trial wave removes only its prescribed residues. At each real \(b=1/2+\varepsilon<1\), apply Landau's real-singularity theorem to the nonnegative difference between \(C_\varepsilon x^b\) and the trial residual. Its transform is regular at every real point above \(b\), so it converges and is holomorphic throughout \(\Re s>b\). Every additional right zero or incorrect multiplicity would leave a pole there for some \(b\) by the uniform nonvanishing above. Reflection supplies the left zeros. This works also for the ordinary-prime product and places no finiteness assumption on the initial zero set. Excluding this approximation by arithmetic remains open. [Quartet and index implications](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TwoIntervalQuartetAmplitudeAndOrdinaryPrimeObstruction.lean#L3113)

**Other adjacent horizons.** For even \(m\), on each complete quotient cell \(m/(j+1)<t\le m/j\) in \((1,2]\), the difference \(\lfloor(m+1)/t\rfloor/(m+1)-\lfloor m/t\rfloor/m\) has values \((m-j)/(m(m+1))\) and \(-j/(m(m+1))\) on the two open subintervals separated by \((m+1)/(j+1)\). Individual rational endpoints use the original floors. The corresponding lengths are \(1/(j+1)\) and \((m-j)/(j(j+1))\), so the signed area of each complete cell is zero and the integral through any interior endpoint is nonnegative. The two-horizon test above uses \(m=2\), where one cell covers the entire octave.
