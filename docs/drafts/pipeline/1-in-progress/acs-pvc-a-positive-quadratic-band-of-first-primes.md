# A positive quadratic band of first primes

**Target in §2.18.** Write \(R=4e^8,\ a=3R/8,\ b=2R/5\). Restrict the original signed reading to first primes \(an^2<p\le bn^2\), retaining all admissible cofactors and quotient cells. The Lean-verified price at conductor \(n\), including its exterior \(n^2\), is
\[
 Cn^3+O(n^{25/9}),\qquad
 C=(1-c)W(1)\int_a^b f(2t)\,dt>0.
\]
Here \(f\) is the dyadic spline, \(W(j)=\mathrm{centeredPrimeWeight}(1,j)\), and \((1+c/2)\log 2=1\). Every late fragment has price at least a positive multiple of \((M-N)N^3\). The existing strip gives \(|B(N)|\ll N^{15/4}\). Subtracting the positive band on \((N,2N]\) therefore forces the signed contribution of the complementary first primes below \(-c_0N^4\) for some \(c_0>0\) on every late octave.

**Only one cofactor survives.** The unit cofactor has weight zero. For \(v\ge3\), already \(vp/n^2>R\), past the last spline sample. For \(v=2\), the cofactor weight is \(1-c>0\) and \(4p/n^2>R\). The sole surviving quotient contributes \(W(1)f(2p/n^2)\). The integer horizons retain both endpoints once the prime exceeds the linear geometric cutoff. On \([2a,2b]\subset(e^8,4e^8)\), the unshifted autocorrelation vanishes and the shifted one is strictly positive, so \(f<0\). Partial summation against \(\theta(x)-x=O(x^{8/9})\) gives the displayed error uniformly at the two sharp endpoints.

**First quotient sign.** Set \(A=1/\log2\), \(s_j=j^{-1/2}-(j+1)^{-1/2}\), \(S=\sum_{1\le j\le128,\ j\text{ odd}}s_j\), \(E=\sum_{1\le j\le128,\ j\text{ even}}s_j\), and \(D=64(1/8-1/\sqrt{128})\). The factorial prefix at resolution one equals \(A(j\bmod2)\). Its parity correction equals \((j\bmod2)-64\mathbf1_{64\le j<128}\) on these cells. The square-root moment therefore gives \(W(1)(S-D)=(A-1)D-E\). Here \(S\le1,\ D\ge2,\ E\le1/\sqrt2<3/4\). Since \(\log2<7/10<8/11\), \(2(A-1)>3/4\). Thus \(W(1)<0\).

**Two adjacent quotients.** Immediately below \(x=R/2\), the mesh at \(x=pv/n^2\) is exactly \(W(1)[f(x)-f(2x)]+f(2x)\). Here \(W(2)=1\) and \(f(3x)=0\). The shared endpoint contributes \((1-W(1))f(2x)<0\). At \(R/2\), \(f(R)=0\) and \(W(1)f(R/2)>0\). By continuity, the first cell is positive, the second negative, and their sum stays above a fixed positive constant on an interval below \(R/2\). At cofactor two this interval corresponds to first primes just below \(Rn^2/4\).

For first primes with \(h=p/n^2\) immediately below \(R/4\), including every cofactor adds exactly the \(v=3,4\) terms. The complete profile is
\[
 W(1)\big[(1-c)f(2h)-f(3h)\big]
 +\big[1-c+2cW(1)\big]f(4h).
\]
At \(h=R/4\), the last term vanishes. The terminal box formula below gives \(|f(3R/4)/f(R/2)|=\sqrt{2/3}[\log(4/3)/\log2]^7<1/128\), whereas \(1-c=3-2/\log2>7/69\) by \(\log2>69/100\). Thus the full prime band also stays positive on a fixed interval below \(R/4\), even after including the negative second quotient and both other cofactors.

**Three moments across all first-prime scales (paper).** For \(h=p/n^2>0\), put \(g_v=\mathrm{innerJump}(1,v)\), \(Q(0)=0\), \(Q(j)=W(j)\) for \(j\ge1\), and \(d_j=Q(j)-Q(j-1)\). The full profile on every fixed compact interval of positive \(h\) is eventually
\[
 F(h)=\sum_{v,j\ge1}g_v d_j f(vjh).
\]
Both sums are finite at each \(h\). Summation by parts in the outer quotient gives this formula with its first positive sample. The geometric prime cutoff and the original lower-product cut are eventually below every prime in such an interval.

For \(k=0,1,2\), \(\int_0^{R/2} F(h)(\log h)^k\,dh=0\). Indeed the spline has integral zero and each coefficient sequence has reciprocal sum zero. For \(g\) the latter is \(1-(1+c/2)\log2=0\). For \(d\), the parity increment at dilation \(a\) has reciprocal sum \(\log 2/a\). Each correction at \(a,64a\) cancels exactly. The remaining two terms give \(1-(1/\log2)\log2=0\). Both sequences have bounded partial sums, by periodicity for \(g\) and telescoping for \(d\). Their logarithmically weighted reciprocal sums also converge by partial summation.

To justify the integral, truncate both coefficient sequences at arbitrary independent indices. Their Dirichlet convolution has partial sums \(O(\sqrt X)\) uniformly in both truncations. Split \(vj\le X\) at \(v,j\le\lfloor\sqrt X\rfloor\), use the bounded partial sum in the long variable, and subtract the intersection. Partial summation against \(f(mh)\) bounds every truncated profile by \(O(h^{-1/2})\) on its support. This dominates all three log weights. For finite truncations substitute \(t=vjh\) and expand \((\log t-\log v-\log j)^k\). Each monomial of degree at most two omits at least one of the three logarithms. Its corresponding unweighted sum or spline integral vanishes in the limit. At finite caps \(V,J\ge1\) the zeroth moment is already zero. The first moment costs \(O(1/(VJ))\), the second \(O(1/V+1/J)\), since each unweighted reciprocal tail is \(O(1/V)\) or \(O(1/J)\).

Consequently the complete profile alternates sign on at least four disjoint, ordered open intervals of \(h\). With at most two sign changes, a polynomial in \(\log h\) of degree at most two, with roots at the sign changes, would have a product with \(F\) of constant sign and nonzero integral. The last nonzero sign is positive throughout \(R/3<h<R/2\). Thus two negative intervals lie below \(R/3\), separated by a positive one. Each contains a fixed closed band on which the profile stays away from zero. The ordinary-prime number theorem there gives the corresponding signed cubic price per late conductor and quartic price per complete late octave.

**The same centered prime band detects every right zero (paper).** For \(k\) normalized boxes on \([-1,1]\), their convolution \(B_k\) satisfies \(B_k(k-z)=z^{k-1}/(2^k(k-1)!)\) for \(0<z<2\). The first box is constant there. The next convolution is \(\frac12\int_0^z B_k(k-t)\,dt\), since the rest of the preceding box spline lies outside its support. Thus on the explicit band \([a,b]=[3R/8,2R/5]\), the eight-box formula gives \(F(h)=D h^{-1/2}u^7\), where \(D>0\) and \(u=\log(R/(2h))\in[\log(5/4),\log(4/3)]\). In particular \((hF(h))'=Dh^{-1/2}u^6(u/2-7)<0\) uniformly. [Eight-box identity](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/ThePrimeProfileOfThreeSquareConductors.lean#L72) · [Normalized box convolution](../../../../formal/GaloisForLFunctions/RHTower/WeilDeletionTestKit.lean#L178)

Write \(M(z)=\int_a^b F(h)h^{z-1}\,dh\). For \(1/2\le\beta\le1\), the log-coordinate density \(A(u)=(ae^u)^\beta F(ae^u)\), \(0\le u\le L=\log(b/a)\), is positive with \(-A'\ge c>0\) uniformly in \(\beta\). Integration by parts gives
\[
 -\Re\!\left(i\gamma\int_0^L A(u)e^{i\gamma u}\,du\right)
 = A(L)(1-\cos(\gamma L))+\int_0^L(-A'(u))(1-\cos(\gamma u))\,du .
\]
For \(|\gamma|\ge2/L\) the right side exceeds \(cL/2\). Below that threshold rotate the integral by \(e^{-i\gamma L/2}\) and take real parts. Thus \(|M(\beta+i\gamma)|\gg(1+|\gamma|)^{-1}\).

Let \(S_n\) be the original weighted price on \(an^2<p\le bn^2\) and \(C=M(1)\). In \(\sum_n S_n n^{-s}\), sum over \(n\) for each prime first. Replacing the sharp conductor sum by its integral costs \(O_K(p^{(1-\Re s)/2})\) for \(s\) in each compact set \(K\), by the two endpoint values and the integral of the absolute first derivative. These errors, weighted by \(\log p\), are locally summable for \(\Re s>3\). Writing \(z=(s-2)/2\), the integral is \(p^{-z}M(z)/2\). Removing proper prime powers from \(-\zeta'/\zeta(z)\) costs a holomorphic function for \(\Re z>1/2\). Subtracting \(C\zeta(s-3)\) therefore cancels the real pole at four. Each right zero \(\rho\) leaves residue \(-\mathrm{mult}(\rho) M(\rho)\ne0\) at \(2+2\rho\). In the general square-mesh formula the window is \(tF(1/t^2)\) on \([1/\sqrt b,1/\sqrt a)\), including its lower endpoint. [Bounded-variation square meshes](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/TheMellinKernelOfSquareConductorPrices.lean#L427)

In particular a one-sided upper bound \(\sum_{n\le N}(S_n-Cn^3)\le D N^\tau\) with \(3<\tau<4\) would already force \(\Theta\le(\tau-2)/2\). The Mellin integral of the nonnegative difference \(D x^\tau-\sum_{n\le x}(S_n-Cn^3)\) has no real singularity above \(\tau\), so Landau's theorem excludes every pole there. Under RH, partial summation against the ordinary-prime error on this fixed band gives \(O_\epsilon(N^{3+\epsilon})\) at every terminal. At \(\tau=11/3\) this would give \(\Theta\le5/6\), hence the full \(|B(N)|\ll N^{11/3}\) by the existing width equivalence. Bounds for every \(\tau=3+\eta\), \(\eta>0\), on this one centered band are equivalent to RH. The required ordinary-prime estimate remains open. [Full prefix and zero width](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheSeventeenNinthsConductorPrefix.lean#L914)

**Ordinary-prime target without a conductor sum (paper).** Extend
\[
 K(y)=\frac y2\int_{\max(a,y)}^b F(h)h^{-2}\,dh\quad(0\le y\le b)
\]
by zero for \(y>b\). Then \(K\ge0\), \(\int_0^b K=C/4\), and uniformly in every terminal \(N\),
\[
 \sum_{n\le N}(S_n-Cn^3)
 = N^2\left[\sum_p (\log p)K(p/N^2)-\tfrac C4 N^2\right]+O(N^3).
\]
For each prime integrate \(t F(p/t^2)\) through the clipped conductor interval, with \(h=p/t^2\). The two endpoints and total variation cost \(O(\sqrt p)\), also when the interval contains no integer. Summing with \(\theta(bN^2)\ll N^2\) gives the error. The kernel is globally Lipschitz on \([0,\infty)\), so replacing any real \(X\ge1\) by \(\lfloor\sqrt X\rfloor^2\) changes the centered bracket by \(O(\sqrt X)\). Thus the requested \(11/3\) estimate would follow from the single ordinary-prime upper bound \(\sum_p(\log p)K(p/X)-CX/4\le A X^{5/6}\).

This kernel increases linearly to \(a\) and decreases to zero on \([a,b]\). Indeed \(F\) is positive decreasing there, giving \(2K'(y)=\int_y^b F(h)h^{-2}\,dh-F(y)/y<0\) inside the right interval. Writing \(\Delta(x)=\theta(x)-x\), the centered bracket is exactly \(-\int_0^b K'(y)\Delta(Xy)\,dy\). Equivalently, for \(P_1(x)=\sum_{p\le x}p\log p\), the bracket equals
\[
 \frac{1}{2X}\int_a^b\frac{F(h)}{h^2}\left(P_1(hX)-\frac{(hX)^2}{2}\right)dh.
\]
This follows by exchanging a finite sum with the integral defining \(K\). The missing estimate is a one-sided \(O(X^{11/6})\) bound for that weighted integral on the fixed ratio \(b/a=16/15\). [Existing ordinary-prime first-moment estimate](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/ThePrimeMassAtAQuadraticProductDivider.lean#L163)

The Mellin transform in the scale variable gives the residues directly. Write \(E(X)=\sum_p(\log p)K(p/X)-CX/4\). For \(\Re s>1\), exchanging the prime sum and the scale integral gives
\[
 \int_1^\infty E(X)X^{-s-1}\,dX
 =\frac{M(s)}{2(s+1)}\left[-\frac{\zeta'(s)}{\zeta(s)}
    -\sum_p\sum_{j\ge2}\frac{\log p}{p^{js}}\right]
    -\frac{C}{4(s-1)}-H(s),
\]
where \(H\) is the scale integral of the prime sum over \([2/b,1]\), hence entire. Indeed \(K(p/X)=0\) for \(X<2/b\), and exchanging the two integrals defining \(K\) gives \(\int_0^b K(y)y^{s-1}\,dy=M(s)/(2(s+1))\). The proper powers are absolutely summable in \(\Re s>1/2\). Since \(M(1)=C\), the pole at one cancels, while every right zero \(\rho\) contributes residue \(-m_\rho M(\rho)/(2(1+\rho))\). This identifies directly which part of the prime sum is needed for the \(X^{5/6}\) target.

**Quartet test from §2.3 (paper).** The poles of the centered conductor series \(\sum_{n\ge1}(S_n-Cn^3)n^{-s}\) in \(\Re s>3\) are exactly the points \(2+2\rho\) with \(\Re\rho>1/2\). Its having exactly one conjugate pair of poles is therefore equivalent to a single off-line quartet, with no finiteness assumption. A pole at \(s_0=2+2\rho\) determines the multiplicity by \(-\operatorname{Res}_{s_0}/M(\rho)\). Excluding this two-pole configuration from ordinary-prime arithmetic would give the radial exclusion law in §2.3. The independent universal bound of two on the confined negative index would then imply RH. [Radial law and quartet](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TheOrdinaryPrimeRadiusDetectsExactlyOneOffLineQuartet.lean#L52) · [Index consequence](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/TwoIntervalQuartetAmplitudeAndOrdinaryPrimeObstruction.lean)

There is also a test directly on the signed conductor prices. Fix \(1/2<\Re\rho<1,\ \Im\rho>0\) and an integer \(m\ge1\). A lone quartet of multiplicity \(m\) at \(\rho\) is equivalent to each of the two estimates below.
\[
\begin{aligned}
 S_n-Cn^3
   &=-2m\Re\!\left(M(\rho)n^{1+2\rho}\right)+O(n^2\log^2(2n)),\\
 \sum_{n\le N}(S_n-Cn^3)
   &=-m\Re\!\left(\frac{M(\rho)}{1+\rho}N^{2+2\rho}\right)
     +O(N^3\log^2(2N)).
\end{aligned}
\]
For the forward implication integrate the ordinary-prime formula \(\theta(x)=x-2m\Re(x^\rho/\rho)+O(\sqrt{x}\log^2(2x))\) against \(nF(x/n^2)\) on \((an^2,bn^2]\). Both endpoint values and the integral of the absolute derivative cost \(O(n^2\log^2(2n))\) together. Summing gives the second estimate, since \(\sum_{n\le N}n^{1+2\rho}=N^{2+2\rho}/(2+2\rho)+O_\rho(N^{1+2\Re\rho})\). Conversely the first error contributes an absolutely convergent Dirichlet series in \(\Re s>3\). For the second, extending integer terminals to all real \(x\) costs \(O_\rho(x^{1+2\Re\rho})\). Partial summation integrates the cumulative error against \(sx^{-s-1}\), giving a holomorphic remainder in the same half-plane. The only poles of the centered price series there must then be the prescribed pair, with residues \(-mM(\rho)\) and its conjugate. The nonzero factor \(M\) identifies the actual zeros and their multiplicities. Thus frequency and multiplicity are fixed even for a trial made with no finiteness assumption. [Ordinary-prime formula for a lone quartet](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/QuadratureOfTwoConsecutivePrimeIntervals.lean#L107)

An upper bound on the signed error alone characterizes the same quartet. For the terminal test, subtract the trial wave from the centered prefix and call the difference \(D(x)\), extending the prefix by its floor. If \(D(N)\le A N^3\log^2(2N)\) at every late integer, the same upper bound holds on the real axis with a larger constant. The Mellin transform of the nonnegative difference \(A x^3\log^2(2x)-D(x)\), starting at a sufficiently large \(x\), continues across every real point \(s>3\). The density pole at four cancels, the two trial poles are nonreal, and \(\zeta\) has no real zero in \((1/2,1)\). Landau's theorem gives convergence throughout \(\Re s>3\). Consequently every nonreal pole must cancel with the trial pair, with the prescribed residues. The per-conductor version uses the nonnegative coefficients \(A n^2\log^2(2n)\) minus the signed error and the same argument. Thus excluding a lone quartet amounts to proving, for every trial, that the signed terminal error divided by \(N^3\log^2(2N)\) is unbounded above. This formulation uses a single real reading on the original conductors. [One-sided Landau argument for the conductor prefix](../../../../formal/GaloisForLFunctions/CountingHolography/Sections/OneSidedBoundsForTheSquareGeneratorPrefix.lean)

For comparison, replacing ordinary primes by the eventually positive measure \((1-2m\Re x^{\rho-1})\,dx\) gives exactly \(Cn^3-2m\Re(n^{1+2\rho}M(\rho))\) on the same band at every late conductor. The distinction specific to ordinary primes is the identification of their logarithmically weighted series with \(-\zeta'/\zeta\) after removing prime powers. Excluding the displayed approximation arithmetically remains open.

**Formal status.** Lean verifies the sharp band price and its complementary quartic, the signs of the two neighboring quotient cells, the terminal seventh-degree spline, and nonvanishing of its Mellin integral in logarithmic coordinates at every nonreal \(z\) with \(\Re z\le1\). The logarithmic moment identities, centered Dirichlet series, kernel reduction and signed quartet criteria above have paper proofs. [Prime-band asymptotic](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheLastFirstPrimesInTheSignedProduct.lean#L131) · [Adjacent quotient cells](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheLastTwoQuotientCellsOfTheSpline.lean#L121) · [Mellin nonvanishing](../../../../formal/GaloisForLFunctions/ExceptionalLayerTheory/SquareConductors/TheLastPolynomialPieceOfThePrimeBand.lean#L217)
