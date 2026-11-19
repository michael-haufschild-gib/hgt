# Quantitative factorization with signed boundaries

On a sharp interval \((L,U]\), each squarefree integer carries its Möbius sign and may carry a second arithmetic weight, such as a prime sum read at \(\lfloor X/n\rfloor\). An exchange replaces one prime factor by two distinct primes, or reverses that operation, with both integers in the interval. For the constant weight, removing disjoint opposite-sign pairs preserves the sum. For a reading \(w\), a pair \((n,m)\) contributes \(\mu(n)(w(n)-w(m))\). A pair cut by an endpoint contributes the signed reading of its retained vertex. The question is which exchanges unique factorization supplies, and how much signed mass survives at every cutoff. The target is
\[
  \left|\sum_{1\le n\le X}\mu(n)\right|\ll_\varepsilon X^{1/2+\varepsilon}
  \qquad(\varepsilon>0).
\]

The final bound remains open. One equivalent target is the centered prime-power sum at the log-square cutoff below. A global matching can leave only a vanishing fraction of vertices unpaid, but their unsigned count has power exponent one. [Centered quotient criterion](#the-smooth-term-at-the-quotient-wall) · [Unsigned obstruction](ThePowerExponentOfEveryUnsignedPrefix.lean)

Restricted factorization matching supplies the reversible moves. Signed divisor sums account for their effects on arithmetic readings across changing cuts. [Signed arithmetic programme, §§2.6 and 2.11](../../../docs/reports/review-1911/obstacles-summary.md#211-a-field-for-a-proof-by-signed-cancellation-alone)

A matching stores its positive endpoints in `sources` and their negative partners in `targets`. Transporting a negative debt follows the corresponding exchange from its negative endpoint to its positive partner.

## What a signed boundary measures

For a single involution \(F\), write \(D_F(t)\) for the signed fixed vertices through \(t\) and \(C_F(t)\) for the signed lower ends of edges crossing \(t\). The exact interval account is
\[
 M(U)-M(L)=D_F(U)-D_F(L)+C_F(U)-C_F(L).
\]
An edge spanning both cuts cancels from the difference. Prescribing the semiprimes as fixed points can make the two charges individually as large as the semiprime count. Their signs and the choice of the same involution at both cuts are essential. [Signed crossings at two walls](TheSignedCrossingsBetweenTwoWalls.lean) · [Semiprime prescription](TheCostOfFixingTheSemiprimes.lean)

A quotient reading can jump **inside** an interval. For a kernel with increments \(a(q)\), each jump places another cut at \(\lfloor X/q\rfloor\). Adding adjacent intervals cancels their common boundary when the reading agrees there. Changing the reading at that boundary leaves its signed difference. A sequence of transports must retain every intermediate change, including repeated visits to one integer. In a divisor expansion the same product can occur in several fibres. Their signed multiplicities must be recombined before estimating the error.

The principal test uses the rough Möbius row at the log-square prime cutoff. Least-prime stopping supplies its terminal rows, divisor inversion gives its smooth center, and the signed flux measures the effect of moving the quotient cuts. A quantitative gain must include the final endpoint. A general rule should gain on several weights using arithmetic independent of a Mertens bound at the proposed output exponent. [Least-prime recursion](TheSignedBoundaryOfAPrefix.lean) · [Exact quotient center](CenteringThePrimePowerReadingsAtTheirQuotientFloors.lean)

The two cutoff regimes test the signs. At \(y=\lfloor\log(X+1)\rfloor^2\) the weighted rough logarithmic prefix plus its centered reading equals \(-y\Psi(\lfloor X/y\rfloor,y)\) exactly. The critical Euler product obeys \(\log E_{1/2}(y)\sim 2\sqrt y/\log y\). At a polynomial cutoff \(b(n)=\lfloor n^\theta\rfloor\), \(0<\theta<1\), the bias to recover is negative. Compare \(\log X\,A_b(X)\) with \(-b(X)\Psi(\lfloor X/b(X)\rfloor,b(X))\). Here \(A_b\) sifts each integer at its own cutoff, whereas the quotient identity freezes one cutoff across the interval. [Critical Euler product](TheCriticalEulerPriceOfTheLogSquareCutoff.lean) · [Polynomial-cutoff comparison](TheSignedBiasOfOnePolynomialRoughSet.lean)


## Where a change of fibre matters

Quantitative Factorization Matching partitions a dyadic block by deleting one or two largest primes according to parity. A negative source with ordered cofactor \(a\) cannot be matched in that fibre if \(aP^+(a)^2\ge 2X\). The witnesses include products of three primes in separated windows of size comparable to \(X^{1/3}\). Ordering the factors differently at the exchange changes which integer is held fixed. [Ordered fibres and debt](../QuantitativeFactorizationMatching/GlobalDyadicGraphAndCofactorFibres.lean)

Write a source as \(cqr\) with \(q<r\) its two largest primes. Try the reverse move \(cqr\mapsto cp\), keeping \(c\) and replacing the entire pair. Both endpoints belong to \((L,U]\) exactly when both variable factors belong to \((\lfloor L/c\rfloor,\lfloor U/c\rfloor]\). If \(p>P^+(c)\), deleting the largest prime from the target recovers \(c\). This permits simultaneous injections over different cofactors. Within one cofactor, the relevant quantities are the number of eligible pairs and the number of available primes in the same interval.

## Prime supply in a sharp cell

Fix \(K\ge1\) and nonnegative integers \(B,D\). For sufficiently large \(s\), take any
\[
 s^2\le u\le v\le2s^2,\qquad v-u\ge s^2/(\log s)^B .
\]
Let \(A\) consist of products \(qr\in(u,v]\) with both factors prime and \(s/K<q\le Ks\). Then
\[
 D\,|A|\le\pi(v)-\pi(u).
\]
The height at which this holds is independent of both cell endpoints. For each \(q\), the prime number theorem bounds the number of possible \(r\) in the exact interval \((u/q,v/q]\). Summing over the balanced primes \(q\) uses one more factor of \(1/\log s\) than counting the available primes in \((u,v]\). This supplies spare partners even inside partial octaves. [Prime supply for balanced products](PrimeSupplyForBalancedProducts.lean)

At scale \(T=s^6\), the smaller prime can range over the entire interval \((s^2/2,2s^3]\). On sharp cells in \([T,2T]\) of width at least \(T/(\log s)^B\), these products use at most nine tenths of the available primes. Mertens' first theorem bounds the total \(\sum_q (\log q)/q\) in this exponent range. The complementary prime window supplies the second logarithm. This covers the cube-root boundary where the original cofactor can first run out of positive partners. [Uniform cube-root estimate](PrimeSupplyAtTheCubeRootBoundary.lean)

## Short exchanges on the whole half-line

Arbitrarily short exchanges retain a fixed reciprocal mass. Given an integer \(J\ge1\), every sufficiently high band \((2^k,2^{24k}]\) contains a table of distinct prime partners \(p\) for distinct semiprimes \(qr\), with all three primes in the band. Every pair satisfies \(|p-qr|\le\min(p,qr)/J\), and the paired primes satisfy \(\sum 1/p\ge1/1040\). Partition each product octave into \(J\) cells and add the reciprocal mass from \(k\) disjoint octaves. The lower bound is independent of \(J\). [Short prime exchanges](ShortPrimeExchangesOfPositiveMass.lean)

For a band with modulus \(Q=\prod_{p\in B}p\), read the entire local divisor \(d=\gcd(n,Q)\). Exactly \(\varphi(Q/p)\) residues have \(d=p\). The product bound for \(\varphi(Q)/Q\) and the paired reciprocal mass give a uniform positive detected fraction. On a squarefree integer with eligible \(d\), replace it by its table partner and retain \(n/d\). This cofactor is coprime to \(Q\), so the reverse switch recovers \(n\). Every disjoint band's gcd stays unchanged. Switching in the first eligible band therefore defines one involution, with no retries. On restricting the involution to \((X,2X]\), each eligible vertex lost at a cutoff lies within \(2X/J\) of that cutoff. [Residue density](ResidueDensityOfShortExchanges.lean) · [First eligible exchange](ReversibleSwitchesOnPrimeRanges.lean)

**Density one on every large block.** For every \(\varepsilon>0\), every sufficiently large \((X,2X]\) has a matching of squarefree integers with at most \(\varepsilon X\) unmatched and every edge of length at most \(\varepsilon X\). For a fixed tolerance one can also choose a single involution on the whole squarefree half-line. At every cutoff its fixed vertices and the vertices whose partners lie above the cutoff carry the entire signed prefix. Their number is at most \(\varepsilon X\) for all sufficiently large \(X\). With \(m\) coprime ranges, the fraction missed in a full period is at most \((1-\kappa)^m\) for an absolute \(\kappa>0\). The period and the edge resolution depend on the tolerance. [Density one for restricted exchanges](DensityOneForRestrictedPrimeExchanges.lean)

**One map works at every tolerance.** On each disjoint dyadic block, choose a matching that minimizes the larger of its unmatched count and its maximum edge length. These two-cycles define one involution on all integers. It moves each integer by \(o(n)\), and its fixed squarefree vertices and crossing endpoints through \(X\) number \(o(X)\). They carry the exact signed prefix for every \(X\). Fixed vertices accumulate over the completed blocks as a geometric sum. Only the block containing the cutoff can contribute a crossing endpoint. [One involution for every sharp prefix](OneInvolutionForEverySharpPrefix.lean)

The same involution has a quantitative bound. For some absolute \(c>0\), its unpaid count through \(X\) and its displacement at \(X\) are both \(O(X/(\log X)^c)\). To sample any bounded gcd test \(|f|\le1\) of squarefree modulus \(Q\), divisor inversion bounds the error from the complete-period mean by \(X^s\prod_{p\mid Q}(1+2/p^s)\), for \(0\le s\le1\). This allows the number of disjoint prime ranges to grow proportionally to \(\log\log X\) even when the period exceeds the cutoff. The same saving holds for both costs of a matching on every sufficiently large \((X,2X]\). [Sharp sampling of prime divisors](SamplingPrimeDivisorsAtSharpCutoffs.lean) · [Logarithmic saving](LogarithmicSavingsForRestrictedExchanges.lean)

**Matching every squarefree nonunit.** Every global restricted matching admits a new matching in which every squarefree integer greater than one has a partner. Its unpaid count is at most the original count at every cutoff. Process the fixed nonunits in increasing order. Give each such integer \(k\) a fresh legal partner \(y>k\) beyond the protected vertices and their partners. Release the former partner of \(y\). Whenever the displaced pair lay entirely below a cutoff, so does the new pair \((k,y)\). Given any threshold \(B(k)\), only \(2\#\{k\le X:B(k)<X\}\) previously moving vertices through \(X\) need change. In particular a perfect matching inherits the logarithmic saving, and its signed crossing charge is exactly \(M(X)-1\) for \(X\ge1\). [Perfect completion at every sharp cutoff](PerfectCompletionAtEverySharpCutoff.lean)

**The unsigned prefix has exact power exponent one.** For every global restricted involution \(F\), write \(U_F(X)\) for the number of fixed or crossing squarefree vertices through \(X\). For \(\theta>0\), the bound \(U_F(X)=O(X^\theta)\) holds exactly when \(\theta\ge1\). To see the obstruction, take products of \(k\ge4\) distinct primes in \((2t,4t]\). Every moving product retains a cofactor of size at least \(t^{k-2}\). It must leave its cell of length \(t^{k-2}\). Each such exit or fixed point charges one of the cell's two endpoint counts. The \(4^k t^2\) cells up to \((4t)^k\) contain \(\gg_k(t/\log t)^k\) distinct products. Taking \(k(1-\theta)>2\) forces arbitrarily large violations of every proposed power bound below one. Consequently a proof from one global involution must estimate the **signs** on its actual unpaid vertices. [Two-cutoff inequality](TheTwoCutoffsAroundASmoothVertex.lean) · [Exact unsigned exponent](ThePowerExponentOfEveryUnsignedPrefix.lean)

At the same cutoffs, both signs among the unpaid vertices exceed every prescribed bound \(CX^t\) with \(0<t<1\). If \(C_F(X)\) counts the smaller sign class, then \(U_F(X)=2C_F(X)+|M(X)|\). A bound of order \(X^t\) for that smaller class would therefore give the forbidden unsigned exponent \(\max(t,7/8)\), using the corpus bound for the full signed sum. [Opposite signs at the same cutoff](NeutralPairsAmongTheUnpaidVertices.lean)

## Simultaneous transport and its boundary

For each negative cofactor \(c\), order the eligible products \(qr\) and primes \(p\) in the sharp quotient interval. Pair equal ranks. Exactly the first \(\min(\#\{p\},\#\{qr\})\) entries of each row are used. Deleting the largest prime from \(cp\), or the largest two from \(cqr\), recovers the same \(c\). Thus rows can choose different aspect ratios and act simultaneously, with no repeated integer. For fixed aspect ratio and logarithmic relative width, every eligible product at sufficiently large quotient scale is paired. Its original ordered fibre has no positive vertex even in the full octave. [Ranked transport and exact boundary](TransportAcrossOrderedFibres.lean)

To retain old positive endpoints, start at each old positive source outside the new source set. Follow its old edge and then the inverse new edge wherever both exist. Switch to old edges at reached sources and keep new edges elsewhere. Each continuation is unique, walks from different starts never merge, and each two-edge step removes exactly two prime factors. A walk starting at \(m\) therefore has at most \(\lfloor\omega(m)/2\rfloor\) such steps. The resulting matching covers every old positive source and every negative target of the transport. [Alternating cofactor descent](AlternatingCofactorDescent.lean)

**Every empty ordered fibre can be evacuated.** Write a negative vertex as \(ar\), with \(r\) its largest prime. The scale \(X/a\) grows uniformly over these vertices. A bounded scale would bound every prime factor and force the squarefree integer \(ar\) to divide a fixed primorial. If all factors of \(a\) are at most \(\sqrt{X/a}\), two larger primes in separated windows produce a positive endpoint in its ordered fibre. Emptiness therefore forces a prime \(q>\sqrt{X/a}\). Choosing the largest such \(q\) and putting \(c=a/q\) gives \(q^3>X/c\), within the merger range. Thus one matching on each sufficiently large octave covers **all** the negative vertices in empty ordered fibres and retains the positive endpoints of any prescribed ordered matching. [Cube-root exchange](TheCubeRootExchange.lean) · [Every empty ordered fibre](EveryEmptyOrderedFibre.lean)

The evacuated family has positive density. For every negative squarefree \(c\le X^{1/24}\), put \(X/c=t^{12}\). The products \(cqr\) with \(2t^4<q\le t^5\) and \(t^{12}/q<r\le2t^{12}/q\) contribute at least \(X/(260c\log X)\) vertices in empty fibres. Their two largest primes recover the cofactor. The reciprocal sum over these negative cofactors is at least \((\log X)/192\). Thus at least \(X/49920\) distinct negative vertices in every sufficiently large octave are accessible to the global exchange and inaccessible to every ordered matching. [Prime mass in deficient rows](PrimeMassInDeficientRows.lean) · [Positive density of the transported debt](PositiveDensityOfTheTransportedDebt.lean)

Every ordered matching can gain at least \(X/49920\) disjoint pairs while retaining all of its positive and negative endpoints. In each affected old row \(b\le X^{1/24}\), set \(T=X/b\) and reassign its prime targets to products whose smaller prime exceeds \(T^{1/16}\). There are enough such products to receive the entire prime row. Deleting their largest prime distinguishes the reassigned positives from the positives reserved for the empty fibres. Alternating transport restores every original positive. The actual unmatched set is a subset of the old one, smaller by at least \(X/24960\). One can also retain every old positive and this same gain while covering the whole empty-fibre family. [Replacement capacity](RoomForDisplacedPrimeTargets.lean) · [Strict gain over ordered matchings](StrictGainOverOrderedMatchings.lean)

## The signed boundary at a cutoff

For a cutoff on the least remaining prime, write
\[
 F(L,U;y)=-\!\sum_{\substack{\max(1,L)<n\le U\\ P^-(n)>y}}\mu(n).
\]
A prime tail ends its branch. Every longer squarefree tail has a unique least prime \(p\). Writing \(P(L,U;y)=\#\{p\text{ prime}:\max(L,y)<p\le U\}\) gives the exact law
\[
 F(L,U;y)=P(L,U;y)-
  \sum_{y<p\le U\atop p\ \mathrm{prime}}
  F(\lfloor L/p\rfloor,\lfloor U/p\rfloor;p).
\]
Stop or expand separately at each row. At a stopped row the factor \(\sum_{d\mid\gcd(n,\prod_{p\le y}p)}\mu(d)\) selects its remaining integers exactly. At an expanded row charge the prime exits and reverse sign for the children. The total of both charges at the root is \(F\) for every stopping rule. Since matched pairs cancel, this also gives the signed count of the actual unmatched endpoints in the interval, including the unit when present. In particular, the prefix through \(X\) is \(\mathbf1_{X\ge1}-F(0,X;0)\). [Signed boundary and divisor inversion](TheSignedBoundaryOfAPrefix.lean)

Full expansion visits exactly one row for the empty prefix and one for each squarefree \(1<m\le U\) with all primes above \(y\). This count includes rows whose sharp interval has no admissible tail. Every adaptive cut visits at most as many. The final obstacle is estimating the signed total of its prime exits and terminal divisor sums.

At a terminal row with \(U\le y^3\), every composite tail has exactly two prime factors. For sufficiently large partial octaves of fixed logarithmic relative width the signed balance \(F\) is at least one tenth of the prime count. This sign forces transport between branches. In every large octave one least-prime branch contributes at least \(X^{3/4}/(80\log X)\). All branches with least prime in \((2X^{1/4},X^{5/16}]\) together contribute at least \(X/(200\log X)\). Every matching must account for that many vertices by unmatched endpoints in the region or by positive endpoints paired outside it. A square-root estimate cannot be obtained by bounding those branches separately in absolute value. [Signed cube-root rows and forced transport](TheSignOfCubeRootRows.lean)

A change in one permitted pair can detect a sharp power bound. For \(0<a<b\), let \(D_aG(X)=G(\lfloor X/a\rfloor)\), with \(G(0)=0\). The difference \((D_a-D_b)G\) satisfies \(O(X^\theta)\) exactly when \(G\) does, for each \(\theta>0\). Evaluating at \(X=an\) leaves the smaller argument \(\lfloor an/b\rfloor\), so induction costs a geometric factor. A finite union of gcd classes has signed prefix \(\sum_{d\in E}\mu(d)D_dM_Q\), where \(M_Q\) counts only integers coprime to \(Q\). Keeping or omitting one opposite-sign pair changes this divisor sum by such a difference. At least one choice retains every positive power exponent of the incoming prefix, simultaneously. [Sharp dilation and divisor-class identities](DetectingPowerBoundsByOneExchange.lean)

**The fixed signed prefix alone can detect every power.** For each \(\varepsilon>0\) there is a single involution with displacement at most \(\varepsilon n\) and eventually at most \(\varepsilon X\) fixed or crossing vertices through \(X\). For every \(\theta>0\),
\[
  \sum_{n\le X,\ F(n)=n}\mu(n)=O(X^\theta)
  \quad\Longleftrightarrow\quad
  \sum_{n\le X}\mu(n)=O(X^\theta).
\]
The same map works at the endpoint of the set of admissible powers. In each prime range one can omit one marked exchange or keep it. The two fixed-divisor sums differ by an invertible sharp dilation difference. Their sets of admissible exponents are nested, so one choice retains them all. After selecting the ranges, the first eligible retained exchange determines both directions of each pair. The choice compares growth classes of infinite sequences. [The Mertens exponent on one sparse fixed set](TheMertensExponentOnOneSparseFixedSet.lean)

Cutting a divisor table at two walls retains an exact signed formula. In the local class \(d\mid Q\), write \(e=F(d)\). A crossing \(cd\le X<ce\) with both endpoints in \((L,U]\) has cofactor strictly above \(a=\min(b,\max(\lfloor L/d\rfloor,\lfloor X/e\rfloor))\) and at most \(b=\min(\lfloor X/d\rfloor,\lfloor U/e\rfloor)\). Its row contributes \(\mu(d)(M_Q(b)-M_Q(a))\), where \(M_Q\) is the Möbius prefix restricted to integers coprime to \(Q\). Summing over \(d\mid Q\) gives a power estimate uniform in all three cutoffs whenever the full prefix has that power. [Signed crossings between two walls](TheSignedCrossingsBetweenTwoWalls.lean)

**Signed crossings can grow arbitrarily slowly.** Given any nonnegative \(w(X)\to\infty\), there is one restricted involution \(F\) of displacement \(o(n)\), with \(o(X)\) unpaid squarefree vertices and
\[
 \left|M(X)-\sum_{\substack{n\le X\\F(n)=n}}\mu(n)\right|
 =\left|\sum_{n\le X<F(n)}\mu(n)\right|\le w(X)
 \qquad\text{for every }X.
\]
In particular, choosing \(w(X)=\log(X+1)\) makes the signed sum on the density-zero fixed set satisfy exactly the same positive power bounds as \(M(X)\), including endpoints. The estimate controls the contribution of every moving vertex. The square-root bound for the remaining fixed signs is open. [One matching for all sharp cutoffs](ArbitrarilySlowSignedCrossingsOnOneDenseMatching.lean)

Fix the modulus \(Q\) of a divisor table. The short-interval mean square for Liouville, followed by square-divisor inversion, approximates \(f(n)=\mu(n)1_{(n,Q)=1}\) in mean absolute error by a row \(g\) with bounded partial sums. For an integer cap \(J\), retain an actual sign whenever adding it keeps the running sum \(T\) in \([-J,J]\). For every comparison row with \(|\sum_{n\le X}g(n)|\le J\), the number discarded through \(X\) plus \(|T(X)-\sum_{n\le X}g(n)|\) is at most \(\sum_{n\le X}|f(n)-g(n)|\). Increasing the cap makes the discarded fraction arbitrarily small. Both ends of an exchange have the same external cofactor, so this rule retains whole edges. Each clipped divisor row reads an interval of retained signs and costs at most \(2J\). Placing successive tables on disjoint blocks above their density and cost thresholds gives the global bound. [Bounded-primitive approximation](MeanApproximationOfCoprimeMobiusRows.lean) · [Optimal sequential thinning](BoundedSignedChargeOnCoprimeCofactors.lean) · [Clipped cofactor exchanges](BoundedCrossingChargeAtEveryPairOfWalls.lean)

**Which crossing bounds are attainable?** For a nondecreasing integer cap \(B(X)\), a density-one restricted matching with sublinear displacement can keep its absolute signed crossing charge below or equal to \(B(X)\) at every cutoff exactly when \(B(X)\to\infty\). More generally, fix \(K\). For every set \(S\) and either sign \(\sigma\), at every sufficiently large \(X\),
\[
 \#\{n\le X:n\in S,\ \mu(n)=\sigma\}
 +\#\{n\le X:|\sum_{m\le n,\,m\notin S}\mu(m)|>K\}\ \ge c_K X .
\]
For each \(k\), some fixed length has positive lower densities of windows with exactly \(k\) nonzero entries, all positive or all negative. Prime-square congruences erase unwanted offsets in a family of dilations. A multiplier selects \(k\) marks with the same sign, and a fresh prime reverses every selected sign. With \(k=2K+1\), every such window meets the selected set in its own sign or has a complementary excursion at an endpoint. [Simultaneous dilation readings](SelectingMobiusSignsByDilatingOneInterval.lean) · [Positive densities of both window orientations](EqualMobiusSignsInConsecutiveWindows.lean) · [Exact crossing threshold](TheBoundedEndpointOfSignedCrossingCharge.lean)

## Prescribing fixed vertices and their charge

A squarefree set \(S\) has density zero exactly when, for every nonnegative \(w(X)\to\infty\), one restricted matching with \(o(X)\) unpaid vertices realizes \(S\cup\{1\}\) with at most \(\min(w(X),\sqrt X)\) membership errors at every cutoff. First protect both endpoints of every edge meeting \(S\). During separated completion, a discrepancy requires an upper endpoint of a changed edge whose lower endpoint has already passed its separation threshold. [Which sparse sets can be fixed](PrescribingTheSquarefreeFixedVertices.lean)

For the squarefree semiprimes, every prime image is a distinct membership error. A fixed prime is unwanted, while a moving prime has a moving semiprime as partner. Sublinear displacement therefore forces at least \(\pi(T)\) errors through every sufficiently large \(X\ge(1+\delta)T\), for each \(\delta>0\). Allowing long exchanges attains any diverging error cap \(w\). The resulting fixed charge tracks \(1+Q_2(X)\) within \(w(X)\), where \(Q_2\) counts all squarefree semiprimes. The crossing charge tracks \(M(X)-1-Q_2(X)\) with the opposite error. [The cost of fixing the semiprimes](TheCostOfFixingTheSemiprimes.lean)

For any integer function \(h\) with \(h(0)=0\) and every increment zero or one, one density-one matching assigns \(h(M(X))\) to its fixed vertices and \(M(X)-h(M(X))\) to its crossings with opposite errors of magnitude at most \(1+w(X)/2\) at every cutoff. Select a fixed sign precisely when that step changes \(h\) along the original walk. The selected signs telescope. Taking \(h(a)=\max(a,0)\) separates the positive and negative excursions. Taking \(h(a)=\lfloor\alpha a\rfloor\) assigns any proportion \(0\le\alpha\le1\). [Nonlinear allocation of the Mertens prefix](NonlinearAllocationOfTheMertensPrefix.lean)

**Transporting charge to distant pairs.** Fix any separation function \(T\) and any nonnegative \(w(X)\to\infty\). One perfect restricted matching outside the unit has a density-zero union of whole pairs \((n,m)\) with \(m>\max(2n,T(n))\). The ordinary signed prefix of those vertices differs from \(M(X)\) by at most \(w(X)\) for all sufficiently large \(X\). A completed pair contributes zero as soon as its upper endpoint arrives. The error counts old crossings changed during completion and the finitely many old exchanges exceeding the separation. With \(w(X)=\log X\), the sparse union retains every positive power bound of \(M\), including an attained endpoint. [Signed charge on arbitrarily long exchanges](TheSignedChargeOfArbitrarilyLongExchanges.lean)

## Sifting each integer at its own cutoff

For a nondecreasing integer function \(b\), let \(A_b(X)\) sum \(\mu(n)\) over \(n\le X\) that have no prime divisor through \(b(n)\). Put \(E_s(y)=\prod_{p\le y}(1-p^{-s})^{-1}\). If \(|A_b(n)|\le Cn^s\), then
\[
 |M(X)|\le 2C(b(X)+1)E_s(b(X))^2 X^s.
\]
Conversely, a full-prefix bound \(Cn^s\) gives \(|A_b(X)|\le4C(b(X)+1)E_s(b(X))X^s\). On a constant interval of \(b\), its sifted sum is a difference of ordinary coprime prefixes. Above that cutoff, adding a prime \(p\) leads to the smaller argument \(\lfloor X/p\rfloor\) with relative weight at most \(p^{-s}\). The factor \((1-p^{-s})^{-1}\) pays the whole recursion. Both inequalities use the same fixed arithmetic set at every sharp endpoint. [Recovery from an increasing prime cutoff](RecoveringTheMobiusPrefixFromAnIncreasingPrimeCutoff.lean)

For \(b(n)=\lfloor\log(n+1)\rfloor^2\), this gives an explicit density-zero set carrying the square-root criterion. For every \(s>1/2\) and \(\eta>0\), either prefix bound of order \(X^s\) gives the other of order \(X^{s+\eta}\). Indeed, choosing \(r<1/2\) with \(s+r>1\) bounds \(\log E_s(y)\) by a constant times \(y^r\). The cost of both transfers is therefore \(X^{o(1)}\). Density zero follows by counting residues coprime to each fixed primorial. [The explicit log-square rough set](TheExplicitLogSquareRoughSet.lean)

The positive and negative counts on this set have an explicit common center. Put \(\delta_y=\zeta(2)^{-1}\prod_{p\le y}(1+1/p)^{-1}\) and \(W(X)=\sum_{1\le n\le X}\delta_{b(n)}\). Their **total** is \(W(X)+O_\varepsilon(X^{1/2+\varepsilon})\) at every cutoff. At a real endpoint \(x\), subtract \(x\delta_y\) from the count of squarefree integers avoiding primes through \(y\). For a prime \(p\), the discrepancies obey \(H_{p-1}(x)=H_p(x)+H_p(x/p)\). The squarefree counting estimate at modulus one gives \(|H_y(x)|\le 4E_s(y)x^s\) for \(1/2\le s\le1\). Summing the endpoint differences over constant intervals of \(b\) proves the total estimate. Bounding the deviation of **either individual count** from \(W(X)/2\) at the same exponents is equivalent to the full Möbius square-root criterion. [Both sign counts on the explicit rough set](TheCommonMainTermOfBothRoughSignCounts.lean)

## The smooth term at the quotient wall

Freeze the prime cutoff at \(y\ge1\), write \(\mu_y(n)=\mu(n)1_{(n,P(y))=1}\), and let \(\psi_y(t)\) count the Mangoldt weights of prime powers with base greater than \(y\). Exact divisor inversion gives
\[
 \sum_{n\le X}\mu_y(n)\log n
 =-y\Psi(\lfloor X/y\rfloor,y)
 -\sum_{m\le X/y}\mu_y(m)
   \left[\psi_y(\lfloor X/m\rfloor)-y\left\lfloor\frac{X}{ym}\right\rfloor\right].
\]
Here \(\Psi(T,y)\) counts all positive integers through \(T\) with prime factors at most \(y\), including repeated factors. Rankin's inequality gives \(\Psi(T,y)\le T^s E_s(y)\). The entire first term therefore costs \(O_\varepsilon(X^{1/2+\varepsilon})\), uniformly for every \(y\le\lfloor\log(X+1)\rfloor^2\). The remaining sum reads the actual prime powers at the sharp quotient endpoints. [Exact centering and the smooth population bound](CenteringThePrimePowerReadingsAtTheirQuotientFloors.lean)

With \(y=b(X)=\lfloor\log(X+1)\rfloor^2\), bounding that **single sequence of centered readings** by \(O_\varepsilon(X^{1/2+\varepsilon})\) is equivalent to the same bound for the full Mertens prefix. For any nondecreasing weight \(v\) with \(v(1)>0\), a bound \(Cv(1)n^s\) on the weighted sum at the single frozen cutoff \(b(n)\) controls every unweighted row with \(y\ge b(n)\) by \(CE_s(y)n^s\). Partial summation spends at most \(CE_s(y)n^s(v(n)-v(1))\) on smaller endpoints. The observed sum pays the remaining unit weight. For logarithmic readings, taking \(v(n)=\log(\max(2,n))\) adds exactly \(\log 2\) at the unit. Undoing the Euler factors then recovers the unrestricted prefix. [Weighted inversion](InvertingAWeightedReadingAtAMovingPrimeCutoff.lean) · [The centered prime-power criterion](OneCenteredPrimePowerReadingAtTheLogSquareCutoff.lean)

## Open questions and success criteria

* Can one group of reversible exchanges lower the exponent on a growing range of quotient cells for the prime-power and exact-floor readings together? Both interval endpoints, exceptional divisor classes, changes of reading and the signed fixed contribution enter the estimate.
* Can the same operation recover the negative smooth bias at a polynomial prime cutoff and the exact negative smooth center at the log-square cutoff, then bound the recombined residual at every endpoint?

* Between the proved logarithmic saving and the obstruction to every power saving, what joint decay of the unpaid fraction and relative displacement can one involution attain?
* Can the largest-pair rows receive every excess of a maximum ordered matching, including excesses in nonempty fibres? For each new cofactor, the demand is a sum of positive parts of the old rows' deficiencies. A comparison of their signed totals can underestimate that demand.
* Which stopped rows must cancel against each other or against the prime boundary? The estimate must hold at **every** cutoff. For one global involution the unsigned power theorem forces cancellation between unpaid vertices.

Arithmetic Orientation Geometry deletes Euler factors from a damped Möbius weight. The prime cutoff in a tail deletes those same divisibility classes and retains both integer endpoints. Exceptional Layer Theory gives a different test of the target exponent. The ordinary-prime sum of its factorial parity profile has exactly the Mertens power bounds above one half. In this calculus the quotient profile also records the least prime, which determines the eligible exchanges at the next level. [Euler factor deletion](../ArithmeticOrientationGeometry/EulerFactorsAndPayment.lean) · [Prime sums of the factorial parity profile](../ExceptionalLayerTheory/ThePrimeErrorAtTheLinearGrowthBoundary.lean)

The wider corpus obtains an unrestricted matching with \(O_\beta(X^\beta)\) unmatched vertices for every \(\beta>20999/24000\) from a zero-free strip. Its endpoint relation allows arbitrary opposite signs. Here the arithmetic of the allowed pairs and the signed boundary charges must supply the estimate. [Unrestricted matching and the zero-free strip](../QuantitativeFactorizationMatching/DyadicMatchingStripAndRiemannEquivalence.lean)

A contribution must enlarge the proven range of arithmetic exchanges, determine the exact signed remainder of a growing construction, or bound that remainder. Unrestricted pairing only measures the original signed sum. Fixed cofactor, arity and layer restrictions have distinct obstructions. The target square-root estimate implies RH by continuation of the reciprocal zeta series and reflection. [Restricted matching obstructions](../QuantitativeFactorizationMatching/CompleteResolutionOfTheFactorizationMatchingQuestion.lean) · [Dyadic transfer](../QuantitativeFactorizationMatching/DyadicMatchingStripAndRiemannEquivalence.lean)
