# Completed signed arithmetic correspondences

An integral graph can meet another graph at a prime power. Moving one graph far along the logarithmic axis turns the sum of these local contacts into a product of degrees. The question is how much the signed intersection can differ from that product when both divisors vary. A bound must survive gluing many graphs, including graphs of opposing sign.

## Contact and degree

For real compactly supported profiles $f,g$, let $h(t)=\int f(u)g(u+t)\,du$. Composition adds logarithmic displacements. Interchanging the profiles sends $t$ to $-t$. Gluing adds their signed multiplicities before taking the correlation. The directed finite-place intersection at separation $\log X$ is

$$
 I_X(f,g)=2\sum_{n\ge1}\frac{\Lambda(n)}{\sqrt n}\,h(\log(n/X)).
$$

The sampled graph height is twice the directed logarithmic order of the integral divisors. With this same factor on the degree side, replacing the contact measure by Lebesgue measure on the positive ratio axis gives

$$
 P_X(f,g)=2\sqrt X\left(\int f(u)e^{-u/2}\,du\right)
                        \left(\int g(v)e^{v/2}\,dv\right).
$$

The object to bound is $I_X-P_X$. Its two terms may grow even when the difference is small. Taking absolute values of the intersections before gluing destroys cancellations in the test itself. The same problem occurs for conductor products whose reduced numerator and denominator both have quartic logarithmic height. [Integral graph contacts and pole moments](../ArithmeticCastelnuovoSeveri/Intersection/PoleMomentsFromSeparatedGraphContacts.lean) · [Reduced conductor heights](../CountingHolography/Sections/QuarticHeightsOfTheReducedSquarePrefix.lean)

## Perfect-power contacts

At prime ratio $p^k$, retaining the perfect $d$-th powers retains exactly the exponents divisible by $d$. This filter has a different pair of limiting degrees for every $d$. With $b=1/d-1/2$ and $M_a(f)=\int f(u)e^{au}\,du$, the directed height satisfies

$$
X^{-b}I_X^{[d]}(f,g)\longrightarrow (2/d)M_{-b}(f)M_b(g).
$$

The proof gives an identity at every separation. Put $a=(d-1)/2$, $F(u)=f(du)e^{au}$ and $G(v)=g(dv)e^{-av}$. Then $I^{[d]}_{Y^d}(f,g)=dY^{-a}I_Y(F,G)$. At $d=2$, the unscaled square contact tends to $(\int f)(\int g)$. Thus a term invisible after division by $\sqrt X$ survives in the finite part. [Exact descent and limit](PowerContactsAndTheirOppositeDegrees.lean)

Twisting the finite contacts by the Liouville sign $\lambda(p^k)=(-1)^k$ reverses the leading pole term. The ordinary contact plus its twist equals twice the square contact at every separation, so their unscaled sum tends to $2(\int f)(\int g)$. Opposite exponential tilts of a fixed positive bump give ordinary and twisted contacts of strictly opposite signs at every sufficiently large separation. [Liouville twist and square contact](TheUnscaledIntersectionOfTheLiouvilleTwin.lean)

## How to measure a glued intersection

Let $u_i$ be the lower multiplicities and $b_j$ the jumps of the upper divisor. Every integral upper divisor supported on $[1,N]$ has such a presentation. A pair $(i,j)$ integrates the same contact measure $d\psi(y)$ up to $j/i$. Replacing it by $dy$ gives $j/i$. In the smooth profile pairing the test carries the additional factor $2h(\log(y/X))/\sqrt y$, so the same replacement gives $P_X$. For the signed logarithmic graph order $H$, put

$$
c_k=\sum_{\lfloor j/i\rfloor=k}u_i b_j,\quad
P=\left(\sum_i u_i/i\right)\left(\sum_j b_jj\right),\quad
F=\sum_{i,j}u_i b_j\{j/i\}.
$$

Then $H-P+F=\sum_k c_k(\psi(k)-k)$. For each nonnegative weight $W$ and constant $C$, the bound $|H-P+F|\le C\sum_k |c_k|W(k)$ holds for every support and both signed divisors exactly when $|\psi(k)-k|\le CW(k)$ for every $k\ge1$. One lower graph against one effective upper endpoint realizes each positive quotient separately. A gain from gluing must therefore use additional structure of the divisor family or a norm that retains relations between distinct quotients. [Finite part and sharp bound](GluingIntegerGraphsAtTheirQuotientEndpoints.lean)

The de la Vallée Poussin estimate gives an unconditional price $W(k)=k\exp(-c\sqrt{\log k})$ for some $c>0$. Whenever $\sum_k|a_k|W(k)<\infty$, the completed finite part $\sum_k a_k(\psi(k)-k)$ converges absolutely. For a power price $W(k)=k^{1/2+\alpha+\varepsilon}$, estimates for every $\varepsilon>0$ and every pair of signed divisors are equivalent to the assertion that the supremum of the real parts of the nontrivial zeta zeros is at most $1/2+\alpha$. The converse follows by testing effective single endpoints and passing from integer to real cuts. This identifies the exact analytic content of changing the exponent. [Completion and the zero-abscissa criterion](CompletingTheMixedIntersectionInWeightedVariation.lean)

Multiplying each lower degree $i$ by $d$ is adjoint to moving each upper jump at $j$ to $\lfloor j/d\rfloor$. This preserves the raw height, every positive quotient coefficient and the full boundary-corrected finite part. The difference of the two pole products is $(\sum_i u_i/i)\sum_j b_j\{j/d\}$. Two successive contractions agree with contraction by the product on every positive quotient. At zero, exact composition restores the jumps that had already reached zero on the first step. [Projection and its zero-boundary term](ProjectionOfTheMixedGraphHeightUnderDilation.lean)

## Effectivity from integer factorization

Intersect every lower graph through $M$ with the upper endpoint $M$. The resulting height $H(M)$ equals $\log(M!)$ by $\sum_{q\mid m}\Lambda(q)=\log m$. Glue a whole residue block after subtracting the common dilation, setting $A_d(n)=\sum_{r<d}(H(dn+r)-dH(n))$. Then, for every $d\ge1$ and $n\ge1$,

$$0\le A_d(n+2)-2A_d(n+1)+A_d(n)\le\frac{2d^2}{(n+1)^3}.$$

The two residue indices have opposite offsets under reflection. For a single residue with offsets $z_j=(r+j+1-d)/d$ and $t=n+1$, its curvature $K$ instead satisfies $\sum_j z_j^2/(t+1+z_j)\le t(t+1)K+\sum_j z_j\le\sum_j z_j^2/(t+z_j)$. This identifies the first moment that survives a partial block and confines the rest to a sign-controlled second moment. [Complete and incomplete block bounds](EffectivityAcrossCompleteEndpointBlocks.lean)

Let $K_d(n)=\Delta^2 A_d(n)$. Frullani’s integral pairs the reflected offsets into a positive measure. Each endpoint shift multiplies the density by a monomial. Thus the mixed sum $\sum_{i,j}u_i v_jK_d(n+i+j)$ is the integral of $U(x)V(x)$ for $U(x)=\sum_i u_ix^i$ and $V(x)=\sum_j v_jx^j$. The constant section attains the exact operator norm $K_d(n)$. The bound $2d^2\|UV\|_\infty/(n+1)^3$ applies to arbitrary signed supports and the integral extends to continuous sections. This curvature concerns the logarithmic graph orders $H$. [Positive block measure and sharp norm](ThePositiveMeasureOfAMixedConductorBlock.lean)

## The real-place metric

In the Weil row of a flat upper divisor, remove $j/i-\psi(\lfloor j/i\rfloor)$ and the diagonal constant $3/(4i)-\log(2\pi)$. At $j=i+k$ the remaining entry $D_i(k)$ is half the second harmonic difference $2H_{k+i}-H_k-H_{k+2i}$. All these offsets are moments of one positive measure,

$$2D_i(k)=\int_0^1 x^k(1-x)(1+x+\cdots+x^{i-1})^2\,dx.$$

Gluing two signed families of shifts inserts their two polynomials under this integral. Equal families give a nonnegative square at every separation. Even after removing the central monomial $i^2x^{i-1}$ from the squared geometric sum, the density stays nonnegative by Cauchy–Schwarz applied to the residue indices in reverse order. The removed contribution to $2D_i(k)$ is exactly $i^2/[(k+i)(k+i+1)]$. [Mixed real-place moments](TheRealPlaceAfterGluingSignedEndpoints.lean)

Let $C_d(k)$ denote $2D_d(k)$ after this central contribution is removed. The same positive polynomial $S_d(x)^2-d^2x^{d-1}$ occurs in the integer block and the centered real metric. Shifting the complete block by one conductor gives the comparison

$$\sum_{r,j<d} C_d(dn+r+j+1)\ \le\ K_d(n)-K_d(n+1)\ \le\ \sum_{r,j<d} C_d(dn+r+j).$$

This is a quadratic-form inequality. It persists when the density in each integral is multiplied by the same square $P(x^d)^2$ for any continuous signed section $P$. For polynomial sections the metric is exactly the sum of the shifted real Weil entries. [Adjacent real metrics and the change of prime curvature](TheRealMetricBoundsTheChangeOfPrimeCurvature.lean)

## The prime defect measured by real Weil energy

For the full lower prefix through $M$ against the upper endpoint $M$, the actual opposite-degree product is $M H_M$, where $H_M$ is the harmonic number. Subtract the ordinary prime-power graph height $\log(M!)$. The second difference $G$ of this defect has entries

$$G(m)=\frac1{m+1}-\log\frac{m+2}{m+1}
=\int_0^1 x^m\left(1-\frac{1-x}{-\log x}\right)dx.$$

On $0<x<1$ the logarithmic mean $(1-x)/(-\log x)$ lies between $x$ and $(1+x)/2$. The degree-one real Weil metric has density $(1-x)/2$. Multiplying these inequalities by $x^n U(x)^2$ proves $D_1\le G\le2D_1$ as quadratic forms on arbitrary signed endpoint shifts. Consequently $|G(U,V)|\le D_1(U,U)+D_1(V,V)$ at every separation $n$. Both costs are computed from their individual divisors, before intersection. The estimate retains the pole product and all prime contacts of the full prefixes. [Mixed defect and real Weil energies](ThePoleDefectOfFullIntegralPrefixes.lean)

Keep these divisors and their pole products fixed and twist only the local contacts. At $m=b^2a$ with $a$ squarefree, the twisted column is $-\log a$. For every integer $t\ge2$, the twisted curvature is at least $\log 2$ at $t^2-1$ and at most $-1/3$ at $t^2-2$. Thus the ordinary positive lower bound fails at arbitrarily large conductors on precisely the same test. [Squarefree columns and sign failure](TheUnscaledIntersectionOfTheLiouvilleTwin.lean)

## Infinite endpoint supports

For any $u,v\in\ell^2(\mathbb N;\mathbb R)$, write $E=\|u\|_2^2+\|v\|_2^2$. The actual pole-subtracted prime curvature satisfies

$$\sum_{i,j\ge0}|u_i v_j G(n+i+j)|\le \frac{E}{2n}\qquad(n\ge1).$$

The absolute value of the signed sum also satisfies the bound by the two separate real Weil energies. These intersections arise from integral divisors. Truncate at $N$ and round each coefficient toward zero in units of $1/(N+1)$. The same two arrays of signed integer multiplicities, divided by their common scale in each variable, recover the completed intersections at both places.

The corresponding estimates for the complete block and the real metric are

$$\sum_{i,j}|u_iv_j K_d(n+i+j)|\le \frac{d^2 E}{n(n+1)},\qquad
\sum_{i,j}|u_iv_j\,2D_d(n+i+j)|\le \frac{d^2 E}{2n}.$$

Charge the two terms in $2|u_iv_j|\le u_i^2+v_j^2$ to their separate telescoping row sums. This proof covers generating functions that diverge at $x=1$. In particular, for bounded individual energies the mixed block curvature tends to zero whenever $d=o(n)$, even as both divisor supports exhaust the integers. [Infinite energy estimates and integral realization](IndependentEnergiesOfInfiniteEndpointSections.lean)

## Aligned divisibility sieves

At the upper endpoint $qm$, delete every lower graph whose conductor is divisible by $q$. The omitted pole product and prime order project exactly to the full prefix at $m$. The remaining defect is $A(qm)-A(m)$, where $A(m)=mH_m-\log(m!)$. More generally, assign lower graph $i$ the integer multiplicity $w(i)=\sum_t a_t(\mathbf1_{d_t\mid i}-\mathbf1_{q\mid i})$ with $d_t\mid q$. Write $L=\sum_t|a_t|$ and $K_w(m)$ for the second difference of the defect in $m$. Deleting every $q$-th conductor costs $L=1$.

For $m\ge1$, define the separate energy $E_m(u)=\sum_{i,j}u_i u_j[D_1(m+i+j-1)-D_1(m+i+j)]$. Its density is $x^{m-1}(1-x)^2/2$ against the square of the endpoint polynomial. For all $u,v\in\ell^2$, the signed and absolute intersections satisfy

$$
\left|\sum_{i,j}u_i v_j K_w(m+i+j)\right|\le\tfrac{L}{4}\bigl(E_m(u)+E_m(v)\bigr),\qquad
\sum_{i,j}|u_i v_j K_w(m+i+j)|\le
\frac{L(\|u\|_2^2+\|v\|_2^2)}{8m(m+1)}.
$$

The extra factor of decay comes from canceling a common curvature. Adding $\tfrac12\log m$ to $A(m)$ leaves a negative second difference with positive moment density bounded by $(1-x)^2/4$. Each stride has the same logarithmic second difference at aligned cuts. Subtracting divisibility classes cancels it exactly. Both estimates are uniform in $q$, and the completed intersection is the limit of rounded integral divisors. Giving the multiples of $q$ a common multiplicity $b$ adds exactly $bG(m)$ to the curvature, with the original full-prefix energy multiplied by $|b|$. This covers every finite signed combination of divisibility classes at the same cut. [Common logarithmic term and positive remainder](TheTrapezoidRemainderOfStridedPrefixes.lean) · [Sieved integral divisors and separate energies](SeparateEnergiesOfSievedIntegralDivisors.lean)

## Opposing sections and integral duality

Put the lower divisors at $1\le i\le X$ and the upper jumps at $j\ge X+L$. Add the directed order minus its pole product to the flat-tail Weil rows with their constant diagonal removed. For this joint height $J$, the prime contributions cancel exactly. With $S_i(x)=1+\cdots+x^{i-1}$,

$$
2J=\int_0^1x^L(1-x)U(x)V(x)\,dx,\qquad
U(x)=\sum_i u_i x^{X-i}S_i(x)^2,\quad V(x)=\sum_j b_jx^{j-X-L}.
$$

Every integer polynomial occurs as an upper section. The coefficient of $x^{X-i}$ in $(1-x)^2U(x)$ recovers $u_i$. Choosing upper jumps from the coefficients of $U$ therefore produces a strictly positive square for every nonzero lower divisor. For arbitrary mixed divisors, the bound is $|2J|\le\|UV\|_\infty/[(L+1)(L+2)]$, including $L=0$. Uniform convergence of the product sections gives convergence of the joint heights. [Opposing sections and strict duality](OppositeSectionsOfTheIntegralGraphGauge.lean)

The ordinary centered row on one effective endpoint $m$ still equals $m-\psi(m)+1/[2m(m+1)]$. For every $B>0$, this row exceeds $B\sqrt m$ and falls below $-B\sqrt m$ at arbitrarily late endpoints. Thus even effective divisors exhibit both signs. For arbitrary opposing divisors the centered row is bounded by the sum of the quotient variation with the de la Vallée Poussin weight and the real-place price $\|UV\|_\infty/[2(L+1)(L+2)]$. [Effective endpoint oscillations and mixed row estimate](CompletingTheMixedIntersectionInWeightedVariation.lean)

## The full Weil form on interleaving supports

Present both divisors $u,v$ by integral endpoint jumps. They may intersect on the diagonal or interleave in either order. Let $c_k$ be the **sum** of the quotient coefficients for the two directions, $F_{u,v},F_{v,u}$ their fractional boundaries, and $D=\sum_i u_iv_i\log(i/(2\pi))$ the diagonal counterterm. The off-diagonal real kernels give a single polynomial

$$J(x)=\sum_{i\ne j}u_i v_j\big(x^{|i-j|-1}+x^{i+j-1}\big).$$

The full mixed Weil form is recovered by

$$W(u,v)-F_{u,v}-F_{v,u}-D=-\sum_k c_k(\psi(k)-k)-\tfrac12\int_0^1 J(x)\,dx.$$

The two pole products in $W$ arise from the continuum degrees of the two directed integer heights. The completed finite part is independent of the exhaustion whenever $c_k$ converges in de la Vallée Poussin weighted variation and $J$ converges in $L^1[0,1]$. The distance is bounded by the weighted distance of the combined coefficients times a universal constant plus half the $L^1$ distance of the real sections. [Arbitrary supports and quantitative completion](TheFullWeilFormOnInterleavingDivisors.lean)

The positive quotient cells have an exact integral range. Write $u_i,v_i$ for actual conductor multiplicities, zero past the cutoff $N$. For $k\ge1$,

$$\sum_{q=k}^N c_q=\sum_{i=1}^N(u_i v_{ki}+v_i u_{ki}).$$

Their total is $2\sum_i u_i v_i$. Every integral profile with even total occurs, already with $u=\delta_1$. If the desired cells are $w_q$, set $v_1=\tfrac12\sum_q w_q$ and $v_k=\sum_{q=k}^Nw_q$ for $k>1$. Taking consecutive differences on the right gives every prescribed cell simultaneously. For self-intersections the total is twice the square mass, and each prime has further constraints from sums of squares along its valuation chains. [Integral range](TheIntegralRangeOfTheMixedQuotientCells.lean) · [Prime chain squares](../HodgeTheoryOfAFixedPart/TheContactsOfAPrimeAreChainSquares.lean)

For arbitrary interleaved divisors, give each actual conductor $i$ weight $r_i>0$, nondecreasing in $i$, and set $E_r(u)=\sum_i r_i^2u_i^2$. For a nonnegative quotient price $w_k$, put $A_N^2=\sum_{k=1}^N r_k^{-2}$ and $B_N^2=\sum_{k=1}^N(w_k/r_k)^2$. Then
$$
\sum_{k=1}^N w_k|c_k|+\tfrac12\int_0^1|J(x)|\,dx
\le (4A_NB_N+A_N^2)\sqrt{E_r(u)E_r(v)}.
$$
Each multiplicative tail has two orientations. Taking its first difference gives four terms, and Cauchy–Schwarz on each sequence of multiples costs $A_NB_N$. The two real monomials have absolute value at most one on the integration interval. When both scalar square sums converge, their limits give one bound for all cutoffs and all signed coefficients. [Separate conductor energies](SeparateConductorEnergiesOnInterleavingSupports.lean)

For fixed $r$ with $1/r\in\ell^2$, the criterion $w/r\in\ell^2$ is necessary as well. Against $u=\delta_1$, the cells are $2v_1-v_2$ and $v_k-v_{k+1}$ for $k\ge2$, with $v_{N+1}=0$. Alternating signed multiplicities ensure $|c_k|\ge|v_k|$ simultaneously. Taking $|v_k|=\lfloor M w_k/r_k^2\rfloor$ and letting the integer $M$ grow forces $\sum_{k=1}^N(w_k/r_k)^2\le C^2r_1^2$ for every cutoff. This converse uses actual integral divisors with the same single lower conductor throughout. [Sharp weight test](TheSharpWeightTestOnOneConductor.lean)

## Relation to the other programmes

Arithmetic Castelnuovo–Severi supplies the integral vertical orders. Absolute Geometry supplies the real-place kernel and identifies its contact correction on reduced square degrees. Arithmetic Orientation Geometry identifies the growth measured by translated Weil tests. Here the question concerns the price of the mixed terms when the arithmetic divisors themselves grow. [Carrier and contact](../AbsoluteGeometryOfSpecZ/TheCarrierKernelIsWeilMinusTheContact.lean) · [Arithmetic Orientation Geometry](../ArithmeticOrientationGeometry/README.md)

## What the curve point count pays for

For a three-point Kummer curve over $\mathbf F_{Q^2}$, a finite closed place of degree $h$ contributes $h$ to the square contact in degree $m$ precisely when $2h\mid m$. Including the rational point at infinity, the square contact at $m=2e>0$ equals the actual extension point count $N_e$. Removing the two poles and normalizing gives $(Q^{2e}+1-N_e)/Q^e=2g(-1)^e$, where $g$ is the dimension of the regular differentials.

At separation $4(L+1)$, put $U_b=\sum_{i\equiv b\pmod 2} u_i(-1)^{\lfloor i/2\rfloor}$, and likewise for $V_b$. After signed gluing the entire normalized trace is $2g(U_0V_0-U_1V_1)$ for every $L$ and both supports. Negating the odd part of the opposing divisor gives the effective square $2g(U_0^2+U_1^2)$. Without that sign the square is nonnegative for all divisors exactly when $g=0$, equivalently $Q+1\mid R$ for the branch exponent $R$. At $R=1$ the odd singleton is negative in every block. [Closed-place trace and duality](TheTwoSquareChannelsOfKummerPointCounts.lean)

For $y^2=f(x)$ with $f$ squarefree of odd degree over a finite field of odd characteristic, every integral polynomial $P$ has an integral opposing polynomial $Q$ at every lag $L\ge1$. Write the reversed L-polynomial as $A(T)=a+TB(T)$ and $m=\deg P$. For each Frobenius root $z$, $z[-B(z)]=a\ne0$ and $z\bar z=q$. Hence
$$
Q(T)=a^{L+m}[-B(T)]^{L+m}\sum_{j=0}^m P_j q^j T^{m-j},
\qquad z^LQ(z)=a^{2(L+m)}\overline{P(z)}.
$$
Writing $N_n$ for the curve's point count over the degree-$n$ extension, the resulting mixed trace is
$$
\sum_{j,k}P_j Q_k(q^{L+j+k}+1-N_{L+j+k})=a^{2(L+m)}\sum_z |P(z)|^2.
$$
It vanishes exactly when $P$ vanishes on every Frobenius root. Applying the opposing operation twice returns the original section on the spectrum after explicit scalar multiplication. [Integral construction, composition and nullspace](IntegralOpposingSectionsOfHyperellipticPointCounts.lean)

## Dilation on late interleaved combs

In Weil's full comb form, multiply every conductor by an integer $d\ge1$. Each prime-power ratio contact is unchanged. Both mixed pole products and each off-diagonal real jet divide by $d$. Each common diagonal gains $\log d$. For any $S\subset(N,N+M]$, $N+M\le QN$, and any signed coefficients on $dS$, the resulting square divided by coefficient square mass is at least

$$
\log(dN/(2\pi))-2\psi(Q)-
\frac{H_M+M/(4N)+M^3/(2N^3)}{d}.
$$

The inequality itself includes zero mass. For every fixed ratio and every fixed integer spacing $d\ge2$, the floor eventually exceeds any prescribed constant, uniformly in the coefficients and in the subset. Further dilation divides the harmonic loss again. At spacing one, the harmonic loss has the same leading logarithm as the diagonal. [Full comb mass under dilation](WeilMassOnDilatedCombWindows.lean)

The flat integral divisor on $(N,2N]$ has unit-spacing Rayleigh limit $E=3\log3-\log(4\pi)-\gamma\approx0.187597$. Consequently, on every fixed-ratio window containing $(N,2N]$, the coefficient-uniform floor can tend to infinity exactly at integer spacings $d\ge2$. Its optimal leading coefficient is $1-1/d$. Indeed, if $D$ is the base diagonal, $P$ the off-diagonal prime form and $M$ the coefficient square mass, then $W_d=W_1/d+(1-1/d)(D-P)+M\log d$. For the flat dyadic divisor $P=0$ and $D/M-\log N\to 2\log2-1-\log(2\pi)$. [Exact dilation and sharp spacing threshold](TheSpacingThresholdForDivergentCombFloors.lean)

A prime $p$ distinguishes two interleaved layers more finely. Pair conductors $da$ and $dp^h b$, where the cores $a,b$ are prime to $p$ and $h\ge1$. The sole prime-power contact occurs at $a=b$. Let $I_d$ be the full mixed intersection, $\eta$ the multiplier on the prime contacts, and $P=\eta(p^h)\log p\sum_a u_av_a$. Then $I_{ed}+P=(I_d+P)/e$. In particular $2I_{2d}-I_d=-P$ for every finite cutoff. Truncating square-summable coefficients and rounding them toward zero at multiplicity $N+1$ gives this inner product in the limit. Both spacings use the same two integer divisors, and the starting spacing may change at every cutoff.

If both undilated layers lie in $(N,N+M]$, put $A=2M/N+H_M+M/(4N)$. Then $|I_d+P|\le A(\|u\|_2^2+\|v\|_2^2)/(2d)$. For example, take every odd core from $2k+3$ to $4k+7$ and its double. Their endpoints interleave. Once $d\log2>A$, every nonzero matched signed vector gives a strictly negative ordinary mixed intersection and a strictly positive Liouville mixed intersection with the same pole degrees and jets. This sign refers to the two **distinct** layers. In the Kummer model, the negative unmodified square instead comes from the odd parity moment in $2g(U_0^2-U_1^2)$, and reversing that moment on one divisor gives $2g(U_0^2+U_1^2)$. [Interleaved layers and completion](PrimeContactsBetweenInterleavedValuationLayers.lean) · [Kummer parity law](TheTwoSquareChannelsOfKummerPointCounts.lean)

## Divisor incidence, the prime debit, and the macroscopic cost barrier

For any finite support $S\subset\mathbf N_{>0}$, contact weight $w:\mathbf N\to\mathbf R$, and real divisor $c:S\to\mathbf R$, split the Weil self-pairing as $\mathrm{combFormW}(w,S,c)=B_{\mathrm{dr}}(S,c)-D_w(S,c)$, where

$$
B_{\mathrm{dr}}(S,c)=\sum_{n\in S}c_n^2\log\frac{n}{2\pi}-\sum_{n\in S}\sum_{m\in S\setminus\{n\}}c_m c_n\,\mathrm{jetKernel}(m,n),
$$

$$
D_w(S,c)=\sum_{n\in S}\sum_{m\in S\setminus\{n\}}c_m c_n\,\mathrm{contactW}(w,m,n)-2\left(\sum_{n\in S}\frac{c_n}{n}\right)\left(\sum_{n\in S}c_n\right).
$$

On $S=[1,N]$ and $u=\mathrm{upperDivisor}(N,a)$, these two pieces match the diagonal-plus-real-jet budget and the mixed prime-plus-boundary debit of `interleaved_finite_part` term for term. Write $v_{d,r}(n)=\mathbf 1_{n\equiv r\pmod d}-1/d$ and $v_d=v_{d,0}$. On unshifted prefixes $[1,N]$, divisor incidence cannot pay its prime debit: already at $N=2$ the integral centered divisor $u_2(n)=2\mathbf 1_{2\mid n}-1$ satisfies $B_{\mathrm{dr}}([1,2],u_2)<D_\Lambda([1,2],u_2)$, and for every prime $p$ the self-pairing $\mathrm{combForm}([1,N],v_p)$ diverges to $-\infty$ at rate $-\frac{1}{p}(1-\frac{1}{p})N\log N$. Even on late combs $S=(N,N+3KN]$ ($K\ge1$), $D_\Lambda(S,v_p)>0$ for every prime $3K<p\le KN$, so the isolated prime-and-boundary term is strictly negative before spending $B_{\mathrm{dr}}(S,v_p)$. [Budget–debit split and prefix obstruction](ThePrimeDebitOfInterleavingSelfIntersections.lean)

On late combs $S=(N,N+3KN]$ with slices $S_r=(N,\lfloor(1+3K)N/r\rfloor]$, three elementary divisibility counts govern all residue refinements:
1. For $d_1,d_2$ coprime to $\{2,\dots,3K\}$, multiplication $m\mapsto rm$ preserves divisibility on $S_r$, giving $\sum_{m\ne n\in S}v_{d_1}(m)v_{d_2}(n)\,\mathrm{contactW}(w,m,n)=2\sum_{r=2}^{3K}w(r)\sum_{m\in S_r}v_{d_1}(m)v_{d_2}(m)$. Replacing $\Lambda$ by $\lambda\Lambda$ leaves the endpoint, real-jet, and diagonal terms unchanged and flips only nonsquare ratios $2\le r\le 3K$ from $-\Lambda(r)$ to $+\Lambda(r)$, strictly increasing every self-pairing by $4\sum_{2\le r\le 3K,\,\neg\mathrm{IsSquare}(r)}\Lambda(r)\sum_{m\in S_r}v_d(m)^2>0$.
2. For coprime $d_1,d_2\ge 1$ and any shift $h\ge 0$, Chinese Remainder incidence cancels $(b-a)/(d_1 d_2)$ identically in $\sum_{m\in(a,b]}v_{d_1}(m)v_{d_2}(m+h)$, leaving discrepancy at most $2$. Direct and reversed Abel summation give $|\mathrm{formBilinW}(w,S,v_p,v_q)|\le C_{K,w}(1+\log N)$ uniformly for all distinct primes $p\ne q$.
3. Partitioning into complete periods gives $\sum_{n\in(a,b]}v_d(n)^2\ge\lfloor(b-a)/d\rfloor(1-1/d)$ and $|\sum_{n\in(a,b]}v_{d,r}(n)|\le 1$. [Divisor incidence counts on late combs](DivisorIncidenceOnLateCombs.lean)

Orthogonal block reduction and the bounded-ratio Schur estimate combine with $|\sum_{n\in(a,b]}v_{d,r}(n)|\le 1$ to give, for every $K\ge 1$, contact weight $w$, and $\kappa>0$, a constant $C_{K,w,\kappa}>0$ such that eventually in $N$, every finite linear combination $c=\sum_{t\in T}\alpha_t v_{d_t,r_t}$ ($d_t\ge 1$) satisfies

$$
\mathrm{combFormW}(w,S,c)\ge\kappa\sum_{n\in S}c_n^2-\frac{C_{K,w,\kappa}}{N}\left(\sum_{t\in T}|\alpha_t|\right)^2.
$$

Consequently, for any $C_0>0$, both the two-prime pilot ($A_w,C_w>0$ and $B_w^2\le A_w C_w$ uniformly for moving primes $p\ne q\le\lfloor C_0\sqrt N\rfloor$) and unconditional eventual positivity on the entire unrestricted span $\{v_p:p\le\lfloor C_0\sqrt N\rfloor\}$ hold for both $\Lambda$ and $\lambda\Lambda$. Conversely, upper-triangular Möbius inversion on $S=(N,QN]$ and Bertrand's postulate ($\sum_{t=1}^Q\mu(t)/t\ne 0$ for all $Q\ge 2$) represent **every** real vector $c:S\to\mathbf R$ as $\sum_{d=2}^{QN}\alpha_d v_d$ on $S$ at macroscopic cost $(\sum_{d=2}^{QN}|\alpha_d|)^2\le C_Q N\sum_{n\in S}c_n^2$. At $Q=1+3K$, embedding the first-step sign-twin failure window produces macroscopic-cost divisibility combinations with $\mathrm{combFormW}(\lambda\Lambda,S,c)<-(1/2000)\sum_{n\in S}c_n^2<0$, proving that the $N^{-1}(\sum|\alpha_t|)^2$ cost law is sharp up to a constant factor; for $\Lambda$, paying $D_\Lambda(S,c)\le B_{\mathrm{dr}}(S,c)$ across macroscopic-cost centered-divisibility combinations at every $K\ge 1$ is unconditionally equivalent to `RiemannHypothesis`. [Controlled positivity and macroscopic barrier](ControlledDivisibilityPositivityAndTheMacroscopicBarrier.lean)

## Tests and open questions

* Beyond full lower prefixes, the multiplicative tail formula holds on arbitrary mixed divisors. Even total is the sole constraint on their positive integral quotient cells. [Range theorem](TheIntegralRangeOfTheMixedQuotientCells.lean)
* At unit spacing, a flat dyadic divisor rules out a divergent coefficient-uniform floor. A fixed positive floor on each window ratio for all signed coefficients remains equivalent to RH. [Exact late-comb criterion](../HodgeTheoryOfAFixedPart/TheRiemannHypothesisIsExactEventualCombPositivity.lean)
* For $1/r\in\ell^2$ and nondecreasing $r>0$, a support-uniform separate bound for the quotient variation and real jet holds exactly when $w/r\in\ell^2$. [Uniform estimate](SeparateConductorEnergiesOnInterleavingSupports.lean) · [Converse](TheSharpWeightTestOnOneConductor.lean)
* An integral opposing polynomial recovers a square at every positive lag for every squarefree odd-degree hyperelliptic curve in odd characteristic. On the integers, the ordinary and Liouville-twisted prefix curvatures have opposite signs at arbitrarily late cuts. [Opposing curve sections](IntegralOpposingSectionsOfHyperellipticPointCounts.lean) · [Curve model and Stepanov](../ExclusionOfTheCriticalState/Models/CurveCriticalStatesAndStepanovExclusion.lean) · [Ordinary and twisted prefixes](TheUnscaledIntersectionOfTheLiouvilleTwin.lean)

A contribution must prove a new uniform estimate, determine a sharp obstruction with a surviving arithmetic invariant, or recover a term of the completed intersection from independently defined operations. For an estimate on exhausting divisors, state which supports may grow, what each section pays, which pole and diagonal terms were removed, and whether the estimate survives passage to the limit.
