# Mathematical obstacles ranked by impact on RH

Here $\Theta$ is the supremum of the real parts of nontrivial zeros of $\zeta$, $\theta(x)=\sum_{p\le x}\log p$, and $[u]_+=\max(u,0)$. Items 1–10 each imply RH. Within that tie, priority goes to estimates with a quantitative strip consequence or an already isolated arithmetic remainder. Items 11–12 improve the zero-free half-plane, 13–17 eliminate exceptional configurations, and 18 tests whether one proposed construction can reach RH at all. Equivalent formulations with the same proof input are listed under their common obstacle. [Route inventory](route-obstacles.md) · [Known obstructions](walls-ledger.md) · [Transfers between routes](route-unification-ledger.md)

### 1. Bound the composite contribution to the prime midpoint

- **Prove that** for every $1/2<t<1$ and every integer $n\ge1$, the signed price of the odd balanced composites minus the all-integer unitary-divisor center is at most $C_t n^t$. Both prices use $(3n,4n]$ minus $(2n,3n]$, restricted to integers coprime to $n$. A balanced composite here has an odd number of at least three distinct prime-power blocks, each smaller than its square root. [Exact definitions](@middefs)
- **Impact** — This upper bound gives RH. For any fixed $1/2\le b<1$, proving it for every $b<t<1$ gives exactly $\Theta\le b$. [Composite criterion](@oddcrit) · [Midpoint RH theorem](@midrh)
- **Lean facts and proof start** — The centered price differs from $D(n)=2\theta(3n)-\theta(2n)-\theta(4n)$ only by a proper-power term of size $O_\varepsilon(n^{1/2+\varepsilon})$. The full center can already be replaced at that cost by an explicit integral at each of $2n,3n,4n$. Start with the signed composite sum against those three integrals. Every balanced three-block integer has coefficient $-2$, forced by canceling the two-block products. The higher odd ranks remain in the sum. [Half-power error](@oddhalf) · [Integral center](@unitint) · [Rigidity of the triple coefficient](@rigid)

### 2. Bound the real part of the conductor tail at cubic order

- **Prove that** for $K=\lfloor N^{17/9}\rfloor$ there is one $C$ such that $\Re\,\texttt{centeredFixedPrimeTail}(N,K)\le C N^3$ for every integer $N\ge1$. This is the sum over ordinary primes above $K$ **after** summing the conductors, with the prescribed quadratic counterterm restored. [Tail and normalization](@taildef)
- **Impact** — This one-sided cubic estimate is equivalent to RH. The same upper estimate with exponent $3+2a$ gives $\Theta\le1/2+a$ for $0\le a<1/2$. [Exact exponent](@tailwidth) · [Cubic endpoint](@tailrh)
- **Lean facts and proof start** — Below the first spline knot the omitted prime weight is exactly linear. Its sum is a known multiple of $\sum_{p\le K}p\log p$, which fixes the counterterm. Apply summation by parts to the remaining primes with the signed spline intact. In the conductor-ordered decomposition, the terminal primes and their complement have opposite quartic leading terms. Bounding those absolute values separately already loses a power of $N$. [Linear part](@linpart) · [Centered comparison](@tailcomp) · [Opposite quartic terms](@quartic)

### 3. Cancel the Möbius-weighted cofactors remaining below $X^{3/7}$

- **Prove that** $|\texttt{primePowerInteriorAtExponent}(4/7,X)|\le C_\varepsilon X^{1/2+\varepsilon}$ for every $\varepsilon>0$ and integer $X\ge1$. Use the log-square sieve at the original $X$ and the quotient cutoff $\lfloor X^{4/7}\rfloor$. [Finite sum](@interior)
- **Impact** — This yields the square-root-plus-$\varepsilon$ Mertens bound for every prefix and hence RH. [Interior-to-Mertens transfer](@merttrans) · [Mertens-to-RH transfer](@mertlittle)
- **Lean facts and proof start** — At this cutoff the remaining cofactors are at most $X^{3/7}$. Removing the head costs $O(X^{1/2-1/84000})$, and the smooth center is already affordable. The signed-flux identity expresses the interior by fixed vertices and pairs crossing its endpoints. Estimate their sum at the same $X$. Moving the head to $X^{3/5}$ while retaining uniform half-plus control would itself prove $\Theta\le5/6$. [Paid head](@paidhead) · [Signed flux](@flux) · [Sharp head height](@headlaw)

### 4. Bound the accumulated positive deficit at square endpoints

- **Prove that** for every $\delta>0$ there are $C_\delta$ and arbitrarily large integers $K$ for which
  $\sum_{m\le K,\ m\ge1}[\log 2-m^{-3}\log G(m^2,m^3)]_+\le C_\delta K^\delta$,
  where $\log G(M,X)=\sum_{M<d\le2M}\lfloor X/d\rfloor\Lambda(d)$. [Gcd product identity](@gcdprod) · [Cofinal quantifier](@subpower)
- **Impact** — This sparse, one-sided estimate gives RH. Replacing $(m^2,m^3)$ by $(m^6,m^7)$, with normalization $m^{-7}$, gives exactly $\Theta\le5/6$ and the $11/3$ conductor estimate at every endpoint. [Square criterion](@gcdrh) · [Sixth-power transfer](@gcdsix)
- **Lean facts and proof start** — The total error from replacing the gcd deficits by reciprocal-Mangoldt octave deficits is at most $14(1+\log K)$. Work on the latter and bound how often and how far each octave falls below $\log 2$. The eighth-power gcd deficit already equals $\tfrac12\log K+C+o(1)$ on its own grid. Cancellation between positive and negative errors in a signed floor sum cannot bound the displayed positive parts. [Rounding after taking positive parts](@gcdround) · [Eighth-power comparison](@grid8)

### 5. Pay the mixed prime terms on the complete unit-spaced Weil comb

- **Prove that** for each integer $K\ge1$, all sufficiently large $N$, and every real profile $c$ on $S=(N,(1+3K)N]\cap\mathbb Z$, the mixed von Mangoldt debit is at most the diagonal and real-place budget of that same $c$. [Complete comb criterion](@combfull)
- **Impact** — This proves RH and supplies the full Weil sign, including mixed terms across prime contacts. [Eventual positivity and RH](@combrh)
- **Lean facts and proof start** — Every $c$ has a centered-divisibility representation with $(\sum_d|\alpha_d|)^2\le C_K N\sum_S c^2$. Payment is proved for a sufficiently small constant at this scale. The gap is payment at a constant large enough to represent every profile. Split the matrix into even and odd sites. The even block $A$ has an eventual positive floor by spacing two. It remains to bound the odd quadratic form after minimization over the even coefficients, $C-B^\top A^{-1}B$. The Liouville-twisted form has negative examples at full span, so this estimate must use the actual prime weights. [Representation](@combrep) · [Small-cost bound](@combsmall) · [Spacing theorem](@spacing) · [Liouville examples](@liouville)

### 6. Bound simultaneous opposite prime excursions at the same numerator

- **Prove that** the following joint upper-tail moment is $O_{a,g,d,\varepsilon,\eta}(X^{1/2+\varepsilon})$. Fix $a,g,\varepsilon>0$ and $0<d\le1/4$. For every sufficiently small fixed $\eta>0$, take all large $X=e^T$, $L=\lceil X^{1+\eta}\rceil$, $X^{1/(1+\eta)}\le k\le X$, and $s=\pm1$. Use $I=(k,L]$ and either flank $J_H=(\lfloor\sqrt H\rfloor,k]$ or $(L,H]$, choosing the same flank throughout the sum. With $\Delta(I,H)=\sum_{m\in I,\ \lfloor H/m\rfloor\ {\rm odd}}(\mathbf1_{m\ {\rm prime}}\log m-1)$, the moment is
  $L\sum_H [s\Delta(I,H)]_+[-s\Delta(J_H,H)]_+/H^2$.
  Sum only over $X\le H<L^2$, $H^{1/2+d}<L$, $\sqrt H<k$, where **both** signed discrepancies exceed $aX^g\sqrt H$. [Coefficient](@delta) · [Numerators and product](@jointdef)
- **Impact** — Failure of RH forces fixed $a,c,g,d,r>0$ and, for **every** $0<\eta\le r$, arbitrarily late tests with this very sum greater than $ca^2X^{1/2+3g}$. Choosing $\varepsilon<3g$ excludes the critical state and proves RH. The upper bound is a sufficient target. [Forced lower bound and order of quantifiers](@jointforce)
- **Lean facts and proof start** — Split at $H=L$. Below it the right flank is empty. On the left flank above level $B\sqrt H$, the mixed sum agrees with the interior second moment up to relative error $O(1/B)$. Use $B=aX^g$ there. Above $L$, count simultaneous exceedances with the same $H$ and weight $L/H^2$. [Below-endpoint second-moment reduction](@jointbelow)

### 7. Give long Möbius polynomials one growth exponent independent of length

- **Prove that** there is one $K\ge0$ such that for arbitrarily large fixed $\theta>0$ there is $C_\theta$ and an unbounded sequence of $T$ with
  $\int_1^T|\sum_{n\le T^\theta}\mu(n)n^{-1/2-it}|^2\,dt\le C_\theta T^K$. The sequence of heights may depend on $\theta$. [Pure Möbius criterion](@pure)
- **Impact** — This proves RH using only the Möbius polynomial. The corresponding moment with an extra $\zeta(1/2+it)$ factor can then be bounded for every length exponent and every $T\ge1$. [All-length consequence](@alllength)
- **Lean facts and proof start** — Writing $w=\Theta-1/2$, the available pure second moment costs $O_\theta(T^{4+2w\theta})$. Expand the square with the original coefficients. Its diagonal is $(T-1)\sum_{n\le T^\theta}\mu(n)^2/n$; the off-diagonal pairs with close $\log(m/n)$ require the new cancellation. Only the exponent $K$ must be uniform in $\theta$. [Current exponent](@purebaseline)

### 8. Prove cumulative decay for every modular scattering pulse

- **Prove that** for every compact smooth pulse $h$ and every $0<\sigma<1/4$, its reflected tail energy satisfies $E_h(T)\le C_{h,\sigma}e^{-2\sigma T}$ for all $T\ge0$. [Energy criterion](@pulserh)
- **Impact** — This gives RH. Every intermediate endpoint $\delta\le1/4$ attained at all rates $0<\sigma<\delta$ gives $\Theta\le1-2\delta$. In particular $\delta=1/12$ gives $5/6$. [Strip calibration](@pulsewidth)
- **Lean facts and proof start** — Rates below $3001/48000$ already hold. For a mean-zero input the field on a finite time range is an exact sum of returns at delays $2\log c$ with weights $\varphi(c)/c$. Estimate interference in the accumulated return sum, restoring the mean term for general pulses. Actual pulses can have arbitrarily many prescribed stalls, which rules out a fixed fractional loss per step. [Available rate](@pulserate) · [Return formula](@pulsereturn) · [Stalls](@pulsestall)

### 9. Bound the total heat-discriminant winding on an exhaustion

- **Prove that** the winding computed from the theta heat transform is zero on a family of regular windows covering all positive real times and all spatial heights. Equivalently, it suffices to bound the absolute total change of argument strictly below $2\pi$ on each window, including all transitions where the spatial cut changes. [Positive-time exhaustion](@heatgate)
- **Impact** — An order-$m$ collision contributes $\binom m2>0$. Vanishing on the exhaustion excludes every positive-real-time collision and proves RH. [Local multiplicity from theta](@heatlocal)
- **Lean facts and proof start** — Sufficiently thin complex-time boxes isolate the collisions of the real slice. The spatial boundary moments give the squared Vandermonde, and the correction on a shared edge is the integral of the logarithmic derivative of the ratio of the two discriminants. Bound their combined argument from theta boundary data. The existing global winding formula constructs its discriminant using the enclosed collision divisor. [Thin boxes](@heatthin) · [Seam correction](@heatseam) · [Global formula](@heatglobal)

### 10. Control every root of the unshifted Jensen polynomials at unbounded degrees

- **Prove that** for arbitrarily large degrees $d$, every root of the degree-$d$ Jensen polynomial of $\Xi$ at shift zero is real. [Cofinal splitting criterion](@jensen)
- **Impact** — The scaled polynomials along such a subsequence force $\Xi$ into the Laguerre–Pólya class and prove RH. One unshifted polynomial with a rigorously nonreal root would refute RH. [Both implications](@jensen)
- **Lean facts and proof start** — The sector estimate gives complete root control whenever $(d-1)w^2\le T^2$, with all zeros verified through height $T$ and width bound $w$. Taking $T=67$, $w=3/8$ certifies $d\le31{,}922$. A proof must control the extreme roots as $d$ increases. The existing large-shift theorem fixes $d$ and moves a different parameter. [Sector estimate](@jsector) · [Finite range](@jrange) · [Shifted theorem](@jshift)

### 11. Improve the cubic Hecke probe to exponent $2/3$

- **Prove that** the Gaussian-smoothed reciprocal cubic-probe signal is $O_{\eta,t}(Z^t)$ as $Z\to\infty$, for every ray class character $\eta$ of $\mathbb Q(\sqrt{-3})$ and every $2/3<t<1$. Fix the deleted prime ideals of norm at most 160 and Gaussian center zero. The signal is the inverse Mellin integral on $\Re s=2$ of $e^{s^2}\,\texttt{probeCorrection}_\eta(s)/L(s,\eta)$ against $Z^s$. The exponent $t$ works for every character; its constant may depend on the character. [Exact signal](@probeident)
- **Impact** — This gives a zero-free half-plane $\Re s>2/3$ for the Hecke family, away from the exceptional point $s=1$, and $\Theta\le2/3$ for ordinary $\zeta$. To apply the corpus theorem at a trial $\beta>2/3$, choose $2/3<t<\beta$ and take the comparison function to be the signal itself. Its comparison error is zero. [Hecke implication](@probehecke) · [Zeta implication](@probezeta)
- **Lean facts and proof start** — The continued correction is nonvanishing on $\Re s\ge2/3$. On the integration line, $1/L(s,\eta)$ has a signed expansion over squarefree ideals. Retain the correction when expanding the smoothed sum. Its sixth-power dilations have an exact Möbius inversion, which identifies the signed rows to estimate together. [Nonvanishing correction](@probenonzero) · [Squarefree expansion](@heckeinv) · [Signed dilations](@probedil)

### 12. Reach $5/6$ using only prime centers of the sharp midpoint

- **Prove that** for every $5/6<t<1$ there is $C_t$ such that $D(p)\le C_t p^t$ for **every ordinary prime** $p$. Here $D(p)$ compares the two neighboring intervals $(2p,3p]$ and $(3p,4p]$ from item 1. [Prime-center criterion](@primegate)
- **Impact** — This improves the corpus half-plane $\Re s>20999/24000$ to $\Re s>5/6$. It also gives the all-$N$ absolute conductor-prefix bound $CN^{11/3}$, the sixth-power deficit of item 4, and removable prime heads through $X^{3/5}$. [Corpus half-plane](@strip) · [Conductor transfer](@midstrip) · [Grid transfer](@gcdsix) · [Head transfer](@headlaw)
- **Lean facts and proof start** — Every large $n$ has an upper prime center $n<p\le2n$ with $D(n)\le D(p)+O(n^{5/6})$. At a prime center the coprimality correction has just the divisors $1,p$, and the clipped density error is $O(1)$ for $1\le Q$, $Q^2\le4p$. For $x=4p$, each band $x^{j/6}<q<x^{(j+1)/6}$, $1\le j\le5$, reproduces $D(p)$ to $O_\varepsilon(p^{5/6+\varepsilon})$ after its factorial subtraction. Bound the least of the five signed prices, allowing the choice to vary with $p$. The first surviving cofactor octave has weight $-\mu(v)$; the later octaves and the center still enter that price. [Interpolation](@primeinterp) · [Prime-center density](@clip) · [Band approximation](@bandapprox) · [Cofactor weights](@firstoct)

### 13. Exclude a third confined crossing

- **Prove that** no three distinct critical ratios of the actual zeta form support a three-state ladder, in the sense of `IsCriticalLadder 2`. [Third-state obstruction](@third)
- **Impact** — This reduces every possible failure of RH to **one** off-line quartet, at arbitrary multiplicity. It closes RH together with item 16, or with the weaker exclusion of a lone quartet. For the latter, one lower floor on all translates of the explicit pole-neutral triple with parameters $(5,6,7)$ suffices. [Zero count and critical ratios](@ratios) · [Single-quartet test](@onequartet)
- **Lean facts and proof start** — A third crossing produces a nonzero linear combination $H$ of those three states with $\mathcal LH(-1/2)=\mathcal LH(0)=0$. Its ordinary-prime wave has both signs larger in magnitude than $M e^{\delta t}$ arbitrarily late, for one $\delta>0$ and every $M>0$. Thus a one-sided upper bound $O_{H,\varepsilon}(e^{\varepsilon t})$ for every $\varepsilon>0$ on these doubly neutral waves already suffices. Use the two exact zero moments before estimating the prime sum. [Damped sign masses](@thirdmass) · [Excursion theorem](@third)

### 14. Force high zeros to approach the critical line

- **Prove that** for every $\sigma>1/2$ there is $T_\sigma$ such that $\Re(\xi'/\xi)(s)\ge0$ whenever $\Re s\ge\sigma$ and $|\Im s|\ge T_\sigma$. [Eventual Hadamard positivity](@zal)
- **Impact** — This proves the Lindelöf hypothesis on the critical line and leaves only finitely many zeros at each fixed positive distance from that line (the approach law, ZAL). Together with item 15 it proves RH. [Lindelöf implication](@lindelof) · [Two-input RH theorem](@twoatoms)
- **Lean facts and proof start** — A zero strictly to the right of a fixed vertical line forces a negative reading of $\Re(\xi'/\xi)$ immediately to its left at the same height. The reverse transfer holds at each fixed depth. Seek an arithmetic lower estimate on the whole late half-strip, allowing the required height to depend on the depth. [Local pole calculation](@localpole) · [Fixed-depth transfer](@fixeddepth)

### 15. Exclude a finite, nonempty outer layer above any background

- **Prove that** for every $h\ge0$, if any nontrivial zero of actual $\zeta$ has $\Re\rho>1/2+h$, infinitely many distinct zeros do. Zeros closer to the line may form an infinite set. [Finite-layer characterization](@aal)
- **Impact** — This proves the asymptotic abscissa law (AAL). It excludes every isolated finite outer layer and, with item 14, proves RH. Item 16 alone excludes only the case $h=0$. [AAL plus approach](@twoatoms) · [Scope of finite-stratum exclusion](@outermodel)
- **Lean facts and proof start** — In a hypothetical finite layer take its top zero and place a vertical line strictly between it and the remaining background. A contracting ordinary-prime filter already isolates that zero with a nonzero normalized limit recording its multiplicity. Get an independent arithmetic bound incompatible with that limit at the same gap, damping and frequency. Reflection and bounded height of both outer layers are already proved. [Layer structure](@layerstruct) · [Selected-zero limit](@filter)

### 16. Exclude a finite, nonempty off-line divisor

- **Prove that** if the off-line support of actual $\zeta$ is finite, every first threshold state $F$ admits $T_j\to\infty$ with $T_j\sum_{|\gamma_q|>T_j}|\mathcal LF(i\gamma_q)|^2\to0$. The sum runs over critical-line zero copies, with multiplicity. [Exact sequential target](@seqtail)
- **Impact** — This target is equivalent to “finite off-line support implies RH.” It removes all lone quartets, makes the Weil packet index either zero or infinite, and removes the exceptional alternative from the three prime-dilation tests. Infinite off-line support remains a separate case. [Equivalence](@finiteeq) · [Index dichotomy](@index) · [Prime-dilation consequence](@dilation)
- **Lean facts and proof start** — On precisely that branch the *same* scaled tail converges to $8aM/\pi>0$, where $a$ is the state's alias coefficient and $M=\int F(u)^2e^{-8u}\,du$. A sub-inverse tail on even one sequence contradicts it. Use the actual signed prime-state equation to gain cancellation in those samples. Smooth log-collar examples already realize the cusp size and fixed-window crowding. [Exact tail constant](@cusp) · [Crowding example](@crowd)

### 17. Force approaching zeros to land on the line

- **Prove that** under ZAL, the heights needed for Hadamard positivity stay bounded as $\sigma\downarrow1/2$, i.e. $\sup_{\sigma>1/2}\texttt{hadamardThreshold}(\sigma)<\infty$. The hypothesis belongs inside the implication to be proved. [Uniform height formulation](@land)
- **Impact** — This rules out infinitely many off-line zeros whose depths tend to zero under ZAL. It turns item 14 into finiteness of the entire off-line support. Items 14, 16 and 17 together prove RH. [Three-input RH theorem](@threeatoms)
- **Lean facts and proof start** — Each fixed-$\sigma$ threshold is finite under ZAL. The thresholds are monotone, and boundedness is equivalent to one height working on the whole open half-plane. A fixed Gaussian observation speed misses infinitely many shallow modes in the adverse case. Estimate the height uniformly as the depth shrinks, or equivalently bound the negative index on the two specified prime towers under ZAL. [Threshold comparison](@landheight) · [Shallow modes](@shallow) · [Two-prime index formulation](@land)

### 18. Test for a strict obstruction to the integer floor-alphabet construction

- **Prove that** there is some $1/4<a_*<1/2$ such that, for every sufficiently large alphabet bound $K$, **every** admissible balanced integer floor row supported in $[1,K]$ has normalized rate greater than $K^{-a_*}$. This is a proposed impossibility theorem. Its quantifier includes every choice of the row, multiplicity $m$ and window $B$. [Admissible rows](@aadrows) · [Rate quantifiers](@aadrate)
- **Impact** — Such a bound kills the construction that seeks rates arbitrarily close to $K^{-1/2}$, even along sparse alphabet sizes. Slower rates retain their exact zero-free payoff $\Theta\le1-a$. In the other direction, constructing rows at every $0<a<1/2$ for all sufficiently large $K$ proves RH. [Exponent transfer](@aadwidth) · [Full-rate implication](@aadrh)
- **Lean facts and proof start** — The universal rate floor is $c/(\sqrt K(1+\log K))$. This excludes exponents above $1/2$ and leaves the proposed $a_*$ open. From RH the existing construction attains every $a<1/4$. Strengthen the necessary peak-to-rate inequality for all admissible rows; optimizing the particular quarter-rate construction cannot establish the required universal lower bound. [Current floor](@aadfloor) · [Peak estimate](@aadpeak) · [Quarter-rate construction](@aadquarter)
