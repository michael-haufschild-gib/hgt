# Arithmetic Incidence Positivity (AIP)

**One question.** The zero form of $\zeta$ is a jump form whose conductance between two points is a
gauge factor times a kernel built from the archimedean density, the prime atoms and the pole. On
which pairs is that conductance negative, how large is the negative part, and what in the
arithmetic of the integers pays it?

AIP is a theory of **pairs**. It reads the critical form conductance by conductance, as a weighted
graph on the line whose arithmetic edges are the incidence relations of the integers: the pair
$(\log a,\log b)$ is coupled through the ratio $b/a$ when $a\mid b$, and $(-\log a,\log b)$ through
the product $ab$. Every statement is unconditional and names the pairs it concerns.

Namespace `GaloisForLFunctions.ArithmeticIncidencePositivity`; umbrella
`ArithmeticIncidencePositivity.lean`. Objects come from `RHTower` and ACT — do not redefine them.

---

## 1. Place in the research

AIP owns the **incidence face** of the shared target: conductance by conductance, with the pole
as the only positive source on crossing pairs. It is a live route: the **global incidence
allocation** with the canonical plateau gauge at every aperture is RH-equivalent; the open
estimate is joint payment of all prime and pole costs on every odd compact test. Progress is
scored in the width unit: a ledger deficit at rate $2\sigma$ at every aperture = strip $\tfrac12+\sigma$.

Three mechanisms shape the field: the ratio/product classification makes the lattice skeleton
positive; reflection and Schur estimates pay atoms locally and give window certificates; translate
Gram identities compress towers to first-power correlations, leaving cross-prime correlations
and their signed balance with the pole — expressed through one two-pole Chebyshev defect.

| Programme | Connection |
|---|---|
| arithmetic-positivity-theory | Source families; Weil–Markov–pole form; grid-tent transfer of AIP windows |
| BiScaleUncertainty | Autocorrelation constraints, blind models |
| TransHorizonIncidenceMechanics | Finite identities vs uniform payment; nine moduli seen from the sieve side |
| BezoutValuationIncidence | Valuations, divisor Gram tools; sign-blindness of period forms |
| ArithmeticCriticalityTheory | Gauges, ground-state representations, zero form, light-cone law |
| SquareRootThreshold | Graded ledger → lag rate → width; odd windows transfer to $P_v$ |
| ArithmeticCompensationTheory | Raw comb energy is $\sim4e^{2r}$ (sharp); translation/resolvent of the comb |
| SignedArithmeticEnergyIncidence | Sine-train capacities; local allocation with frustration |
| ArithmeticOrientationTheory | Product pairs are the only frustrating edges; one square per tower |
| ArithmeticOrientationGeometry, SignedSuccessorArithmetic | Signed form vs absolute majorant; which observations keep orientation |
| TransThresholdPairCorrelation | Close prime pairs = height-averaged prime-ratio correlations (the replacement hypothesis) |
| Others (ACCE, SSIC, ACS) | Extension of local certificates; signed info across scales; effectivity |

Three levels must stay separate: comparison of scalar weights, an integrated energy inequality,
and positivity for all compact tests (only the last is RH).

---

## 2. Why

**The zero form is a jump form.** In an odd gauge $\omega>0$ on $(0,\infty)$, $M=\Phi\omega$,
$\mu=M\sinh(x/2)$:
$Z(\Phi\omega u)=\int dm(t)\int M(x)M(x+t)(u(x)-u(x+t))^2+\iint\mu(x)\mu(y)(u(x)-u(y))^2$
(`zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy`). Per unordered pair the **gauge-free kernel**
is $k(x,y)=dm(|x-y|)+2\sinh(x/2)\sinh(y/2)$ (the factor 2 is forced by the two orders in the
variance integral).

**Same side vs across.** $M(x)M(y)>0$ same side, $<0$ across. Negative conductance lives only on
crossing pairs where $k>0$: on the prime anti-diagonals $|x|+y=\log n$, and where the archimedean
density beats the polar weight.

**Incidence.** On the lattice $\{\pm\log a\}$: same-side atom iff $b/a$ is a prime power (ratio
pair); crossing atom iff $ab$ is a prime power (product pair, forcing one tower).

**Polar compensation.** On the crossing pair $(-a,s-a)$ the polar weight is
$P_s(a)=2\sinh\frac a2\sinh\frac{s-a}2=\cosh\frac s2-\cosh(\frac s2-a)$ — the only positive source. It
pays the archimedean density except on axis collars of length $\asymp2e^{-s}$, vanishes at the axes
(never pays an atom near the ends), and at the midpoint dominates $\Lambda(n)/\sqrt n$ except for
$n\in\{2,3,4,5,7\}$, and atom + density except for the **nine moduli** $\{2,3,4,5,7,8,9,11,13\}$.

**Where the difficulty sits.** Lattice pairs are decided; the pole pays the archimedean continuum
off the collars. What remains is the prime atom near the axes of its anti-diagonal (all $n$) and
along the whole anti-diagonal for the nine moduli, to be paid by same-side atoms and the gauge
with no slack.

---

## 3. Objects and language

| Object | Lean |
|---|---|
| $\omega$, prime atom $\Lambda(n)/\sqrt n$ | `RHTower.archLevyDensity`, `RHTower.vonMangoldtAtom` |
| Signed jump / variance energy | `ArithmeticCriticalityTheory.signedJumpEnergy`, `varianceEnergy` |
| Archimedean pair kernel, crossing symbol $S(s)=\cosh\frac s2-\omega(s)$, threshold $s_0\in(\log5,\log6)$ | `archPairKernel`, `crossingSymbol`, `crossingThreshold` |
| Ratio / product / net atoms; skeleton energies | `ratioAtom`, `productAtom`, `netAtom`, `ratioEnergy`, `productEnergy`, `skeletonEnergy` |
| Dyadic window $(X/2,2X)$; two-bump window | `InDyadicWindow`, `SquareRootThreshold.lagPrimeWindow` |
| Polar weight; collar; collar ends | `crossingPolarWeight`, `antiDiagonalCollar`, `collarInnerEnd`, `collarOuterEnd` |
| Five / nine moduli; total kernels | `atomDominatedModuli`, `totalDominatedModuli`, `totalLatticeCrossingKernel`, `totalAntiDiagonalKernel` |
| Unpaid set and level of $n$ | `unpaidSet`, `antiDiagonalLevel` |
| Strip box energy $T(p,r)$, shells, fold constants | `stripBoxEnergy`, `shellIntegrand`, `stripFoldConstant`, `shellFoldConstant` |
| Prime strip charge; light-cone and thin bands; edge tents | `primeStripCharge`, `lightConeBand`, `thinBand`, `edgeTent`, `edgeTentOdd` |
| Ledger pieces | `surplusPool`, `crossingPotentialTerm`, `evenStripGain`, `oddStripCost`, `gaugeRemainder`, `poleCharge`, `aperturePlateau` |
| Global allocation; reflected-prime/polar cost | `GlobalIncidenceAllocation`, `reflectedPrimePolarCost` |
| Pairing, autocorrelation $A(t)$, translate/geometric trains | `testPairing`, `autoCorr`, `translateComb`, `geoTrain` |

**Words.** Pair *same-side* ($xy>0$) / *crossing* ($x<0<y$), sum $s=|x|+y$, imbalance $x+y$.
*Negative conductance* on a crossing pair = $k>0$. *Tower* $\{p^i\}$. *Lag charge*: weighted sum of
$A$ at a progression of lags. *Resonant direction*: train of disjoint bump copies at that spacing.
*Anti-diagonal of $n$*. *Collar*. *Payment*: polar weight $\ge$ negative conductance.

---

## 4. Mechanisms

### Archimedean kernel and lattice
1. **Sign law.** For crossing pairs $k_{\text{arch}}>0\iff\cosh(\frac{x+y}2)>S(y-x)$; $S$ increases and
   crosses 1 once at $s_0\in(\log5,\log6)$: below $s_0$ every crossing pair is negative; beyond, only
   unbalanced ones within $3e^{-3s/4}$ of an axis.
2. **Lattice closed form.** $k_{\text{arch}}(-\log a,\log b)<0$ off the axes except $\{2,2\},\{2,3\}$;
   reflected pairs negative only at $a=2$.
3. **Dominance and scale suppression.** On product pairs $ab=p^{i+j}$:
   `productAtom a b = ratioAtom a b / a`; the prime skeleton is a nonnegative graph Laplacian and
   $\ge(1-1/A)$ ratio energy on $[A,\infty)$.
4. **Total lattice law.** With atoms, the crossing kernel is positive exactly on
   $\{2,2\},\{2,3\},\{2,4\},\{3,3\}$; off-diagonal same-side conductance strictly dominates.
5. **Windows.** Inside a dyadic window divisor relations are doublings/triplings; product pairs are
   $(p^i,p^{i+1})$, $p\in\{2,3\}$, of size $O(1/X)$; inter-window couplings bounded by ratio-band sums.

### Continuum: polar compensation
6. **Anti-diagonal decomposition** $k_{\text{arch}}=\omega(s)-P_s(a)$; pointwise payment off the collar;
   collar of exact order $2e^{-s}$ (second-order expansion); unpaid archimedean mass $O(e^{-3s/2})$.
7. **Atom vs pole classifications.** Pointwise: atom wins everywhere iff $n\in\{2,3,4,5,7\}$; with the
   density iff $n$ in the nine moduli; for $n\ge23$ unpaid points within $\asymp2(1+\Lambda(n))/n$ of the
   axes. Integrated against gauges: all log-concave gauges pay iff $n\notin\{2,3,4,5,7,11,13\}$;
   first-jet log-concave iff $n\notin\{2,3,4,5,7,11\}$; shifted ground states $m_a$ (large $a$, midpoint
   concentration) iff $n\notin\{2,3,4,5,7\}$.

### The odd fold and windows
8. **Folded odd plateau.** Every archimedean crossing conductance is paid by its same-side partner
   leaving a killing $4\int F^2(\Omega(x)-\Omega(x+r))$; plateau potential via the edge function;
   $\hat Z\ge\frac1{40}\int F^2$ on odd $[-\frac7{25},\frac7{25}]$.
9. **Selectivity.** Shifted pair $\zeta(s-a)\zeta(s+a)$: odd form $2\hat Z(F)+4\int(\cosh at-1)(2\cosh\frac t2-\omega)A_F$;
   negative past $\log\rho/2$ and (via the Hankel limit, $f=\omega-2\cosh(t/2)$ not log-convex) already on
   $[-\frac{13}{125},\frac{13}{125}]$, while $\zeta$ is coercive on $[-\frac{21}{200},\frac{21}{200}]$.
10. **Curved fold.** Exact fold $J_P=$ killing $+2S_P$ with surplus kernel $\omega(|x-y|)-\omega(x+y)$;
    cubic/quartic gauges give odd windows $17/50$, $347/1000$ (past $\frac12\log2$).
11. **Micro-fold Harnack.** Splitting $F$ about $\frac12\log n$ into even/odd parts: the atom costs only
    the odd part; the reflection strip's surplus pays it (constant $\to\log2+\frac12$, sharp version
    $1.9$ via the regional log kernel, eigenvalue 2). **Every prime-power atom is paid by its own
    strip** for windows $\frac12\log n<r\le\frac12\log n+\frac1{12}$; keeping the even part makes the atom
    a net gain (e.g. $n=4$).
12. **Schur lending and the prime atom paying the strip.** Ground-state remainder → potential on
    rectangles $Z\times H$; exact identity $\int FF(\cdot+L)=2\int_S\alpha^2-\int_SF^2$; windows $353/1000$,
    $356/1000$, $9/25$, $181/500$ with $\hat Z\ge\frac1{1000}\int F^2$.
13. **Shared strip surplus.** Strips $S_n=[\log n-r,r]$ are nested: shell micro-fold, union and chain
    allocations (e.g. $\{23,25\}$ needs the shell); **light cone** of exact square-root width
    $\delta\asymp e^{-r}$ (Selberg sieve) shares one copy of the surplus; beyond it, edge tents and the
    bipolar edge-dipole defeat odd-part sharing and signed band sharing; **logarithmic capacity**
    $\frac7{10\log6}\log\frac1{12\varepsilon}\le\text{Cap}\le2\log\frac4\varepsilon+84$.
14. **Overlapping strips of 2 and 3.** Wide and harmonic folds pay both atoms through $r=23/40$ with
    $(1/62)\int_{S_2}F^2$ spare; **odd-part payment ends before $\log2$** (linear profile counterexample,
    quotient $\to12-16\log2<\sqrt2\log2$).
    **Nine-modulus window.** At $r=2\log2$ the prime powers among the relevant shifts $[2,15]$ are
    exactly the nine moduli, so prime charge and comb energy reduce to them with zero error. From
    $r=23/40$ on, smooth odd tests separate $\zeta$ from the Liouville-twisted weight (Catalan pair
    $(8,9)$ carries opposite signs; Liouville ground eigenvalue $<-3/10$ and antitone).
15. **Global shared-surplus allocation.** Light cone shares the pool; every other atom is charged to
    its strip mass $m_n(F)$. What remains is paying strip masses — the prime–polar problem.

### The ledger at every aperture
16. **Incidence ledger.** For odd $F$ on $[-r,r]$, plateau $P$:
    $\hat Z(F)=\text{pool}+\text{crossing potential}+\sum\text{gains}-\sum\text{costs}+\text{gauge remainder}-\text{pole charge}$
    (`fullZeroForm_eq_incidenceLedger`); all but the remainder nonnegative; remainder purely
    archimedean with explicit floor. RH ⇔ `GlobalIncidenceAllocation` at every aperture. Explicit
    ledger floor with no Weil operator. Graded by width.
17. **Large-aperture content.** Beyond lag $O(1)$ the surplus is negligible ($\omega\asymp e^{-t/2}$ vs
    prime/polar densities $\asymp e^{t/2}$); correlations beyond $r$ are at most $a(0)/2$ (constant, not a
    power saving); edge tests make pole charge and prime correlation both $\asymp e^r$ with opposite
    signs. Rate 1 is the prime–polar balance at PNT level.

### Translate calculus and towers
18. **Pairing calculus**; geometric train resolvent identity.
19. **Prime tower law.** Two-step square ⇒ $(p-1)C_p(F)\le\log p\,(A(0)+\sqrt pA(\log p))$: a whole tower is
    controlled by $A(\log p)$; envelope attained by resonant trains; Liouville twin bound
    $\log p(A(0)-\sqrt pA(\log p))$ attained by alternating trains — the tower law reads the sign of $A(\log p)$.
20. **Bi-tower law** for two spacings (products and ratios as payers); **bi-lattice train**: two aligned
    towers resonate fully and envelopes add (cross-prime aggregate strictly positive).
21. **Divisor-lattice Gram positivity** of one modulus; squarefree subset forms; Möbius comb blind on
    resonant directions.
22. **Prime-comb reduction and its limit.** Cost side ≤ $\sqrt{A(0)E_w(F)}$; a polynomial cross-prime
    aggregate would give a polynomial bound — but raw comb energy is $\sim4e^{2r}$ on smooth odd families
    (ArithmeticCompensationTheory), so the raw second moment is not the open quantity.
23. **Rank one per tower.** Lattice product part of tower $p$ is $\log p(S_p(q)^2-q(1)^2)$.

### The Chebyshev ledger
24. **Balance = receiver.** $\sum\Lambda(n)h(\log n)-\int(e^s+1)h=\int E(s)h'(s)ds$ with
    $E(s)=e^s+s-1-\psi(e^s)$; second order against $D(s)+s^2/2-s$; for $h=2e^{-s/2}A$ the polar integral is
    the pole plane.
25. **Instrument on sources.** Defect is a complete invariant (`eq_of_lagPrefix_eq`); shifted pair,
    Liouville, Beurling, dilations, Möbius/characters each have their own ledger; ideal source matches
    to $1+\log2$; bounded defect forces density; $E$ unbounded.
26. **Discrete receiver** on integer cells; first prime windows are identities.
27. **Test geometry.** Half-mass bound beyond the aperture; ladder $\cos(\pi/(k+1))$; quadratic gap;
    banded Gram of atoms; **replacement hypothesis**: a power saving over the $\ell^1$ prime cost ⇔
    bounded Schur constant for prime-ratio correlations; defect coordinate with free $3/4$ (odd: $1/2$)
    discount on high lags.
28. **Euler comb ledger** (sequential payment law for every weight $\le1$) and **spectral symbol**: the
    whole Chebyshev pairing is $2\int(\text{primeSymbol}_N(\xi)-2K_{2r}(2\pi\xi))|\hat F|^2$; a pointwise
    symbol floor is a floor for every test; the pole pays only on $|\xi|\le1/(8r)$ where odd tests carry
    cubically small mass.
29. **Reflected-prime/polar ledger at every aperture.**
    $\hat Z=\text{pool}+\text{crossing potential}+\text{remainder}-\text{reflectedPrimePolarCost}$; cost = Chebyshev
    pairing; sharp pole charge $\le(2\sinh r-2r)\int F^2$; bipartite halving; pure-mass bound
    $69e^r\int F^2$, PNT prefactor $(3+\varepsilon)e^r$; Sobolev dlVP saving $e^{r-c\sqrt r}$; shared
    derivative-energy payment; `GradedIncidenceAllocation (1/2) 75`.
30. **Sign flips.** Period quadratic forms are sign-blind; comb energy and two-atom translate laws see
    signs through the ratio lag $\log(b/a)$.

### Bridges
31. **Continuum crossing-to-ratio bridge.** Unpaid atom set = two axis intervals with inner end
    $2\Lambda(n)/(n-1)$; cubic Lipschitz suppression there; continuum crossings priced through an
    intermediate ratio shift; at $23/40$ an explicit ledger floor with the pole still subtracted.
32. **Bump bridge.** Single-bump archimedean self-energy $\sim M(\alpha)^2(\int\beta^2)w\log(1/w)$, $O(w^2)$
    decoupling; calibrated remainder → lattice incidence form in `netAtom`; lattice positivity is
    small-support positivity.

---

## 5. Pillar theorems

1. **Lattice skeleton positive** (`skeletonEnergy_nonneg`, `totalLatticeCrossingKernel_pos_iff`).
2. **Atom vs pole; the unpaid axis; nine moduli** (`totalAntiDiagonalKernel_pos_forall_iff`,
   `totalAntiDiagonalKernel_pos_imp_near_axis`, `forall_logConcave_collarAtomMass_lt_iff`).
3. **Each atom pays its own strip; odd-part payment fails at the first prime**
   (`two_mul_primePowerShift_le_stripSurplus`, `not_forall_oddPart_le_stripSurplus_logTwo`).
4. **Odd positivity past the first prime** (`fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths`).
5. **Global allocation is RH** (`fullZeroForm_eq_incidenceLedger`, `riemannHypothesis_iff_globalIncidenceAllocation`).
6. **Light cone and logarithmic capacity** (`exists_squareRoot_lightCone_allocation`, `sum_le_of_isPayableOddPartFamily`).
7. **Tower laws read the sign of $A(\log p)$** (`sub_one_mul_twistedTowerCharge_le`, `geoLagCharge_alternatingTrain_eq`).
8. **Chebyshev ledger, source rigidity, spectral symbol** (`sum_vonMangoldt_sub_polar_eq_chebyshev`,
   `eq_of_lagPrefix_eq`, `chebyshev_pairing_eq_spectral`).
9. **Reflected-prime/polar ledger at rate ½** (`fullZeroForm_eq_reflectedPrimePolarLedger`,
   `gradedIncidenceAllocation_half_seventyFive`).
10. **Bump bridge** (`tendsto_calibratedSignedJumpEnergy_latticeBumpProfile_netAtom`).
11. **Liouville selectivity from $23/40$** (`smooth_odd_selectivity_of_ge_twentyThreeFortieths`,
    `nineModulusCollar_selectivity_package`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Polar weight $\sinh\sinh$ without the 2 | Every classification changes |
| $k>0$ = positive conductance | On crossing pairs it is negative conductance |
| Thin collar everywhere | Below $s_0$ every crossing pair is negative |
| Product atom dominates on lattice pairs | Never; equality only at $a=1$ |
| Atoms flip no lattice sign | Exactly $\{2,4\},\{3,3\}$ |
| Lattice skeleton is the form | It is the $O(w)$ correction under $w\log(1/w)$ self-energy |
| Pole pays atoms near the axes | Polar weight vanishes there |
| Midpoint comparison = payment | Integrated against the gauge collar it depends on the gauge |
| Five moduli = nine | Atom alone vs atom + density |
| Summing per-strip Harnack bounds | Strips are nested; needs allocation |
| Union allocation covers thin families | Fails at $\{23,25\}$ |
| Edge-tent obstruction is a failure of the form | Only odd-part payment fails; even parts cancel |
| The ledger is a positivity theorem | It is an identity; positivity only where certificates exist |
| Exact sign is the only target | Graded by width; bounded window families report nothing |
| Tower law estimates the prime side | Envelope attained; only the fold defect is information |
| Oddness/edge decay give a power saving | Constant-factor only; rate 1 is the prime–polar balance |
| Comb-energy reduction is a bound | Premise false: raw comb energy $\sim4e^{2r}$ |
| Chebyshev ledger = full Weil energy | Archimedean density is not in it |
| Symbol criterion supplies a sign | It reduces to one function; the floor is the open problem |
| Bound $E$ by its size | $E$ is unbounded; use increments/curvature |
| Single-tower envelope bounds two aligned towers | Envelopes add on the bi-lattice train |

---

## 7. Open problems

1. **Pay the ledger at every aperture.** One budget paying every strip mass, the pole and the signed
   remainder on every odd compact test. Odd-part routes end before $\log2$; any allocation must use
   odd/even cancellation = prime–polar balance.
2. **The rate.** Deficit $Ce^{2\sigma r}\int F^2$ for one $\sigma<\tfrac12$; unconditional: rate 1 (PNT
   constants, dlVP Sobolev saving). Lower the exponent, not the constant.
3. **Signed Chebyshev pairing.** Bound $\int_0^{2r}E\,w_F$ with both sides together; spectrally a lower
   bound on `primeSymbol` $-2K_{2r}$ on frequencies an aperture-$r$ test reaches; state the norm used.
4. **Replacement after the raw comb obstruction.** Specify a coherent subtraction (translation/resolvent
   of ACT-comp) and its norm, then a Schur bound for the remainder.
5. **Tower discounts.** Turn the reduced cost side (primes vs $A(\log p)$) into a ledger lower bound;
   choose divisor-lattice weights that pay first-power charges.
6. **Signed gauges** with controlled remainder and Harnack across growing prime shifts.
7. **The five moduli.** Classify gauges whose same-side atoms pay the atoms of $\{2,3,4,5,7\}$ (never the pole).
8. **Topics.** Selectivity audit of every theorem (shifted pair, Beurling, Liouville); windows past
   $23/40$ only if they pay the pole and several strips jointly; global choice of intermediate ratio
   shifts for the continuum bridge.

---

## 8. Tools to build

A joint budget for all strips + pole + remainder; a lower bound on the signed spectral symbol; a
compensated correlation kernel with a Schur bound; a signed first-power prime–polar estimate with
half-power weights.

---

## 9. Principles

- Search first (CHMD reflected-prime singular part and divisor cuts already exist).
- Name the pair: same-side or crossing, lattice or continuum, which window.
- Separate density from atoms; pair them with a profile before comparing.
- Read pair weights off the proved decomposition $Z=J_M+V_\mu$, never off a docstring.
- Unconditional statements on honest classes; no hypothesis restating the sign.
