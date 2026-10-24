# Arithmetic Incidence Positivity (`GaloisForLFunctions.ArithmeticIncidencePositivity`)

**One question.** The zero form of `ζ` is a jump form whose conductance between two points is a
gauge factor times a kernel built from the archimedean density, the prime atoms and the pole. On
which pairs of points is that conductance negative, how large is the negative part, and what in the
arithmetic of the integers pays it?

Arithmetic incidence positivity (AIP) is a theory of *pairs*. Where the arithmetic criticality theory
treats the critical form as one quadratic functional of a profile, AIP reads it conductance by
conductance, as a weighted graph on the real line whose arithmetic edges are indexed by the
incidence relations of the integers: the pair of points `(log a, log b)` is coupled through the ratio
`b/a` when `a ∣ b`, and the pair `(−log a, log b)` through the product `ab`. The sign problem of the
critical form is the sign problem of this graph. Every statement in AIP is unconditional and names the
pairs it concerns.

---

## Place in the research

AIP resolves a global sign question into interactions of pairs, strips and prime towers. Its
central object is the exact decomposition of the odd Weil form into an archimedean surplus,
crossing potential, prime gains and costs, a gauge remainder, and the pole. A decomposition is
useful only when it identifies a resource that can pay several costs without being spent twice.

Three mechanisms give the field its shape. The ratio/product classification makes the lattice
skeleton positive. Reflection and Schur estimates pay prime atoms locally and produce window
certificates. Translate Gram identities compress whole towers to first-power correlations, after
which the unresolved arithmetic sits in cross-prime correlations and their signed balance with
the poles. Lag Abel summation expresses that balance through one two-pole Chebyshev defect.

| Programme | Connection |
|---|---|
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md) | Supplies complete source families and the Weil–Markov–pole form being decomposed. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Supplies autocorrelation constraints, blind models, and calibration of what a restricted test sees. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Studies the same distinction between finite incidence identities and uniform arithmetic payment. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Supplies valuations, divisor relations and arithmetic Gram tools for the prime side. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) | Supplies gauges, exact ground-state representations, the zero form and its criticality. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Converts growing-aperture allocation bounds into lag estimates and zero-width bounds; identifies what bounded windows cannot settle. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Asks how a local certificate could extend while retaining its exact energy budget. |
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | Tracks the signed information lost by independent positive estimates at different scales. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Proves the raw comb energy has sharp exponential growth and identifies its translation and resolvent; directs estimates back to the signed prime–polar pairing. |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Seeks an effectivity or intersection argument that forces the required sign. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Retains the source signs when passing to ratio kernels and absolute majorants. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Reads the product (sum) pairs as the only frustrating edges of the odd ledger and proves that their contribution is one square per prime tower. |
| [Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md) | Its close prime pairs `|log(n/m)| < 4b` are a height-averaged form of the prime-ratio correlations whose bounded Schur constant is the replacement hypothesis of mechanism 56. |

**The shared target.** The programmes in the table work on one object: RH as the sign of the
complete critical arithmetic form, read through pairwise incidence, lag (Square-Root Threshold) and
aperture (Arithmetic Criticality Theory). AIP owns the incidence face — conductance by conductance,
with the pole as the only positive source on crossing pairs — and reports progress in the width
unit: a ledger deficit at rate `2σ` at every aperture is the strip `½ + σ`.

Read §2 for pair and weight conventions, then the lattice classification, the odd fold, the shared
surplus, the tower calculus and the Chebyshev ledger in §3; §4 lists the pillar theorems and §§6–7
the questions and open problems. Keep three levels separate: a comparison of scalar weights,
an integrated energy inequality, and positivity for all compact tests. Only the last is the RH
criterion. `RHTower` supplies the archimedean, explicit-formula and divisor-cut analysis.

---

## 1. Why: motivation

**The zero form is a jump form.** In an odd gauge `ω`, positive on `(0, ∞)`, with test coordinate
`M = Φω` and `μ = M sinh(x/2)`, the zero form of an even profile `u` is

    Z(Φ(ωu)) = ∫_{t>0} dm(t) ∫ M(x)M(x+t)(u(x) − u(x+t))² dx + ∫∫ μ(x)μ(y)(u(x) − u(y))² dx dy,

where `dm` is the jump measure: the archimedean density `ω(t) = e^{−t/2}/(1 − e^{−2t})` on `(0, ∞)`
plus the prime atoms `Λ(n) n^{−1/2}` at `t = log n` (`ArithmeticCriticalityTheory`,
`zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy`). The first integral counts each unordered
pair `{x, y}` once, with the weight `dm(|x − y|)`; the second counts it twice, with the weight
`μ(x)μ(y)`. So the conductance of the unordered pair `{x, y}` per unit `M(x)M(y)` is the
**gauge-free kernel**

    k(x, y) = dm(|x − y|) + 2 sinh(x/2) sinh(y/2).

RH is the nonnegativity of this jump form on every even profile, in any one such gauge. (The factor
`2` on the polar term is forced by the two orders of the pair in the variance integral; a kernel
without it describes a different form.)

**Same side, across.** For `M` odd and positive on `(0, ∞)` the gauge factor `M(x)M(y)` is positive
when `x` and `y` lie on the same side of the origin and negative when they lie across it. A same-side
pair has `k > 0` (both terms positive): positive conductance. A crossing pair `x < 0 < y` has
negative conductance exactly where `k > 0`, that is where the jump measure at the distance `|x| + y`
exceeds the polar weight `2 sinh(|x|/2) sinh(y/2)`. The negative conductances of the form are
therefore confined to the crossing pairs, on the prime anti-diagonals `|x| + y = log n` (an atom of
infinite density) and on the set where the archimedean density `ω(|x| + y)` beats the polar weight.

**Incidence.** On the logarithmic lattice `{± log a}` the two kinds of pairs are arithmetic
relations. The same-side pair `(log a, log b)` carries an atom iff `b/a` is a prime power: `a` divides
`b` with prime-power quotient. The crossing pair `(−log a, log b)` carries an atom iff `ab` is a
prime power, which forces `a` and `b` to be powers of one prime. So the prime conductances of the
form are the divisibility relations of the integers read in two ways, by ratio and by product. The
field's thesis is that the sign of the critical form should be understood through this incidence
structure: which pairs of integers carry negative conductance, how it compares with the positive
conductance on the same pair, and how the window structure of the primes enters.

**Polar compensation.** The pole of `ζ` enters the form as the variance term; per unit gauge its
weight on the crossing pair `(−a, s − a)` is the **polar weight** `2 sinh(a/2) sinh((s − a)/2)
= cosh(s/2) − cosh(s/2 − a)`. It is the only positive source on crossing pairs. It pays the
archimedean crossing density `ω(s)` pointwise everywhere except on a collar of the two axes of
length `≍ 2e^{−s}`, and it vanishes at the axes, so it never pays a prime atom near the ends of its
anti-diagonal. As a scalar comparison at the midpoint, where the polar weight is largest, it dominates the atom weight `Λ(n)/√n` for every
`n ≥ 2` except `2, 3, 4, 5, 7`, and it dominates the sum of the atom weight and the sampled archimedean density for every
`n ≥ 2` except `2, 3, 4, 5, 7, 8, 9, 11, 13`.

These scalar classifications do not compare measures: a Dirac atom and a continuous density
must first be paired with a profile before an energy-payment claim is meaningful.

**Where the difficulty sits.** The pair picture separates what is already decided from what is not.
On lattice pairs the negative atom is never larger than the positive atom on the same pair, and the
negative total conductance is carried by the axis pairs and four small pairs. In the continuum the
pole pays the archimedean density off the collars. What remains is the prime atom near the axes of
its anti-diagonal, for all `n`, and along the whole anti-diagonal for the nine moduli: it must be paid
by same-side atoms at other ratios and by the gauge, with no slack to lose.

---

## 2. What: objects and language

The objects come from `RHTower` and `ArithmeticCriticalityTheory`. Do not redefine them.

| Object | Meaning | Lean |
|---|---|---|
| Archimedean density | `ω(t) = e^{−t/2}/(1 − e^{−2t})`, `t > 0` | `RHTower.archLevyDensity` |
| Prime atom | `Λ(n)/√n` at `t = log n`, `n ≥ 2` | `RHTower.vonMangoldtAtom` |
| Signed jump energy | `J_M(u) = ∫_{t>0} dm(t) ∫ M(x)M(x+t)(u(x) − u(x+t))²` | `ArithmeticCriticalityTheory.signedJumpEnergy` |
| Variance energy | `∫∫ (u(x) − u(y))² μ(x)μ(y)`, all ordered pairs | `ArithmeticCriticalityTheory.varianceEnergy` |
| Archimedean pair kernel | `k_arch(x,y) = ω(\|x−y\|) + 2 sinh(x/2) sinh(y/2)` | `archPairKernel` |
| Crossing symbol | `S(s) = cosh(s/2) − ω(s)` | `crossingSymbol` |
| Crossing threshold | the unique root `s₀ ∈ (log 5, log 6)` of `S = 1` | `crossingThreshold` |
| Ratio atom | `Λ(b/a)/√(b/a)` on the same-side pair `(log a, log b)`, `a ∣ b` | `ratioAtom` |
| Product atom | `Λ(ab)/√(ab)` on the crossing pair `(−log a, log b)` | `productAtom` |
| Net atom | `ratioAtom − productAtom` | `netAtom` |
| Lattice skeleton energies | `Σ_{a<b} (·)(c a − c b)²` with ratio, product or net atoms | `ratioEnergy`, `productEnergy`, `skeletonEnergy` |
| Dyadic window | `(X/2, 2X)` as a predicate on integers | `InDyadicWindow` |
| Two-bump window | `\|log n − v\| ≤ 2w` | `SquareRootThreshold.lagPrimeWindow` |
| Polar weight | `P_s(a) = 2 sinh(a/2) sinh((s−a)/2)` on the crossing pair `(−a, s−a)` | `crossingPolarWeight` |
| Off-collar region | crossing pairs with `k_arch ≤ 0` | `offCollar` |
| Collar of an anti-diagonal | `{a ∈ (0,s) : k_arch(−a, s−a) > 0}` | `antiDiagonalCollar` |
| Collar ends | `ℓ(s) = ω(s)/sinh(s/2)`, `L(s) = ω(s)/sinh(s/2 − 3e^{−3s/4})` | `collarInnerEnd`, `collarOuterEnd` |
| Payment scale | `Λ(n)/√n` over `2 sinh²(log n / 4)` | `polarPaymentScale` |
| Five moduli | `{2, 3, 4, 5, 7}` | `atomDominatedModuli` |
| Total lattice crossing kernel | `k_arch(−log a, log b) + Λ(ab)/√(ab)` | `totalLatticeCrossingKernel` |
| Total anti-diagonal kernel | `ω(log n) + Λ(n)/√n − P(a)` on the anti-diagonal of `n` | `totalAntiDiagonalKernel` |
| Nine moduli | `{2, 3, 4, 5, 7, 8, 9, 11, 13}` | `totalDominatedModuli` |
| Unpaid set of a level | `{a ∈ (0,s) : P_s(a) < E}` | `unpaidSet` |
| Level of `n` | `E_n = ω(log n) + Λ(n)/√n` | `antiDiagonalLevel` |
| Unpaid ends | `ℓ = E/sinh(s/2)`, `L = E/sinh(s/2 − min(s/4, E/sinh(s/4)))` | `unpaidInnerEnd`, `unpaidOuterEnd` |
| Box energy of a strip | `T(p, r) = ∫_p^r ∫_p^r k(x, y)(F x − F y)²`, both orders | `stripBoxEnergy` |
| Shell integrand | the strip integrand with the inner box `(p', ∞)²` removed | `shellIntegrand` |
| Strip and shell constants | `λ₀ = 1.9 − η/p − 3η²`; `λ₀ − (r − p')((2 + η/2)/c + 1)` | `stripFoldConstant`, `shellFoldConstant` |
| Prime strip charge | `2Λ(n)/√n ∫ F F(· + log n) + 2(Λ(n)/√n) t ∫_{S_n} F²` | `primeStripCharge` |
| Light-cone band | `2r − 2δ ≤ log n < 2r` | `lightConeBand` |
| Thin band | `2r − 1/6 ≤ log n ≤ 2r − 1/24` | `thinBand` |
| Edge tent | `max(ε/2 − abs(x − (r − ε/2)), 0)` and its odd extension | `edgeTent`, `edgeTentOdd` |
| Prime side and strip mass | `n ≤ e^{2r}`; `m_n(F) = ∫_{log n − r}^{r} F²` (crossing strip) or `∫ F²` | `primeSide`, `atomStripMass` |
| Crossing potential of a gauge | `Π_P(x) = ∫_{t>x} ω(t) P(t − x) dt`; collar part `∫_{t>x+r} ω(t) P(t − x) dt` | `crossingPotential`, `collarCrossingPotential` |
| Relevant shifts | `n ≥ 2`, `log n < 2r` | `relevantShifts` |
| Odd strip cost, even strip gain | `4Λ(n)/√n ∫_{S_n} α_n²`, `2Λ(n)/√n ∫_{S_n} F²` | `oddStripCost`, `evenStripGain` |
| Surplus pool, crossing potential term | `2 S_P(F)`, `4 ∫_{x>0} F² Π_P` | `surplusPool`, `crossingPotentialTerm` |
| Gauge remainder, pole charge | `∫ F² P (−𝒲P + prime part)`, `2 (∫ F sinh(x/2))²` | `gaugeRemainder`, `poleCharge` |
| Plateau of an aperture | `1` on `[−r, r]`, `0` outside `(−R, R)` | `aperturePlateau` |
| Global incidence allocation | costs + pole ≤ pool + crossing potential + gains + remainder | `GlobalIncidenceAllocation` |
| Reflected-prime/polar cost | `Σ_n oddStripCost_n − Σ_n evenStripGain_n + poleCharge` | `reflectedPrimePolarCost` |
| Pairing, autocorrelation | `⟪A, B⟫ = ∫AB`; `A(t) = ⟪F, F(· + t)⟫` | `testPairing`, `autoCorr` |
| Translate combination | `Σ_k α_k F(· + c_k)`, over a range or a finite index set | `translateComb`, `finsetComb` |
| Geometric train | `S_N = Σ_{k ≤ N} z^k F(· + kL)`, `S_N − zS_N(· + L) = F − z^{N+1}F(· + (N+1)L)` | `geoTrain`, `geoTrain_resolvent` |
| Tower lag charge | `C_p(F) = log p Σ_{k ≥ 1} p^{−k/2} A(k log p)` | `PrimeTowerEulerEnvelope` |
| Euler envelope, fold defect | `z/(1−z)·A(0)`; `A(0) − A(L)` | `PrimeTowerEulerEnvelope` |
| Train lag charge | `A_G(s) = Σ_{j,k ≤ N} w^{j+k} A(s + (k − j)b)` | `BiTowerIncidenceLaw` |
| Divisor-lattice comb | `Σ_{d ∣ q} c_d F(· + log d)` and its Gram `Σ_{d,e ∣ q} c_d c_e A(log e − log d)` | `DivisorLatticeGramPositivity` |
| Squarefree subset form | `Σ_{S ⊆ s} (−1)^{#S}(Π_{i ∈ S} λ_i) F(· + Σ_{i ∈ S} a_i)` | `SquarefreeIncidencePositivity` |

**Words.**
* **Pair `(x, y)`:** two points of the real line; **same-side** if `xy > 0`, **crossing** if
  `x < 0 < y`. For a crossing pair, `s = |x| + y` is the **sum** (the jump length) and `e = x + y`
  the **imbalance**; the pair is **balanced** when `e = 0`.
* **Conductance:** `M(x)M(y)k(x,y)` of the unordered pair; **negative conductance** on a crossing
  pair means `k(x,y) > 0`.
* **Lattice pair:** both points in `{± log a : a ≥ 1}`. The lattice pair `(log a, log b)` is a
  **ratio pair** when `a ∣ b`; `(−log a, log b)` is a **product pair** when `ab` is a prime power.
* **Tower:** the set `{p^i : i ≥ 0}` of powers of one prime. Product pairs live inside towers, and
  the tower's whole prime charge is one geometric lag charge.
* **Lag charge:** a weighted sum of the autocorrelation at a progression of lags. The prime side is
  the sum of the tower lag charges; the translate calculus bounds each by its first-power datum.
* **Resonant direction:** a test whose autocorrelation is maximal at every lag used, realised by a
  train of disjoint copies of one bump at that spacing. Envelopes are attained there, so a bound
  that a resonant train meets with equality carries no information beyond the Euler constants.
* **Anti-diagonal of `n`:** the segment `{(x, y) : x < 0 < y, |x| + y = log n}` on which the prime
  atom of `n` sits; its lattice points are the factorizations `n = ab`.
* **Collar:** the set of crossing pairs with negative archimedean conductance; beyond the threshold
  it is a thin neighbourhood of the two axes.
* **Window:** a dyadic range of integers `(X/2, 2X)`; **window incidence** is the set of ratio and
  product pairs with both members in the window.
* **Polar weight** of a crossing pair: the variance conductance per unit gauge,
  `2 sinh(|x|/2) sinh(y/2)`. **Payment** means that the polar weight on a pair is at least the
  negative conductance on it; the **payment scale** of `n` is the ratio of the atom to the largest
  polar weight on its anti-diagonal.

---

## 3. How: mechanisms

### The archimedean kernel

1. **Product-to-sum.** `2 sinh(x/2) sinh(y/2) = cosh((x+y)/2) − cosh((x−y)/2)`, so for `x < y`
   `k_arch(x,y) = ω(y−x) + cosh((x+y)/2) − cosh((y−x)/2)` (`archPairKernel_eq_of_lt`). On same-side
   pairs both terms of `k_arch` are positive (`archPairKernel_pos_of_sameSide`).
2. **Sign law.** For `x < y`, `k_arch(x,y) > 0 ⟺ cosh((x+y)/2) > S(y−x)` (`archPairKernel_pos_iff`).
   A crossing pair has negative conductance iff its imbalance is large enough for its sum: the
   symbol `S(s) = cosh(s/2) − ω(s)` is the balanced value of the kernel-defining threshold.
3. **The symbol is monotone and crosses `1` once.** `S` is strictly increasing on `(0, ∞)`
   (`cosh(s/2)` grows, `ω` decays), `S(log n) = (n+1)/(2√n) − n²/((n²−1)√n)`
   (`crossingSymbol_log_nat`), `S(log 5) < 1 < S(log 6)`, so `S` has a unique root `s₀`, the crossing
   threshold (`crossingThreshold_mem`, `crossingSymbol_crossingThreshold`). Since `cosh ≥ 1`: every
   crossing pair with sum below `s₀` has negative conductance (`archPairKernel_pos_of_lt_threshold`);
   at the threshold exactly the balanced pair is neutral (`archPairKernel_pos_iff_of_eq_threshold`);
   beyond it balanced pairs have positive conductance (`archPairKernel_balanced_neg_iff`) and only
   the unbalanced ones, close to an axis, remain negative.
4. **Collar bound.** For `s ≥ 4 log 2` a negative crossing pair has `min(|x|, y) < 3 e^{−3s/4}`
   (`min_lt_of_archPairKernel_pos`). Two estimates: near an axis,
   `c sinh(s/4) ≤ cosh(s/2) − cosh(s/2 − c) < ω(s)` with `c = min(|x|,y)`; for a balanced-type pair,
   `cosh(s/2) − cosh(s/4) ≥ 3s²/32` beats `ω(s) ≤ 64/255`.

### The lattice

5. **Reflection law.** The reflected lattice pair `(−log a, log a)` has sum `2 log a` and imbalance
   `0`; it has negative archimedean conductance iff `2 log a < s₀`, that is iff `a = 2`
   (`archPairKernel_reflection_pos_iff`; `log 4 < log 5 < s₀ < log 6 < log 9`).
6. **Closed form on lattice crossing pairs.**
   `k_arch(−log a, log b) = (2(ab)² − (a−1)(b−1)((ab)²−1)) / (2√(ab)((ab)²−1))`
   (`archPairKernel_neg_log_log`), so the conductance is negative iff
   `(a−1)(b−1)((ab)²−1) < 2(ab)²` (`archPairKernel_neg_log_log_pos_iff`). The axis pairs `a = 1` or
   `b = 1` always qualify; for `a, b ≥ 2` exactly the two pairs `{2,2}` (`15 < 32`) and `{2,3}`
   (`70 < 72`) do (`archPairKernel_neg_log_log_pos_iff_of_two_le`); from `(a−1)(b−1) ≥ 3` on the
   kernel is negative (`archPairKernel_neg_log_log_neg_of_three_le`).
7. **Tower lemma.** If `ab` is a prime power, `a = p^i` and `b = p^j` for one prime `p`
   (`exists_prime_pow_of_isPrimePow_mul`); then `b/a = p^{j−i}` is a prime power as well, and
   `Λ(ab) = Λ(b/a) = log p`.
8. **Dominance law.** For `1 ≤ a < b`, `productAtom a b ≤ ratioAtom a b`
   (`productAtom_le_ratioAtom`): the crossing atom of a lattice pair is never larger than the
   same-side atom of the same pair, because `√(ab) ≥ √(b/a)`. Strict for `a ≥ 2` and `ab` a prime
   power (`productAtom_lt_ratioAtom`); equality at `a = 1` (`productAtom_one_left`). Hence the prime
   skeleton `Σ_{a<b} netAtom(a,b)(c a − c b)²` of a lattice profile is a nonnegative graph Laplacian
   (`skeletonEnergy_nonneg`), and a profile constant along each tower has no crossing energy at all
   (`productEnergy_eq_zero_of_tower_constant`).

### Windows

9. **Window divisibility.** Two integers of one dyadic window have ratio below `4`, so a divisor
   relation inside the window is a doubling or a tripling (`eq_two_mul_or_three_mul_of_dvd`); the
   same-side atoms inside a window are `Λ(2)/√2` and `Λ(3)/√3` only (`ratioAtom_inDyadicWindow`).
10. **Window towers.** Two powers of one prime in a common window have consecutive exponents; a
    prime `p ≥ 5` has at most one power per window (`exponent_sub_le_one_of_inDyadicWindow`,
    `exponent_eq_of_inDyadicWindow_of_five_le`). A product pair inside a window is `(p^i, p^{i+1})`
    with `p ∈ {2, 3}` (`consecutive_powers_of_isPrimePow_mul`), and its atom is below
    `2 log 3 / X` (`productAtom_lt_of_inDyadicWindow`).
11. **Two-bump windows.** The window `|log n − v| ≤ 2w`, `2w < log 2`, of a two-bump test lies in
    the dyadic window at scale `e^v` (`inDyadicWindow_of_mem_lagPrimeWindow`), so its internal
    incidence obeys 9 and 10 (`eq_two_mul_or_three_mul_of_mem_lagPrimeWindow`,
    `productAtom_lt_of_mem_lagPrimeWindow`).

### The continuum: polar compensation

12. **Anti-diagonal decomposition.** On the anti-diagonal of sum `s > 0`, written `(−a, s − a)`,
    `k_arch = ω(s) − P_s(a)` with the polar weight `P_s(a) = 2 sinh(a/2) sinh((s−a)/2)
    = cosh(s/2) − cosh(s/2 − a)` (`archPairKernel_antiDiagonal_eq`, `crossingPolarWeight_eq`).
    `P_s` is symmetric under `a ↦ s − a`, vanishes at both ends, increases from the axis to the
    midpoint (`crossingPolarWeight_mono`), and has its maximum `cosh(s/2) − 1 = 2 sinh²(s/4)` there
    (`crossingPolarWeight_midpoint`, `crossingPolarWeight_le_midpoint`).
13. **Pointwise payment off the collar.** Where `k_arch(x, y) ≤ 0` on a crossing pair,
    `ω(y − x) ≤ 2 sinh(|x|/2) sinh(y/2)`; in a gauge with `M(x)M(y) ≤ 0` across the origin the
    archimedean crossing conductance is at most the variance conductance of the unordered pair,
    hence for every profile the archimedean crossing energy over the off-collar region is at most the
    variance energy over it (`lintegral_archCrossingDensity_offCollar_le`). The archimedean
    negativity that survives the pole lives on the collar.
14. **Collar measure.** For `s ≥ 4 log 2` the collar of the anti-diagonal lies within `3 e^{−3s/4}`
    of its two ends (`antiDiagonalCollar_subset`); its length is at most `6 e^{−3s/4}`
    (`volume_antiDiagonalCollar_le`), and the archimedean conductance the pole leaves unpaid on the
    anti-diagonal has total mass at most `6 ω(s) e^{−3s/4}` (`lintegral_antiDiagonalCollar_le`).
15. **Small and large anti-diagonals.** For `2 ≤ n ≤ 5` the whole anti-diagonal `|x| + y = log n`
    has negative archimedean conductance, because `log 5 < s₀`
    (`archPairKernel_antiDiagonal_pos_of_le_five`); for `n ≥ 16` only the end collars of length
    `< 3 n^{−3/4}` do (`antiDiagonal_collar_of_sixteen_le`).
16. **Axis law.** The polar weight tends to `0` at the ends of every anti-diagonal
    (`tendsto_crossingPolarWeight_zero`): no pole mass is available against a prime atom near the
    axes.
17. **Payment scale.** The ratio of the atom to the midpoint polar weight is
    `2Λ(n)/(√n − 1)²` (`polarPaymentScale_eq`), at most `8 log n / n` for `n ≥ 4`
    (`polarPaymentScale_le`).
18. **Exact classification, atom alone.** `(√n − 1)² < 2Λ(n)` iff `n ∈ {2, 3, 4, 5, 7}`
    (`sqrt_sub_one_sq_lt_two_vonMangoldt_iff`): the primes up to `7` and the square `4`. For these the
    atom exceeds the polar weight at every point of the anti-diagonal
    (`crossingPolarWeight_lt_vonMangoldtAtom`, `antiDiagonal_total_pos_of_mem`); for every other
    `n ≥ 2` the pole pays the atom at the midpoint (`vonMangoldtAtom_le_crossingPolarWeight_midpoint`).
    Inputs: `Λ(p^k) = log p`; `log r ≤ sinh(log r)` on fourth roots for `p ≥ 11`
    (`two_mul_log_le_sqrt_sub_one_sq`); `log p ≤ p − 1` for `k ≥ 2`; four explicit comparisons.
19. **Collar sandwich.** From `a sinh(s/2 − a) ≤ P_s(a) ≤ a sinh(s/2)` on `0 ≤ a ≤ s/2`
    (`le_crossingPolarWeight`, `crossingPolarWeight_le`; the upper bound is
    `sinh a − a ≤ cosh a − 1`): for `s ≥ 4 log 2`,
    `(0, ℓ) ∪ (s − ℓ, s) ⊆ collar ⊆ (0, L) ∪ (s − L, s)` (`innerEnds_subset_antiDiagonalCollar`,
    `antiDiagonalCollar_subset_outer`), with `ℓ(s) = 2e^{−s}/((1 − e^{−2s})(1 − e^{−s}))`
    (`collarInnerEnd_eq`), `2e^{−s} ≤ ℓ(s) ≤ (256/239) · 2e^{−s}`, and
    `L = ℓ · sinh(s/2)/sinh(s/2 − 3e^{−3s/4})` (`collarOuterEnd_eq`). The collar has exact order
    `2e^{−s}` at each axis; the unpaid archimedean mass is at most `2ω(s)L(s)`
    (`lintegral_antiDiagonalCollar_le_outer`), of order `4e^{−3s/2}`.

**Sharp collar geometry.** For `s ≥ 4 log 2` the collar is exactly `(0, c) ∪ (s − c, s)` with
   `P_s(c) = ω(s)`, `ℓ ≤ c ≤ 2ℓ` and `|c − ℓ − (coth(s/2)/2)ℓ²| ≤ 8ℓ³` (`collarEnd_second_order`);
   the second-order coefficient is exact, `(coth(s/2)/2)ℓ(s) = e^{−s}/(1 − e^{−s})³`
   (`half_coth_mul_collarInnerEnd`), so `|c/ℓ − 1 − e^{−s}/(1 − e^{−s})³| ≤ 37e^{−2s}` and
   `c(s)/ℓ(s) = 1 + e^{−s} + O(e^{−2s})` (`collarEnd_ratio`).

20. **Exact classification, atom plus density.** On the anti-diagonal of `n` the total kernel
    `ω(log n) + Λ(n)/√n − P(a)`, with `ω(log n) = n²/((n² − 1)√n)` (`archLevyDensity_log_nat`), is
    smallest at the midpoint, where it equals `(2n²/(n² − 1) + 2Λ(n) − (√n − 1)²)/(2√n)`
    (`totalAntiDiagonalKernel_midpoint_eq`). It is positive everywhere iff
    `(√n − 1)² < 2n²/(n² − 1) + 2Λ(n)`, and for `n ≥ 2` this holds iff
    `n ∈ {2, 3, 4, 5, 7, 8, 9, 11, 13}` (`total_midpoint_inequality_iff`,
    `totalAntiDiagonalKernel_pos_forall_iff`). For all other `n` the pole pays the whole negative
    conductance at the midpoint (`totalAntiDiagonalKernel_midpoint_nonpos`): `6` is the first such
    modulus and `17` the first such prime; the near misses are `8` (`3.344` against `3.418`) and `9`
    (`4` against `4.07`); from `17` on, `2x²/(x² − 1) + 2 log x ≤ (√x − 1)²`
    (`two_sq_div_add_two_log_le`, through `log r ≤ sinh(log r)` on the fourth root).
21. **Unpaid axis intervals.** The unpaid set of a level `E` is two axis intervals once the quarter
    point is paid, and the bounds of mechanism 19 sandwich its ends:
    `(0, ℓ) ∪ (s − ℓ, s) ⊆ unpaid ⊆ (0, L) ∪ (s − L, s)` with `ℓ = E/sinh(s/2)` and
    `L = E/sinh(s/2 − min(s/4, E/sinh(s/4)))` (`innerEnds_subset_unpaidSet`,
    `unpaidSet_subset_outer`, ratio `unpaidOuterEnd_eq`). For the full level
    `E_n = ω(log n) + Λ(n)/√n` of the anti-diagonal of `n`, the inner end is
    `ℓ_n = 2(n²/(n² − 1) + Λ(n))/(n − 1)` (`unpaidInnerEnd_level_eq`), between `2/(n − 1)` and
    `2(1 + 1/(n² − 1) + log n)/(n − 1)`, and the quarter point is paid for every `n ≥ 23`
    (`antiDiagonalLevel_le_quarter`, by the fourth-root bound and the polynomial
    `2.004r + 4(r² − 1) ≤ r⁵ − r⁴ − r² + r` for `r ≥ 2.189`). Hence for `n ≥ 23` the pole pays the
    whole negative conductance of the anti-diagonal of `n` except on two axis intervals of length
    between `ℓ_n` and `L_n` (`unpaid_level_subset_outer`, `totalAntiDiagonalKernel_pos_imp_near_axis`):
    the prime obstruction on the anti-diagonal of `n` is confined to a neighbourhood of the axes of
    exact order `2(1 + Λ(n))/n`. The quarter point itself is classified: with `r = n^{1/4}` it is paid
    iff `n²/(n² − 1) + Λ(n) ≤ (n + 1 − r³ − r)/2`, that is exactly for `n ∈ {10, 12}` and `n ≥ 14`,
    `n ≠ 17` (`antiDiagonalLevel_le_quarter_iff_mem`). Once the midpoint is paid the unpaid set is
    `(0, c) ∪ (s − c, s)` with `P_s(c) = E` (`unpaidSet_eq_of_le_midpoint`), and the midpoint is paid
    while the quarter point is not exactly for `n ∈ {6, 17}`, where `s/4 < c ≤ s/2`
    (`unpaidSet_level_eq_of_quarter_unpaid`).

### The lattice with its atoms

22. **Total lattice crossing law.** For `a, b ≥ 2` the total crossing kernel
    `k_arch(−log a, log b) + Λ(ab)/√(ab)` is positive exactly on the four unordered pairs
    `{2,2}, {2,3}, {2,4}, {3,3}` (`totalLatticeCrossingKernel_pos_iff`). The archimedean kernel alone
    is positive on `{2,2}` and `{2,3}`; the prime atom flips exactly two further pairs, `{2,4}`
    (`126 log 2 > 61`, `totalLatticeCrossingKernel_two_four_pos`) and `{3,3}` (`160 log 3 > 158`,
    `totalLatticeCrossingKernel_three_three_pos`), and no other
    (`totalLatticeCrossingKernel_pos_iff_archPairKernel_pos_or`). In closed form the condition is
    `(a−1)(b−1)(N²−1) < 2N² + 2Λ(N)(N²−1)`, `N = ab`
    (`totalLatticeCrossingKernel_pow_pow_eq`); outside the four pairs the three tower regimes are
    `p = 2` with `(a−1)(b−1) ≥ 7`, `N ≥ 16`, `p = 3` with `(a−1)(b−1) ≥ 16`, `N ≥ 27`, and `p ≥ 5`
    with `(a−1)(b−1) ≥ (p−1)²`, `N ≥ 25` (`lattice_atom_inequality`).

### The fold of the odd sector

23. **Folded odd plateau.** For an odd test `F` in an even gauge `P` (equivalently an even profile in
    the odd gauge `sign(x) P(x)`), the crossing pair `(−a, b)` and the same-side pair `(a, b)` carry
    `(F(a) + F(b))²` and `(F(a) − F(b))²` at the rates `ω(a + b) ≤ ω(|a − b|)`, so their sum is at least
    `2ω(a + b)(F(a)² + F(b)²)`: every archimedean crossing conductance is paid by its same-side partner
    and leaves a killing. Integrated (`fourKilling_le_archJump`, via the Z-type law
    `archCrossingDiff_le_two_mul_archSame` in test coordinates),
    `J_P(F) ≥ 4 ∫_{x>0} F(x)² (Ω(x) − Ω(x + r))` when `P = 1` on `[−r, r] ⊇ supp F`, with
    `Ω(y) = ∫_y^∞ ω` (`archLevyAntideriv`). The plateau potential is exact through the edge function
    `E = Ω − N` (`integral_one_sided_window_eq`): `−𝒲P(x) ≥ Ω(R − x) + Ω(R + x) − log 8 − π/2 − (γ + log π)`.
    The pole is not converted, so the plastic threshold plays no role; the odd pole costs
    `(R³/3) cosh²(R/2) ∫F²`. The total potential is `−log 2 − ½ log((R² − x²)x²/(x + r)²) − O(r²) − (γ + log π)`,
    worst at the golden point `x = R/φ`, where `(R − x)x² ≤ R²(R + x)/11`; it is positive up to
    `R ≈ 0.297`. Every odd `F` supported in `[−7/25, 7/25]` has `Ẑ(F) ≥ (1/40) ∫ F²`
    (`fullZeroForm_ge_of_odd_support_le`), that is `J_M(u) + V_μ(u) ≥ 0` for every even profile
    with `M u` supported there, in every odd gauge.
24. **Selectivity past the plastic threshold.** The zero form of `ζ(s − a) ζ(s + a)` is
    `Ẑ_a(F) = 2(Ẑ(F cosh(a·)) − Ẑ(F sinh(a·)))` (`shiftedPairZeroForm`; on autocorrelations the shift acts
    by `cosh(a·)`, `autoCorr_cosh_sub_autoCorr_sinh`). On supports shorter than `log 2`,
    `Ẑ_a(F) = 2Ẑ(F) + 4 ∫_0^∞ (cosh(at) − 1)(2cosh(t/2) − ω(t)) A_F(t) dt` (`shiftedPairZeroForm_eq`): the
    product system adds the screw kernel weighted by `cosh(at) − 1`. Two opposite bumps separated beyond
    `t_* = log ρ` make it negative for all large `a` (`exists_odd_shiftedPairZeroForm_neg`), so on every
    window `t_*/2 < r ≤ 7/25` the odd form of `ζ` is coercive while that of the shifted pair is not
    (`odd_window_selective`): odd-window positivity past `t_*/2` sees the position of the zeros.
25. **The infinite-shift Hankel limit.** For `H` supported in `[y₀, r]`, `y₀ > 0`, the odd test
    `F_a = G_a − G_a(−·)`, `G_a = e^{−ay} H`, splits the shifted-pair form into
    `2Ẑ(F_a) + 8∫(cosh(at) − 1)κ A_{G_a} + 2∫(1 − e^{−at})² f (H ∗ H)` with `f = ω − 2cosh(t/2)`
    (`shiftedPairZeroForm_oddReweightedHankel`); the reflection turns the crossing autocorrelation into the
    self-convolution `e^{−at}(H ∗ H)`, and `(cosh u − 1)e^{−u} = (1 − e^{−u})²/2`. The first two terms are
    `O(a² e^{−2ay₀})`, so as `a → ∞` the form tends to the Hankel form `2∫∫ f(y + z) H(y) H(z)`. Near `0`,
    `f ≈ 1/(2t)` is Hilbert-like, but `f` is not log-convex on `[0.12, 0.20]` (`screwWeight_values`), so the
    two-bump `H = φ_{0.06} − (93/50) φ_{0.10}` makes the Hankel form negative
    (`integral_weighted_hankelProfile_le`). Hence the shifted pair fails on odd tests supported in
    `[−13/125, 13/125]` for every large `a` (`exists_odd_shiftedPairZeroForm_neg_below_markovWindow`), while
    `ζ` is coercive on `[−21/200, 21/200]` (`markovWindow_selective`): positivity at the Markov window is
    already selective, well below `t_*/2`.
26. **The curved fold.** The fold of mechanism 23 is exact: `J_P(F)` is the killing plus twice the
    surplus `S_P(F) = ∫_{x>0}∫_{s>0} (ω(s) − ω(s + 2x)) P(x)P(x+s)(F(x) − F(x+s))²`
    (`two_mul_archSame_sub_archCrossingDiff_eq`): each same-side pair keeps the excess
    `k(x, y) = ω(|x − y|) − ω(x + y)` of its rate over its crossing partner. Pairwise
    `(a − b)² ≥ a²(1 − q/p) + b²(1 − p/q)`, so for any gauge `h > 0` on `[0, r]`
    `S_P(F) ≥ ∫ F² U_h`, `U_h(x) = ∫_0^r k(x, y)(1 − h(y)/h(x)) dy` (`surplusEnergy_ge_potential`).
    For a cubic gauge `U_h` is explicit: `ω = 1/(2t) + ρ` with `1/4 − t/16 − t²/32 ≤ ρ ≤ 1/4`, and
    `∫_0^r k₀(x, y)(h(x) − h(y)) dy = a₁x(1 − ℓ) + a₂(3x²/2 − rx) + a₃(11x³/6 − r²x/2 − x³ℓ)`,
    `ℓ = log((x + r)/x)` (`integral_principalSurplus_cubicGauge`): only the odd part of `h` meets the
    reflected pole. The gauge `h = 1/500 + (3/5)y − y² − (6/5)y³` peaks near the golden point and
    lifts the potential there by `≈ 0.2`; after multiplying by `h`, the two logarithms `ℓ` of the
    killing and of `U_h` merge into the single coefficient `1/500 − x²` (the even part of `h`). Every
    odd `F` supported in `[−17/50, 17/50]` has `Ẑ(F) ≥ (1/100)∫F²`
    (`fullZeroForm_ge_of_odd_support_le_curved`): the variation inequality for all even profiles
    reaches `0.98 · log 2/2`. In the small-window scaling the odd sector is governed by the second
    eigenvalue of the logarithmic Laplacian on an interval; the flat fold captures `−γ + (5/2) log φ`
    of it, the cubic gauge most of the remaining gap.
27. **The first prime window.** For a plateau with `2R < log 3` only the prime `2` acts
    (`signedJumpEnergy_eq_arch_add_two`, `profilePrimeSum_eq_two`), and on a test with `P = 1` on its
    support the prime jump minus the prime potential is the autocorrelation
    `−2 ∫ F(x)F(x + log 2)` (`gaugeJumpProfile_sub_primePotential_eq`). For odd `F` on `[−r, r]` the
    product lives on the crossing pairs `(−a, log 2 − a)` of the edge strip `S = [log 2 − r, r]` and
    `∫ F(x)F(x + log 2) ≤ ∫_S F²` (`integral_mul_shift_le_strip`): the atom `Λ(2)/√2 ≤ 0.4902` is a
    charge per unit of mass on `S` only, where the plateau potential `−½ log(R² − x²)` is large. With
    a flatter quartic gauge (`QuarticGaugeSurplusPotential`, `quarticSurplusMain`: the `y⁴` term is
    even and never meets the reflected pole) the potential exceeds `489/20000` on `(0, 347/1000]` and
    `489/20000 + 0.4902` on `[0.346, 0.347] ⊇ S`. Every odd `F` supported in `[−347/1000, 347/1000]`
    has `Ẑ(F) ≥ (1/100)∫F²` (`fullZeroForm_ge_of_odd_support_le_pastFirstPrime`): the variation
    inequality for all even profiles holds past `½ log 2`, with the atom paid on the first prime window
    and no pole-free margin. The crossing of `½ log 2` costs nothing at the prime: the binding
    constraint stays the archimedean middle of the window.

28. **The micro-fold: the first prime atom is dominated.** On the edge strip `S` split `F` into its
    even and odd parts about `½ log 2`: `F(a)F(log 2 − a) = F_e(a)² − α(a)²`, so the atom costs only
    `α²`. For four points `x, log 2 − x, y, log 2 − y` of `S` the even parts drop out of the four
    surplus terms (`microFold_quadruple_ge`), and integrating over `S × S`
    (`microFold_strip_ge`) gives the Harnack inequality across the prime shift

        ∫_S ∫_S k(x, y)(F x − F y)² ≥ (2K + 2η k₀(2η)) ∫_S α²,   η = r − ½ log 2,

    with `K = Ω(η) − Ω(2η) − η ω(2(log 2 − r))`. As `η → 0` the constant tends to `log 2 + ½`, above
    `2Λ(2)/√2 = √2 log 2`, and it stays above `0.9804` up to `r = 2/5` (`microFoldConstant_ge`). Hence
    `2Λ(2)/√2 ∫ F(x)F(x + log 2) ≤ ∫_S ∫_S k(F x − F y)²` for every odd `F` on `[−r, r]`,
    `r ≤ 2/5` (`two_mul_primeShift_le_stripSurplus`). With the `S × S` pairs kept exact in the
    ground-state transform (`surplusEnergy_ge_potentialOff_add_strip`), the first prime window becomes
    atom-free (`fourKilling_add_potentialOff_le_archJump_sub_prime`): up to `2/5` positivity of the
    variation inequality is a purely archimedean potential bound for `U_h^{off}`, with no strip charge.
    The reason is local: across the reflection about `½ log 2` the archimedean jump rate
    `ω(t) ≈ 1/(2t)` dominates the atom; the constant `log 2 + ½` of this mechanism is not sharp
    (mechanism 30).

29. **The window `7/20` without a strip charge.** Off `S × S` the ground-state transform keeps every
    pair; on `S` the removed pairs cost `h(x)(U_h − U_h^{off})(x) = ∫_S k(x, y)(h(x) − h(y)) dy ≤
    L|S|(½ + |S|/4)` (`mul_surplusPotential_le_off_add`), since `k(x, y)|x − y| ≤ ½ + |x − y|/4`. At
    `r = 7/20`, `|S| = 0.7 − log 2 < 0.00686`, the charge is `0.0023` per unit of gauge instead of
    `Λ(2)/√2 · h ≈ 0.49 h`. With `R = 701/2000` and the gauge
    `1/500 + (3/5)y − y² − (3/10)y³ − (49/20)y⁴` the numerator exceeds `0` on `(0, 7/20]` and `0.0023`
    on `[0.343, 0.35]` (`atomFreeNumerator_nonneg`, `atomFreeNumerator_strip`; margins `≈ 0.001` in the
    middle, `≥ 0.0074` on the strip). Every odd `F` supported in `[−7/20, 7/20]` has
    `Ẑ(F) ≥ (1/200)∫F²` (`fullZeroForm_ge_of_odd_support_le_sevenTwentieths`). The strip is now cheap;
    the binding constraint is the middle of the window, where the margin is that of the gauge.

30. **The sharp micro-fold: every prime-power atom is dominated.** Folding the odd part `α` about
    `m = L/2` onto `[m, r]` turns the four pairs `x, L − x, y, L − y` into a same-side pair at
    distance `|u − v|` and a crossing pair at distance `u + v`; their sum is
    `2k(u, v)(a − b)² + 4k₀(u + v)(a² + b²)`, `k` the surplus kernel. Mechanism 28 dropped the surplus
    term; keeping it and transforming it in the gauge `η/10 + t` (`sharpQuadruple_ge`) gives the
    potential `2U_g + 4K ≥ 1.9 − η/p − 3η²` (`sharpFold_potential_ge`), hence
    `∫_S ∫_S k(F x − F y)² ≥ (1.9 − η/p − 3η²) ∫_S α²` (`sharpMicroFold_strip_ge`). In the scaling limit
    the strip problem is the regional logarithmic kernel `1/(2|s − t|)` on `[−1, 1]`, whose odd ground
    state is exactly linear, `∫_{−1}^{1} sign(s − t) dt = 2s`: the gauge `t` gives `U = 1 − ℓ`,
    `4K = 2ℓ`, and the logarithms cancel to the eigenvalue `2`. Since `Λ(n)/√n ≤ log n/√n ≤ 2/e < 0.736`
    (`vonMangoldtAtom_le`) and `2 · 0.736 < 1.56`, **every** prime-power atom is paid by the
    archimedean surplus of its own reflection strip `[log n − r, r]`, for all windows
    `½ log n < r ≤ ½ log n + 1/12` (`two_mul_primePowerShift_le_stripSurplus`): a Harnack inequality
    across every prime shift with explicit constant. The atoms never win locally; positivity can only
    fail through the interaction of several strips or through the ground-state gradient at the edge.

31. **The strip shared: window `353/1000`.** Past `7/20` the binding point is the inner edge
    `p = log 2 − r` of the strip: the `S × S` pairs that pay the atom are missing from the
    ground-state potential at `p`, a loss `≈ |h'(p)| |S|/2` per unit of gauge. The sharp micro-fold
    needs only the fraction `θ = 2Λ(2)/√2/λ ≈ 0.53` of the strip surplus, and the convex combination of
    the full ground-state transform with the transform keeping `S × S` exact
    (`fourKilling_add_potentialMix_le_archJump_sub_prime`) leaves the potential
    `(1 − θ)U_h + θU_h^{off}`. Two second-order expansions pay the rest
    (`SecondOrderSurplusPotential`): `ω₂ ≤ ω ≤ ω₂ + u³/250` on `(0, 3/4]`,
    `ω₂(u) = 1/(2u) + 1/4 − u/48 − u²/32`, so `k = k₀ + min(x, y)/24 + xy/8 + O((x + y)³)` and the
    curvature cost drops from `L·O(r³)` to `L(4/125)r⁵` (`mul_surplusPotential_quarticGauge_ge_second`,
    with the exact polynomial `firstOrderSurplus`); and `Ω(y) ≥ −½ log(y/4) + π/4 − y/4 + y²/96`
    (`archLevyAntideriv_ge_second`) adds `(2x² + R²)/48`. With the plateau collar `R − r = 1/20000`
    every odd `F` supported in `[−353/1000, 353/1000]` has `Ẑ(F) ≥ (1/1000)∫F²`
    (`fullZeroForm_ge_of_odd_support_le_threeHundredFiftyThreeThousandths`). The inner-edge loss is
    structural: for a gauge with the true edge behaviour `(R − x)^{1/2}` it tends to `¼` per unit of
    gauge whatever `|S|`, so the micro-fold plus ground-state transform cannot go far past this window
    with near-optimal gauges.

32. **The ground-state remainder carries potential: window `356/1000`.** The ground-state transform
    splits each pair energy exactly, `k(F(x) − F(y))² = F(x)²k(1 − q) + F(y)²k(1 − 1/q) +
    k h(x)h(y)(f(x) − f(y))²`, `q = h(y)/h(x)`, `f = F/h`, and mechanisms 21–31 drop the remainder. On a
    rectangle `Z × H` the Schur step `A(c − t)² + Bt² ≥ c²AB/(A + B)` with `A = k/q`, `B = β` turns the
    remainder into potential at `x`, paid for at `y` (`sq_sub_ge_groundState_schur`):
    `k(a − b)² ≥ a²(k(1 − q) + kβq²/(k + βq)) + b²(k(1 − 1/q) − β)`. Integrated
    (`surplusEnergy_ge_potential_add_schur`),
    `S_P(F) ≥ ∫F²U_h + s₀|H|∫_Z F² − β|Z|∫_H F²` whenever `s₀ ≤ kβq²/(k + βq)` on `Z × H`. The potential
    is no longer local: a deficit on `Z` is paid by any `H` that can afford `β|Z|` per unit of mass. In
    the first prime window the inner edge `Z = [337/1000, 343/1000]` of the strip borrows from its outer
    part `H = [35/100, 356/1000]`, where the plateau logarithm is large. There `k ≥ 128/5`, because the
    distance is at most `19/1000`, and `q ≥ 31/40`; with `β = 40` this gives `s₀ = 21/2`
    (`schurFold_pairWeight_ge`). With the gauge `1/500 + (3/5)y − y² − (11/50)y³ − (49/20)y⁴`, every odd
    `F` supported in `[−356/1000, 356/1000]` has `Ẑ(F) ≥ (1/1000)∫F²`
    (`fullZeroForm_ge_of_odd_support_le_threeHundredFiftySixThousandths`). The structural inner-edge
    loss of mechanism 31 is a loss of the local potential only. With the remainder kept, the wall moves
    to the point where the hub runs out of spare potential.

33. **The prime atom pays the strip: window `9/25`.** For odd `F` supported in `[−r, r]`, `L/2 < r`,
    split `F` on `S = [L − r, r]` into its parts even and odd about `L/2`, `F(a) = e + α`,
    `F(L − a) = e − α`. The atom sees `F(a)F(L − a) = e² − α²` and `e² + α² = (F(a)² + F(L − a)²)/2`,
    so exactly (`integral_mul_shift_eq_two_reflectedOdd_sub`)
    `∫ F(x)F(x + L) dx = 2∫_S α² − ∫_S F²`. Mechanisms 28–32 used only `∫ F F(· + L) ≤ ∫_S α²` and
    dropped the even part. But the even part is the direction of the ground state, and for it the atom
    is a gain: the prime term of `Ẑ` equals `2Λ(2)/√2 ∫_S F² − 4Λ(2)/√2 ∫_S α²`. Interpolating
    (`integral_mul_shift_le_interp`) gives `∫ F F(· + L) ≤ (1 + t)∫_S α² − t∫_S F²` for `t ≤ 1`. The
    sharp micro-fold pays `(1 + t)` times the odd part with the fraction `θ = (1 + t)2Λ(2)/√2/λ`, and the
    strip carries the prime potential `(Λ(2)/√2)t ≥ (49/100)t`
    (`fourKilling_add_potentialMixPrime_le_archJump_sub_prime`). With `t = 1/2` and `θ = 4/5`, in units
    of the gauge this is `(49/200)h ≥ 0.0096` against a strip loss `≤ 7/1000`, so the inner-edge wall of
    mechanisms 31–32 disappears. The window is then limited by the archimedean middle (minimum near
    `x ≈ 0.2`). Under the dilation `x ↦ sx` the log-kernel potential is invariant except for the
    plateau term, which drops by `log s`. The gauge of mechanism 32 dilated by `90/89`,
    `1/500 + (89/150)y − (44/45)y² − (17/80)y³ − (82/35)y⁴`, still has slack there. Every odd `F`
    supported in `[−9/25, 9/25]` has `Ẑ(F) ≥ (1/1000)∫F²`
    (`fullZeroForm_ge_of_odd_support_le_nineTwentyFifths`).

34. **Lending potential to the middle of the window: window `181/500`.** Past `9/25` the binding
    region is the archimedean middle, `x ≈ 0.2`. The off-strip ground-state transform drops the
    remainder of every pair with its lower point below the strip. Two Schur rectangles in it
    (`surplusEnergy_ge_potentialOff_add_strip_add_schur`, with the pair step `sq_sub_ge_schur_pair` and
    the densities `rectDensity`) move potential to `Z = [7/50, 27/100]`:
    * from a hub below, the origin region `[11/250, 7/100]`, where the killing `log((x + r)/x)` is
      large;
    * from a hub above, the strip `[207/625, 181/500]`, where the even part of the atom (mechanism 33,
      now with `t = 4/5`, `θ = 24/25`) leaves the potential `(49/125)h − 97/10000 ≥ 0.0057` in units of
      the gauge.

    They enter with the weight `θ` of the off-strip transform
    (`fourKilling_add_potentialMixPrimeSchur_le_archJump_sub_prime`). The middle gains
    `(24/25)(s_A|H_A| + s_B|H_B|) ≥ 0.0061` per unit of mass, `86%` of it from the strip. The origin
    lends little because a gain per pair is at most `kq²`: its pairs are far apart (`k ≥ 31/50`) and
    the gauge ratio is small (`q ≥ 1/3`), so `kq² ≈ 0.07`. The strip pairs have `k ≥ 5/4` and `q ≥ 1/2`.
    With the gauge of mechanism 33 dilated to `181/500`, every odd `F` supported in
    `[−181/500, 181/500]` has `Ẑ(F) ≥ (1/1000)∫F²`
    (`fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths`).

35. **Harnack across the prime-power shifts with the even part kept.** The identity of mechanism 33
    holds for every shift `log n`. With the sharp micro-fold of the strip `S_n = [log n − r, r]`,
    `(1 + t)2Λ(n)/√n ≤ θλ` gives
    `2Λ(n)/√n ∫F F(· + log n) ≤ θ · 2 stripSurplus_{S_n} − 2(Λ(n)/√n)t ∫_{S_n} F²`
    for all windows `½ log n < r ≤ ½ log n + 1/12`
    (`two_mul_primePowerShift_le_stripSurplus_sub_evenPart`). It sharpens mechanism 30, which is the
    case `t = 0`. For `n = 3`, `Λ(3)/√3 ≤ 0.6344` and `λ ≥ 1.7`, so `t = 1/3`: the atom of `3` is paid
    by its strip and leaves the potential `2/5` (`two_mul_primeThreeShift_le_stripSurplus_sub`). For
    `n = 4`, `Λ(4)/√4 = ½ log 2`: the full even part (`t = 1`) costs `2 log 2 ≤ (4/5)λ`, so `80%` of the
    strip surplus pays the atom and the atom is a net gain `log 2 ∫_{S_4} F²`
    (`two_mul_primeFourShift_le_stripSurplus_sub`). The same holds for every proper prime power,
    since `Λ(p^k)/p^{k/2} ≤ log p/p ≤ 1/e`.

### The shared strip surplus

For an odd test on `[−r, r]` every strip `S_n = [log n − r, r]` ends at `r`, so the strips of the
entered prime powers are nested and share their inner pairs. Mechanisms 30 and 35 pay each atom from
the box `T(S_n) = ∫∫_{S_n × S_n} k(x, y)(F x − F y)²` (`stripBoxEnergy`); summed, they count the pairs
of the innermost strip once per atom.

36. **The shell micro-fold.** Let `S' = [p', r]` be an inner strip right of the centre of `S = [p, r]`,
    `c = p' − m > 0`. A point `m − u` of the left half never exceeds `p'`, so of the four pairs
    `x, L − x, y, L − y` of a quadruple only the right–right pair `(m + u, m + v)` can lie in `S' × S'`,
    and it does exactly when `u, v > c`. Off this corner the sharp quadruple bound holds for the
    strip integrand with the inner box removed (`shellQuadruple_ge`); on the corner the folded weight
    is at most `(2 + η/2)/c + 1` (`sharpFoldWeight_le_corner`: `k(u, v)(u − v) ≤ ½ + (u − v)/4`,
    `4ω(u + v) ≤ 1/c + 1`), and the corner has width `r − p'`. Hence
    `T(S) − T(S') ≥ (λ₀ − (r − p')((2 + η/2)/c + 1)) ∫_S α²`, `λ₀ = 1.9 − η/p − 3η²`
    (`sharpMicroFold_shell_ge`; `T(S) − T(S')` is the shell, `integral_shellIntegrand_eq`). The loss is
    of the order of the width ratio `(r − p')/c` of the two strips.

37. **Allocation without double counting.** *Union:* weights `θ_n ≥ 0`, `Σ θ_n ≤ 1`,
    `(1 + t_n) 2Λ(n)/√n ≤ θ_n λ₀(n)` pay a family of thin strips from one box, since boxes of nested
    strips are monotone (`stripBoxEnergy_mono`, `sum_primeStripCharge_le_union`). *Chain:* for
    `n₀ < … < n_k`, each next strip right of the centre of the previous one, strip `j` pays from the
    shell `T(S_{n_j}) − T(S_{n_{j+1}})` with the shell constant (`shellFoldConstant`) and the last
    from its box; the shells are disjoint and telescope to `T(S_{n₀})`
    (`sum_primeStripCharge_le_chain`). The summand `primeStripCharge` is the atom plus the potential
    `2(Λ(n)/√n)t ∫_{S_n} F²` of its even part. Strips of very different widths share nothing. For
    `½ log 25 < r ≤ ½ log 25 + 1/250` both strips of `23` and `25` are thin, but
    `2Λ(23)/√23 + 2Λ(25)/5 > 1.95` exceeds `λ₀`, so no union allocation exists; the shell constant is
    at least `1.4 > 2Λ(23)/√23` (`shellFoldConstant_twentyThree_twentyFive`) and `7/10` of the box of
    `25` pays twice its atom, so both atoms are paid by `2 stripSurplus_{S_23}` with the even part of
    `25` left as the potential `16/25` (`primeStripCharge_twentyThree_twentyFive_le`, `C¹` form
    `…_of_contDiff`).

38. **The light cone, at every scale, and its exact square-root width.** The band `2r − 2δ ≤ log n < 2r`
    (`lightConeBand`) has at most `2δe^{2r} + 1` integers (`card_lightConeBand_le`), each atom at most
    `2r/(e^r(1 − δ))` (`vonMangoldtAtom_le_of_mem_lightConeBand`). For `r ≥ 2` and `δ ≤ e^{−r}/(16r)`
    its mass is below `1.6` (`sum_vonMangoldtAtom_lightConeBand_le`), under the strip constant `1.89`,
    so every atom of the band is paid by one copy of the surplus of `[r − 2δ, r]`:
    `Σ_{band} 2Λ(n)/√n ∫ F F(· + log n) ≤ T(r − 2δ, r)` (`sum_primeShift_le_lightCone`, `C¹` form
    `…_of_contDiff`). By Selberg sieve (`card_prime_lightConeBand_le_sieve`) and exponent injectivity on
    proper prime powers (`card_properPrimePow_lightConeBand_le`, `pow_add_two_mul_pow_pred_le_pow`), the
    `1/r` factor is removed: the light cone widens to the exact square-root scale `δ ≤ (1/60)e^{−r}`
    for large `r` and uniformly to `δ ≤ c₀ e^{−r}` for all `r ≥ 2` (`eventually_sum_vonMangoldtAtom_lightConeBand_le_squareRoot`,
    `exists_squareRoot_lightCone_allocation`), corresponding to `N − c√N < n < N` for `N = e^{2r}`.
    Conversely, for every `C ≥ 64000`, tiling the macroscopic band into square-root sub-bands shows that
    `T(r − 2Ce^{−r}, r)` frequently fails to pay the odd parts at width `δ = Ce^{−r}`
    (`frequently_lightConeBox_oddPart_sharing_fails_at_squareRoot`).

39. **Outside the light cone neither the odd parts nor the signed band can share.** The odd edge tent of
    width `ε` (`edgeTent`, `edgeTentOdd`) lies in every strip at once. For `r ≤ L ≤ 2(r − ε)` its shift
    product vanishes identically, so the atom of `e^L` is zero and `2∫_{L−r}^r α_L² = ∫_{L−r}^r F² ≥ ε³/32`
    (`edgeTent_oddPart_eq`, `edgeTent_sq_integral_ge`), while all pairs of the support carry
    `T(0, r) ≤ 3ε²r` (`stripBoxEnergy_edgeTent_le`). The thin band `2r − 1/6 ≤ log n ≤ 2r − 1/24`
    (`thinBand`) carries `Σ Λ(n)/√n ≥ (ψ(X) − ψ(e^{−1/8}X))/√X`, `X = e^{2r − 1/24}`
    (`psi_sub_div_le_sum_thinBand`), which by the prime number theorem of `RHTower.Sieve` outgrows every
    linear budget (`eventually_lt_sum_thinBand`). Hence for all large `r` there is an odd test on
    which every atom of the thin band vanishes and every odd part is paid by its own strip, yet the
    odd parts together exceed the surplus of all pairs of `[0, r]²`
    (`exists_edgeTent_oddPart_sharing_fails`). Keeping the even parts does not restore unconditional
    band sharing: the bipolar edge-dipole `F = edgeTentOdd r (1/48) − edgeTentOdd (r − 1/12) (1/12)`
    (`bipolarEdgeTentOdd`) has `F(x)F(x + L) ≥ 0` pointwise for every `L ∈ [2r − 1/6, 2r − 1/24]`
    (`bipolarEdgeTentOdd_mul_shift_nonneg`), integral `≥ 1/884736` on `2r − 7/48 ≤ log n ≤ 2r − 1/8`
    (`integral_bipolarEdgeTentOdd_mul_shift_ge`), and `T(0, r) ≤ r`
    (`stripBoxEnergy_bipolarEdgeTentOdd_le`), so the signed thin-band charge strictly exceeds `T(0, r)`
    for all large `r` (`exists_bipolarEdgeTent_signed_thinBand_sharing_fails`, exact global identity
    `thinBand_signedCharge_eq_tsum_sub_complement`).

40. **The overlapping strips of `2` and `3`, and the end of the odd-part payment.** For
    `½ log 3 < r < log 2` the strip `S₃ = [log 3 − r, r]` lies inside `S₂ = [log 2 − r, r]`, and since
    `e^{2r} < 4` the atoms of `2` and `3` are the whole prime side. Past `r = ¾ log 2` the half-width
    `η = r − ½ log 2` of `S₂` exceeds its distance `p = log 2 − r` to the origin, beyond the sharp fold.
    In folded coordinates `u = |x − L/2|`, `v = |y − L/2|` a quadruple has a same-distance pair group
    with kernels `ω(|u − v|) − ω(L ± (u + v))` and a crossing group with kernels
    `ω(u + v) − ω(L ± |u − v|)`; both pairs of a group see the same odd difference and the same even
    difference.
    * *Wide fold.* Each group at its smaller kernel, `R₋ = ω(|u − v|) − ω(L − u − v)` and
      `R₊ = ω(u + v) − ω(L − |u − v|)`, with `R₋ ≥ R₊` by complete monotonicity of `ω`; in the gauge
      `β + t` the folded weight is `W = 2(R₋ − R₊)(1 − q) + 4R₊`, `q = (β + v)/(β + u)`, and the
      strip pays `λ ∫_{S₂} α²` once `∫_0^η W(u, v) dv ≥ λ` at every `u`. Integrated, `W` is the
      surplus potential minus a defect of order `u³/(L(L − 2η))` plus the crossing term
      `2 log((u + η)/u) − 2 log(L/(L − η)) − O(η²)`.
    * *Harmonic fold.* The even difference of a group is optimized away:
      `K₁(D + e)² + K₂(D − e)² ≥ (4K₁K₂/(K₁ + K₂)) D²`. A group keeps `R + γw` of its excess
      `ω(L − w) − ω(L + w)` when `cs·w ≤ κR`, `γ = cs/(2 + κ)`; at `L = log 2` the excess is at least
      `(28/(9√2)) w` term by term in `ω = Σ e^{−(2k+½)t}` (`slope_mul_le_archLevyDensity_reflect`). A
      pair shared with an inner strip at the fraction `θ` leaves the group the rate
      `2(1 − θ)/(2 − θ) · R` instead of `0`.
    * *Sharing.* Withholding the fraction `θ` of `S₃ × S₃` from the box of `S₂` removes `θ T(S₃)`;
      `θ T(S₃)` pays the atom of `3` by the sharp fold and the rest pays the atom of `2`. For odd
      Lipschitz `F` supported in `[−r, r]`:

          2Λ(2)/√2 ∫ F F(· + log 2) + 2Λ(3)/√3 ∫ F F(· + log 3)
            ≤ 2 stripSurplus_{S₂} − (1/62) ∫_{S₂} F² − c ∫_{S₃} F²,

      with `c = ½` at `r = 221/400` (wide fold, all of `S₃ × S₃` to the atom of `3`) and `c = 0` at
      `r = 23/40` (harmonic fold, `θ = 69/100`)
      (`two_mul_primeTwoThreeShifts_le_stripSurplus_twentyThreeFortieths`).
    * *The end of the odd-part payment.* On `S₂ = [p, log 2 − p]`, `0 < p ≤ 1/400`, the linear
      profile `F(x) = x` has `∫∫_{S₂ × S₂} k(x, y)(x − y)² < 2Λ(2)/√2 ∫_{S₂} α²`. The box of
      `[0, a]²` is at most `a³ − (4/3)a³ log 2 + a⁵/288 + a⁶/180`, so the quotient is at most
      `12 − 16 log 2 + a²/24 + a³/15`: the regional eigenvalue `2` minus `6J`,
      `J = ∫∫_{[0,1]²} (x − y)²/(x + y) = (8 log 2 − 5)/3`, the share of the reflected pairs. At
      `a = log 2` it is `≈ 0.952 < √2 log 2`. Hence no inequality
      `2Λ(2)/√2 ∫_{S₂} α²_F ≤ 2 stripSurplus_{S₂}(F)` holds near `log 2`
      (`not_forall_oddPart_le_stripSurplus_logTwo`): every fold of `S₂ × S₂` that bounds the odd part
      alone stops before `log 2`. With mechanisms 39 and 41, the strip surplus pays odd parts neither
      for a single atom near `log 2` nor for the thin band at large `r`. What any allocation must use
      is the cancellation of the odd parts against the even parts of the atoms, the prime–polar
      balance of mechanism 42 (open problem 7(c)).

41. **The logarithmic capacity of the shared surplus.** For the edge tent the pairs across the foot
    `a = r − ε` carry `∫_0^a ω(x − y) dy = Ω(x − a) − Ω(x) ≤ ½ log(4/ε) + ε/(2(x − a)) + 4/5`
    (`archLevyAntideriv_le_capacity`), so `T(0, r) ≤ (log(4/ε) + 42) ∫_0^r F²` uniformly in `r`
    (`stripBoxEnergy_edgeTent_le_log`), while every strip `[L − r, r]`, `r ≤ L ≤ 2(r − ε)`, charges
    `½ ∫_0^r F²` to its odd part (`edgeTent_oddPart_eq_half_mass`). One copy of the surplus of all
    pairs of the support therefore pays the odd parts of a family of strips wider than `ε` only if
    their weights sum to at most `2 log(4/ε) + 84` (`stripBoxEnergy_edgeTent_lt_sum_oddPart`,
    `sum_le_of_isPayableOddPartFamily`). Conversely, the geometric ratio-`6` telescoping chain
    `L_j = 2(r − η₀/6^j)` (`geometricChainShift`) has scale-invariant corner ratio `1/2` and shell
    constant `≥ 7/10` at every layer (`sharpMicroFold_ratioSix_shell_ge`,
    `sum_geometricChain_oddPart_le_stripBoxEnergy`), establishing the matching lower bound
    `(7/(10 log 6)) log(1/(12ε))` (`exists_payableOddPartFamily_log_lower_bound`).
    The atom mass of the width layer `[η, 2η]` is `≍ ηe^r`, so only the light cone `η ≲ e^{−r}` fits.
    A global allocation must keep the even parts, which cancel the odd parts on the single edge
    tent.

42. **The global shared-surplus allocation.** The prime side `Σ_n 2Λ(n)/√n ∫ F F(· + log n)` of an
    odd test on `[−r, r]` is the finite sum over `n ≤ e^{2r}`: past `2r` the supports are disjoint
    (`integral_mul_shift_eq_zero_of_lt`, `tsum_primeShift_eq_sum_primeSide`). For every `r ≥ 2` and
    `0 < δ ≤ e^{−r}/(16r)` it is at most `T(r − 2δ, r) + Σ_{n ≤ e^{2r}, n ∉ cone} 2Λ(n)/√n m_n(F)`
    (`tsum_primeShift_le_globalAllocation`, `C¹` form `…_of_contDiff`). The atoms of the light cone
    share one copy of the surplus (mechanism 38). Every other atom is charged once, to the mass
    `m_n(F)` of its own strip, `∫_{log n − r}^{r} F²` on a crossing strip (the parity identity at
    `t = −1`) and `∫ F²` otherwise (`atomStripMass`, `two_mul_primeShift_le_atomStripMass`). Every
    atom of the prime side is allocated, and no pair of the surplus is counted twice. By mechanisms
    39 and 41 the surplus share cannot be extended past the cone through odd parts. What remains is
    to pay the strip masses, which is the prime–polar problem of the form, not an allocation of the
    surplus.

### The ledger at every aperture

43. **The incidence ledger and the global allocation condition.** For an odd test `F` supported in
    `[−r, r]`, every `r > 0`, and the plateau `P = aperturePlateau r R` (`1` on `[−r, r]`, `0` outside
    `(−R, R)`, any `R > r`) the fold of mechanism 26 is exact at every aperture:
    `J_P(F) = 2 S_P(F) + 4 ∫_{x>0} F(x)² Π_P(x) dx` with the crossing potential
    `Π_P(x) = ∫_{t>x} ω(t) P(t − x) dt` (`archJump_eq_two_mul_surplus_add_crossingPotential`; the
    bound `ω(t) t² ≤ 3/2 + 4B²` on `(0, 2B]` replaces the restriction `2B ≤ 1` of the windows), and
    `Π_P(x) = (Ω(x) − Ω(x + r)) + ∫_{t>x+r} ω(t) P(t − x) dt`, the killing of the plateau plus the
    axial collar potential of the gauge beyond `r`, between `0` and `Ω(x + r) − Ω(x + R)`
    (`crossingPotential_eq_killing_add_collar`, `collarCrossingPotential_bounds`). The prime side is
    the finite sum over the relevant shifts `n ≥ 2`, `log n < 2r` (`relevantShifts`; a shift
    `log n ≥ 2r` meets no translate, `integral_mul_shift_eq_zero_of_two_mul_le`), and each shift
    splits by mechanism 33 into its even gain and its odd cost. Hence, exactly
    (`fullZeroForm_eq_incidenceLedger`):

        Ẑ(F) = surplusPool + crossingPotentialTerm + Σ_n evenStripGain_n − Σ_n oddStripCost_n
               + gaugeRemainder − poleCharge.

    The pool, the crossing potential, the gains, the costs and the pole are nonnegative
    (`surplusPool_nonneg`, `crossingPotentialTerm_nonneg`, `sum_evenStripGain_nonneg`,
    `sum_oddStripCost_nonneg`, `poleCharge_nonneg`); the gauge remainder
    `∫ F² P(−𝒲P + prime part)` is the only signed piece, bounded below pointwise by the plateau
    potential of mechanism 27. The **global incidence allocation condition**
    `GlobalIncidenceAllocation r R F` is the inequality costs + pole ≤ pool + crossing potential +
    gains + remainder. By the ledger it is the sign of the form, test by test
    (`globalIncidenceAllocation_iff_fullZeroForm_nonneg`), and since RH is the positivity of `Ẑ` on
    odd compact tests (`riemannHypothesis_iff_forall_odd_fullZeroForm_nonneg`):

        RH ⟺ every odd compact test satisfies the condition at every aperture and plateau radius

    (`riemannHypothesis_iff_globalIncidenceAllocation`; one plateau radius per test suffices,
    `riemannHypothesis_iff_exists_plateau_globalIncidenceAllocation`). Every window theorem of
    mechanisms 23–35 and 40 is the condition at its aperture: the sharp micro-fold pays
    `oddStripCost` from a share of the pool, the even part is `evenStripGain`, and the certificate
    bounds the remainder with the crossing potential and the pole. Mechanism 42 pays the costs beyond
    the light cone with the strip masses; the ledger names what must pay those masses, the remainder
    and the crossing potential of the pairs the cone does not use, together with the gains.

    The remainder is archimedean and has an explicit floor. The prime part of `−𝒲P` cancels the
    returned prime sum exactly, `gaugeRemainder P F = ∫ F² P (∫_{u>0} profileArchTerm P x u − (γ + log π) P(x))`
    (`gaugeRemainder_eq_arch`), and for the aperture plateau
    `gaugeRemainder ≥ ∫ F² · (Ω(R − x) + Ω(R + x) − 2E(0) − (γ + log π))`
    (`plateauPotentialFloor`, `gaugeRemainder_ge_plateauPotentialFloor`; mechanism 27 pointwise,
    integrated through `Ω ≤ Ω(R − r)` on the support). With the pole bound of mechanism 23 this gives
    the **explicit ledger floor** (`fullZeroForm_ge_explicitLedgerFloor`):

        Ẑ(F) ≥ surplusPool + crossingPotentialTerm + Σ gains − Σ costs
               + ∫ F² · plateauPotentialFloor R − (R³/3) cosh²(R/2) ∫ F²,

    every term an explicit functional of `F` with no Weil operator and no pole moment; its
    nonnegativity is a sufficient condition for the sign of the form, and every window certificate
    of the programme is a proof of it at its aperture with a gauge transform of the pool.

    **The ledger is graded by the width.** The exact sign of the allocation is the endpoint of a
    one-parameter family, and the interior members are explicit zero-free strips: an allocation
    deficit `C e^{2σ r}∫F²` at every aperture `r` gives `Θ ≤ ½ + σ`, a deficit bounded uniformly in
    the aperture gives RH (`SquareRootThreshold.zetaZeroWidth_le_of_gradedIncidenceAllocation`,
    `riemannHypothesis_of_gradedIncidenceAllocation_zero`). The bridge is the odd difference test of
    the lag family, whose aperture rate `e^{2σ(v/2+w)}` is the lag rate `e^{σv}`, and the lag rate is
    the width. So quantitative work on the ledger is scoreable, and the sign is needed only in the
    limit — provided the estimate holds at *every* aperture: a bounded family of windows reports
    nothing however good its constants.

    **What the floor is made of at large aperture.** Beyond lag `O(1)` the ledger's balance is the
    prime–polar difference and nothing else. At lag `t` the prime measure has density
    `≍ e^{t/2}dt`, the polar measure `2 cosh(t/2)` has the same density, and the archimedean density
    `ω(t) ≍ e^{−t/2}` is smaller by `e^{t}`: the surplus contributes nothing where the mass is, which
    is why every window of this programme lives at small aperture and why the remainder cannot pay
    the strip masses. The far correlations cannot be made small either: the autocorrelation is
    positive definite and supported in `[−2r, 2r]`. The Krein chord inequality gives
    `a(t) ≤ (3/4)a(0)` beyond `r`; the sharper bipartite split into the two halves of the test
    gives `a(t) ≤ a(0)/2` there (`autoCorrelation_le_half`). Both are constant-factor bounds,
    not a power saving as the aperture grows. Nor does oddness help: an odd test concentrated in an `O(1)` window at
    the edge of its support has edge mass `m(s) ≍ 1`, the lags within `O(1)` of `2r` already carry
    the full prime mass `≍ e^{r}`, and for that test the pole charge `2(∫F sinh(x/2))² ≍ e^{r}` and
    the prime correlation `≍ −e^{r}` are of the same size and opposite sign. The rate-`1` floor is
    the prime-charge-against-pole-charge balance at PNT level, and a sub-trivial rate is a fixed
    zero-free strip — exactly as hard as what it would prove.

### The translate calculus and the tower laws

Mechanisms 1–43 read the form through the geometry of pairs: which conductance is negative, which
atom is unpaid, which strip pays it. The mechanisms below read it through a second, independent
source of unconditional inequalities: the nonnegativity of the energy of a *finite combination of
translates* of the test. Each one is a single square expanded in the autocorrelation, so each is an
inequality among the **lag charges** of one test, with no gauge, no fold and no archimedean input.

44. **The pairing calculus.** On continuous compactly supported functions, `⟪A, B⟫ = ∫AB` with its
    bilinearity, translation invariance and Cauchy–Schwarz; the autocorrelation
    `A(t) = ⟪F, F(· + t)⟫` with `|A(t)| ≤ A(0)` and `A(t) = 0` beyond the support diameter; the Gram
    expansion `⟪Σ_k α_k F(· + c_k), Σ_j β_j F(· + d_j)⟫ = Σ_{k,j} α_k β_j A(d_j − c_k)` with the bound
    by the product of the coefficient masses; and the **geometric train**
    `S_N = Σ_{k ≤ N} z^k F(· + kL)` with the resolvent identity
    `S_N − z S_N(· + L) = F − z^{N+1} F(· + (N+1)L)` (`TranslatePairingCalculus`). Every estimate of
    the prime side in this programme is an estimate of `⟪A, B⟫` for such combinations.
45. **The prime tower law and its first-power discount.** The prime side of the zero form is
    `Σ_{n ≥ 2} 2Λ(n)n^{−1/2} A(log n)`. Read tower by tower, the atoms of `p, p², p³, …` sit at the
    arithmetic progression `k log p` with geometric weights, so a whole tower is one geometric lag
    charge `C_p(F) = log p Σ_{k ≥ 1} z^k A(k log p)`, `z = p^{−1/2}`. The two-step square
    `∫(S(u) − S(u + 2L))² ≥ 0`, together with the resolvent identity, collapses to
    `(1 − z²) Σ_{k ≥ 1} z^k A(kL) ≤ z² A(0) + z A(L)`, that is the **Euler envelope**
    `z/(1−z)·A(0)` discounted by the **first-power fold defect** `A(0) − A(L)`. At `z = p^{−1/2}`,
    `L = log p` this is
    `(p − 1) C_p(F) ≤ log p (A(0) + √p·A(log p))` (`PrimeTowerEulerEnvelope`): the charge of a whole
    prime tower is controlled by the single datum `A(log p)`. The proper prime powers carry no
    information of their own beyond the Euler constants, and a test uncorrelated at the prime shift
    charges the tower `log p/(p − 1)` instead of the envelope `log p/(√p − 1)`.
46. **The envelope is attained: the resonant train.** `M + 1` disjoint copies of one bump at
    spacing `L` have `A_S(mL) = (M + 1 − m)A_g(0)`, hence lag charge a fraction
    `z/(1−z) − z^{M+1}/(1−z) − z/((M+1)(1−z)²)` of the mass (`ResonantTrainWitness`). The envelope is
    therefore sharp, and its extremal tests are the trains carried by a **multiplicative
    progression** `{1, p, p², …}`. The content of the tower law is its discount, not its envelope.

    **The parity twin of a tower.** The tower law holds for every ratio `|z| < 1`, signed ones
    included. At `z = −p^{−1/2}` the weights become `λ(p^k)Λ(p^k)p^{−k/2}`, the Liouville twin of the
    tower, and the law reads `(p − 1)C⁻_p(F) ≤ log p (A(0) − √p A(log p))`
    (`sub_one_mul_twistedTowerCharge_le`) against `(p − 1)C_p(F) ≤ log p (A(0) + √p A(log p))`. The
    two bounds differ by `2√p log p A(log p)`: where the first power is positively charged (the
    resonant regime, expensive for the primes) the twin is strictly cheaper, and conversely. Its
    envelope is attained by the **alternating train** `Σ_k (−1)^k g(· + kL)`, whose correlation
    carries the parity of the lag index, so its twisted charge equals the untwisted charge of the
    resonant train (`geoLagCharge_alternatingTrain_eq`). The single-tower sector is therefore closed in
    both signs, and the tower law is not a formal consequence of geometric decay: it reads the sign
    of `A(log p)`, and through it separates the primes from their parity twin at the first power.
47. **The ledger with the prime powers eliminated.** By the exact even–odd identity of an atom the
    net charge of a shift is `evenStripGain_n − oddStripCost_n = −2Λ(n)n^{−1/2}A(log n)`, so the net
    prime charge of the ledger is `−2` times the prime side; the tower law then removes the proper
    prime powers, bounding the whole cost side by a functional of the **primes** below the horizon
    and their first-power autocorrelations `A(log p)`, with the Euler constants `log p/(p − 1)` and
    `√p log p/(p − 1)` (`PrimeTowerLedgerReduction`).
48. **The bi-tower law: two spacings, with products and ratios as payers.** Reading the `b`-train
    `G = Σ_{k ≤ N} w^k F(· + kb)` as the test and applying the tower law at spacing `a` gives a law
    for the whole lattice of lags `ma + jb`, `m ≥ 1`, `j ∈ ℤ`. The train's autocorrelation is the
    two-sided `b`-ladder `A_G(s) = Σ_{j,k ≤ N} w^{j+k} A(s + (k − j)b)`, and
    `(1 − z²) Σ_{m ≥ 1} z^m A_G(ma) ≤ z² A_G(0) + z A_G(a)` (`BiTowerIncidenceLaw`). At
    `z = p^{−1/2}, a = log p, w = q^{−1/2}, b = log q` the lags are the integers `p^m q^{k−j}`, so the
    **product** shifts `log(p^m q^i)` and the **ratio** shifts `log(p^m/q^i)` both occur, with the
    Euler weights of both primes: the entire coupling graph between two towers is paid by two ladder
    charges, and a ladder uncorrelated at the lag `a` pays only `z²/(1−z²)` of its mass.
49. **The divisor lattice of one modulus.** Fix `q` and weight its divisors by `c`; the comb
    `Σ_{d ∣ q} c_d F(· + log d)` has nonnegative energy, so the **ratio-incidence matrix of a
    modulus is positive semidefinite**, `0 ≤ Σ_{d,e ∣ q} c_d c_e A(log e − log d)`
    (`DivisorLatticeGramPositivity`). Every minor is an unconditional inequality among the charges at
    the ratios of divisors of one modulus — single modulus, no family average. Two readings: with the
    **Möbius row** `c = μ` the comb is the divisor-lattice difference operator and on a *resonant*
    direction the form collapses to `(Σ_{d ∣ q} μ_d)² A(0)`, which vanishes for every `q ≠ 1`, so the
    Möbius comb annihilates exactly the mode where the charges are largest; with `c ≡ 1` the same
    collapse gives the maximum `τ(q)² A(0)`. Products over a set of shifts give one term per
    **subset**: the signed combination `Σ_{S ⊆ s} (−1)^{|S|}(Π_{i ∈ S} λ_i) F(· + Σ_{i ∈ S} a_i)` has
    nonnegative self-pairing, and at `a_i = log p_i` its shifts are the logarithms of the squarefree
    divisors of `Π p_i`, so the whole incidence lattice of a squarefree modulus constrains the
    charges of its primes at once, with weights the allocation may choose freely
    (`SquarefreeIncidencePositivity`). The cases `|s| = 1, 2` are the one-shift bound
    `2λ A(a) ≤ (1 + λ²)A(0)` and the two-shift coupling law.
50. **The prime-comb reduction and its limitation.** After
    mechanism 47 the cost side is a weighted sum of *first-power* charges `Σ_p w_p A(log p)` with the
    Euler weights `w_p ≍ log p/√p`. Read as a pairing it is `⟪F, Σ_p w_p F(· + log p)⟫`, so
    Cauchy–Schwarz bounds its square by `A(0)` times the **prime-comb energy**
    `E_w(F) = Σ_{p,q} w_p w_q A(log q − log p)`, the Gram form of the weighted prime comb
    (`PrimeCombEnergyReduction`). Split it:
    `E_w(F) = (Σ_p w_p²) A(0) + Σ_{p ≠ q} w_p w_q A(log(q/p))`.
    The diagonal is harmless — with the Euler weights `Σ_{p ≤ e^{2r}} (log p)²/p` is *polynomial* in
    the aperture, while the squared `ℓ¹` majorant is `(Σ_p w_p)² ≍ e^{2r}`. Hence a nonpositive cross-prime aggregate gives
    `Σ_p w_p A(log p) ≤ √(Σ_p w_p²)·A(0)` (`cost_le_sqrt_diagonal_mul_mass`). More generally an
    aggregate at most `B(r)A(0)` gives the bound `√(Σ_p w_p² + B(r))·A(0)`. A polynomial `B`
    would therefore turn the exponential rate-`1` bound into a polynomial one. This is a valid
    conditional reduction, but its universal polynomial premise is false. Compensation Theory
    proves that both raw comb energy and the cross-prime aggregate are `∼4e^{2r}` on a smooth
    odd unit-mass family (`exists_odd_smooth_family_sharp_comb_rate`). Its normalized comb translates
    the slowly varying profile to the horizon, while the first-power charge is only `o(e^r)`.
    On every fixed nonzero continuous compact test, energy is `∼4J(F)e^{2r}` with `J(F)>0`.
    Thus Cauchy–Schwarz can discard the very overlap geometry needed to estimate the charge;
    the raw second moment is not the unresolved signed prime–polar balance.
51. **The bi-lattice train: simultaneous resonance defeats a sign-only bound.** The single-tower sector is closed — both the arithmetic envelope and its
    parity twin are attained by trains on one multiplicative progression (mechanism 46). The
    cross-tower sector needs a test aligned with *two* primes at once: the **bi-lattice train**, unit
    copies of one bump at the shifts `S = {ia + jb : i, j < M}`, `a = log p`, `b = log q` — the
    logarithms of the `{p, q}`-smooth numbers of a square box. Since `log p` and `log q` are
    `ℤ`-independent, the lag `ka` is matched exactly by the lattice pairs differing by `k` in the
    first exponent and agreeing in the second, so `A_S(ka) = (M − k)·M·A_g(0)` and
    `A_S(0) = M²·A_g(0)`, symmetrically in `b` (`BiLatticeTrainWitness`). Both towers resonate to the
    full fraction `(M − k)/M → 1`: **the two Euler envelopes add**, so the prime-side bound is sharp
    already on a pair of aligned towers. The consequence for mechanism 50 is negative and exact: the
    cross lags `log(p^i/q^j)` carry positive counts, so the cross-prime aggregate of an aligned test
    is *strictly positive*. This refutes a universal nonpositive-aggregate hypothesis. Strict positivity alone does not
    refute a polynomial upper bound; the growing-aperture family in mechanism 50 supplies that
    separate quantitative obstruction. The surviving target retains the first-power charge and
    the pole together, or subtracts a proved coherent contribution before estimating a remainder.

**Finite capacities and shared allocation.** SAEI sharpens the train calibration: for `M+1`
disjoint bumps at spacing `log p`, the first-lag charge is at most
`cos(π/(M+2)) A(0)`, attained by sine amplitudes, whereas unit amplitudes give `M/(M+1)`.
For two aligned towers the capacities add and the product sine attains their sum
(`SineTrainsAreExtremalForOnePrime`, `TowerGridCapacitiesAdd`). These concern first lags at finite
length, not simultaneous attainment of every prime-power envelope. Its local allocation theorem
also identifies the abstract budget constraint: every overlap borrows shares from its two
endpoints without exceeding either diagonal budget. Balance makes positivity equivalent to such
payment; frustration permits positive forms that require a global treatment. A continuum
application still needs a justified coupling and uniform limiting estimates.

**The product part is rank one per tower.** In the lattice model a half-line profile `q` on the
integers has ratio correlation `R_q(m) = Σ_a q(a)q(am)` and product correlation
`P_q(m) = Σ_{ab=m} q(a)q(b)`, and the odd prime side is `Σ_m Λ(m)m^{−1/2}(2R_q(m) − P_q(m))`. The
product pairs at `p^k` lie in one tower, and the whole product contribution of the tower of `p` is
one square, `log p·(S_p(q)² − q(1)²)` with `S_p(q) = Σ_i q(p^i)p^{−i/2}` the local Mellin value of
the profile at `s = ½` (`sum_vonMangoldt_productCorr_prime_pow`, Arithmetic Orientation Theory).
The sign of the odd form is therefore a competition between the ratio correlations, which couple
every tower to every other, and a sum of independent rank-one squares, one per prime. Summed over
a tower, the product part is at least `−log p·q(1)²` and is a sum of squares once the profile
vanishes at `1`, so the odd prime side is then at most twice its ratio part
(`latticeOddPrimeSide_le_of_eq_zero`): the summed counterpart of the dominance law of mechanism 8.

### The Chebyshev ledger: the prime–polar balance as one signed functional

The large-aperture comparison has an exact arithmetic coordinate, developed in
`LagChebyshevAbelSummation`. Its subject is the arithmetic channels of the form only — the prime
side and the pole plane; the archimedean density is not part of this ledger.

52. **The balance and the receiver.** For a `C¹` lag weight `h` vanishing beyond a finite endpoint,
    with the **two-pole Chebyshev defect** `E(s) = e^s + s − 1 − ψ(e^s)`, lag Abel summation gives

        Σ_n Λ(n) h(log n) − ∫_{s>0} (e^s + 1) h(s) ds = ∫_{s>0} E(s) h'(s) ds

    (`sum_vonMangoldt_sub_polar_eq_chebyshev`). The primitive `e^s + s − 1` vanishes at `0`; its
    derivative is the density of both poles. A second summation by parts pairs the curvature of the
    weight with the critical-scale functional `D(s) = ∫₀ˢ(e^u − ψ(e^u))du`: the same imbalance is
    `−∫_{s>0}(D(s) + s²/2 − s)h''(s)ds` (`sum_vonMangoldt_sub_polar_eq_criticalScalePrefix`). For the
    test weight `2e^{−s/2}A(s)` the polar integral is exactly the pole plane
    `2(∫F e^{−x/2})(∫F e^{x/2})`, a rank-one readout that is minus a square on odd tests. So the
    incidence decomposition and the critical-scale receiver are two readings of one signed functional.
    Tail and double-tail weights realise every mollified value of `E` and of `D + s²/2 − s`: the
    ledger does not merely imply the receiver, it measures it. Band weights see `E` modulo constants
    and `D` modulo affine functions (`abs_residue_le_centred`, `abs_residue_band_le_affine`), so
    every estimate the ledger supports is an *approximation error* of the receiver across a band,
    never its size.
53. **The ledger is an instrument on sources.** Nothing in the summation is special to `Λ`: every
    source, every lag system and every calibration `W` with `W(0) = 0` has its own prefix, defect and
    critical-scale receiver, and the balance holds verbatim. What separates sources is therefore the
    defect alone, and the defect is a complete invariant: two sources with equal lag prefixes agree
    index by index (`eq_of_lagPrefix_eq`), every prefix is realised by a source, and the ledger
    reads a single-index perturbation at `log m` exactly. The test models are separated at the only
    quantity the ledger sees: the shifted pair carries `Λ(n)(n^α + n^{−α}) ≥ 2Λ(n)` and is off by a
    full Chebyshev count (`two_mul_vonMangoldt_le_shiftedPairWeight`), indeed by a different pole
    position; the Liouville twist is off by twice the odd-`Ω` prime-power mass
    (`chebyshevTwoPoleDefect_le_liouville`); a geometric Beurling system is off at the size of the
    main term; dilating a test by `λ` is a passage to the Beurling system of `λ`-th powers, whose
    critical line is `1/(2λ)` (`weil_dilation_covariance`). A criterion calibrated to `ζ` cannot be
    dilation invariant. The Möbius source is read against the reflected pole alone, with defect
    `s − M(e^s)` and the Mertens receiver `∫₀ˢ(u − M(e^u))du`; real character twists and residue
    classes have their own ledgers, which partition `ζ`'s with no cross terms. The logarithm source
    has a double pole and defect `O(s)` (Stirling) unconditionally: the difficulty is specific to `Λ`.
54. **Calibration and density.** An integer-indexed source can calibrate exactly the poles
    `0 < ρ ≤ 1` to `O(1)`: the defect must absorb the calibration's increment across every cell,
    which is unbounded for `ρ > 1` and for a double pole at `1`. The **ideal source** with weights
    `1 + log(1 + 1/(n−1))` matches the two-pole calibration to `1 + log 2`
    (`abs_lagSourceDefect_idealSource_le`), so an `O(1)` defect is neither automatic nor impossible,
    and `ζ`'s ledger differs from the ideal one by exactly the PNT error paired with `h'`
    (`ledger_vonMangoldt_sub_ideal`). Conversely a bounded defect forces density: an atom-free
    interval of length `L` forces defect `≥ L/2` (`defect_poleAt_ge_of_atomfree`), a defect `≤ K`
    forces at least `J` prime powers below `1 + 3KJ` (`card_ge_of_poleAt_defect_le`), and the
    exponent of the forced density is the position of the pole. Since the atoms `log p` are
    unbounded, so is `E` (`exists_abs_chebyshevTwoPoleDefect_gt`): the receiver is a statement about
    the rate of growth of `E`, whose leading rate is the prime number theorem
    (`tendsto_chebyshevTwoPoleDefect_div_exp_iff`).
55. **The receiver as a discrete object.** The Chebyshev count is frozen on integer cells, so
    `D(log(N+1)) = D(log N) + 1 − ψ(N)log(1 + 1/N)` (`criticalScalePrefix_log_natCast_succ`), `D` is
    strictly convex on each cell with kinks exactly at the atoms, it is positive on the first two
    cells (`criticalScalePrefix_pos_first_cell`, `criticalScalePrefix_pos_second_cell`), positivity
    propagates across a cell exactly when `ψ(N)/N` leaves a margin — the receiver's sign is a
    statement at PNT precision — and it lies in explicit unconditional envelopes at every scale
    (`criticalScalePrefix_le_exp`, `criticalScalePrefix_ge_explicit`). The first prime windows are
    identities: no arithmetic below aperture `log 2/2`, the single atom at `2` below `log 3/2`
    (`testBalance_firstWindow`), the atoms at `2, 3` below `log 4/2`, and the first prime power
    `4` below `log 5/2`.
56. **Test geometry.** Past the aperture the correlation is at most half the mass, sharply
    (`autoCorrelation_le_half`), and the far prime side is one bilinear pairing of the two halves
    of the test — the convolution of the halves — so on an odd test with a nonnegative half every far
    atom is read with the favourable sign (`autoCorrelation_nonpos_of_odd_nonneg`). Along chains of
    `k` points the extremal correlation is the path eigenvalue `cos(π/(k+1))` (the aperture–lag
    ladder, sharp at every rung, `sum_atom_mul_autoCorrelation_le_ladder`), and the displacement
    energy `D(t) = A(0) − A(t)` obeys `D(kt) ≤ k²D(t)`, which yields the universal quadratic gap
    `A(u) ≤ (1 − u²/(8r²))A(0)` for `0 < u ≤ r` (`autoCorrelation_le_quadratic`). The Gram matrix of
    atoms is a function of the ratio alone, banded by the integer spacing, and its Schur constant is
    the mass times the number of partners within the aperture (`aggregate_le_bandwidth`,
    `aggregate_dyadic_le`). The **replacement hypothesis** is exact: a power saving over the `ℓ¹`
    prime cost is equivalent to a bounded Schur constant for the prime-ratio correlations, and
    nothing weaker about the test supplies it. The cross-prime aggregate is the energy of the prime
    field and the prime cost its first moment (`crossAggregate_eq_meanSquare`, `crossAggregate_ge`):
    for first-power Euler weights it is polynomial, for the half-power family
    `√p log p/(p − 1)` the question is open. An odd test has autocorrelation of zero total mass and
    must carry a definite negative correlation at its far lags; the even/odd decomposition splits
    the Weil-shaped form exactly (`residue_even_odd_split`).

    **The defect coordinate.** Writing `δ(t) = A(0) − A(t)`, the prime charge is
    `Σ_n (Λ(n)/√n)A(log n) = ℓ¹·A(0) − D(F)` with the atom-weighted defect
    `D(F) = Σ_n (Λ(n)/√n)δ(log n)` (`sum_atom_mul_autoCorr_eq`). An upper bound on the charge is a
    lower bound on `D`: the test must be *non-invariant* under the prime shifts, `D ≥ (ℓ¹ − C)A(0)`
    with `ℓ¹ ≍ 2e^r`, i.e. decorrelate at essentially every prime-power lag in the atom-weighted
    average. Part of this is free. The chord cascade `A(0)/m² ≤ δ(x₀/m)` whenever `A(x₀) ≤ 0`, and
    every lag beyond the aperture has a vanishing double, so each shift longer than the aperture
    has defect at least a quarter of the mass (`quarter_le_shiftDefect`); since the atoms above
    `e^r` carry the bulk of the `ℓ¹` mass, the high range is discounted unconditionally,
    `Σ_{log n > r}(Λ(n)/√n)A(log n) ≤ (3/4)(Σ_{log n > r}Λ(n)/√n)A(0)`
    (`sum_atom_mul_autoCorr_le_three_quarters`). The remaining quarter is a statement about the
    arithmetic of the shifts, not about the geometry of the test.
57. **The Euler comb ledger.** A squarefree comb `F − λF(· + a)` acts as the Euler transform at
    weight `w = 2λ/(1+λ²)`; iterating over a family of lags telescopes into a payment law — the
    first-power charge of each lag, in the ledger transformed by its predecessors, is paid by the
    mass (`eulerPayment_le_mass`) — for every admissible weight `w ≤ 1`, which includes every
    prime-power Euler weight `Λ(n)/√n ≤ 2/e` (`eulerPayment_vonMangoldt_le_mass`). The law is never
    tight on a nonzero test (`eulerPayment_lt_mass`), and the raw first-power charge differs from the
    sequential payment by explicit cross-charges at the ratio and product lags of each pair
    (`eulerPayment_eq_raw_sub_cross`): the coherent subtraction the prime side needs, located at the
    incidences of §3.
58. **The spectral form.** The Gram kernel is the cosine transform of the nonnegative density
    `|F̂|²` (`autoCorrelation_eq_integral_spectral`), so each weighted lag charge is the pairing of
    its symbol `Σ_j w_j cos(2πa_jξ)` with that density; a comb multiplies the density by
    `1 − w cos(2πaξ)`, and the payment law is the statement that a nonnegative multiplier removes at
    most the whole mass (`eulerPayment_eq_integral_multiplier`). An aperture-`r` test has a
    Lipschitz density, so it can track a peak of a symbol only if the peak is wider than `1/r`. The
    polar side has the symbol `K_T(b) = ∫₀ᵀcosh(s/2)cos(bs)ds`, nonnegative only up to the first
    quarter period: the pole pays only in the band `|ξ| ≤ 1/(8r)` (`coshCosKernel_nonneg_band`),
    where an odd test, whose density vanishes quadratically at the origin, can place only a cubically
    small mass (`setIntegral_spectralDensity_payingBand_le`). The whole Chebyshev pairing is one
    frequency integral, `2∫(primeSymbol_N(ξ) − 2K_{2r}(2πξ))|F̂(ξ)|²dξ`
    (`chebyshev_pairing_eq_spectral`), and the **symbol criterion** follows: a pointwise floor `c` on
    the signed symbol gives the floor `2c·A(0)` on the pairing for every test supported in `[−r, r]`
    (`chebyshev_pairing_ge_of_symbol_ge`). At the origin the symbol is the Chebyshev–Mertens
    comparison `Σ_{n≤N}Λ(n)/√n − 4 sinh r` (`symbol_zero_eq`); a statement quantified over all tests
    becomes a statement about one explicit function of frequency.
59. **The reflected-prime/polar ledger at every aperture.** The window certificates decouple the
    reflected-prime strips from the pole charge only on restricted horizons, `R ≤ 3/5`. Across
    arbitrary tests the decoupling fails on the odd edge tent, for two independent reasons: its
    pole charge grows like `ε⁴e^r` against a strip box energy `≤ 3ε²r`, and every sub-light-cone
    shift has `F(x)F(x + L) = 0` (`exists_edgeTent_reflectedPrimePolar_decoupling_fails`). What
    survives at every aperture is a regrouping of the ledger around one signed quantity, the
    **reflected-prime/polar cost** `costs − gains + poleCharge`:

        Ẑ(F) = surplusPool + crossingPotentialTerm + gaugeRemainder − reflectedPrimePolarCost(F, r)

    at every `0 < r < R` (`fullZeroForm_eq_reflectedPrimePolarLedger`). The other pieces are
    controlled separately. The gains are a polar integral plus a Chebyshev pairing and always pay
    at least half the odd costs (`sum_evenStripGain_eq_polar_add_chebyshev`,
    `sum_oddStripCost_le_two_mul_sum_evenStripGain`). The pole charge is at most
    `8 sinh r ∫F² ≤ 4e^r∫F²` for every plateau (`poleCharge_le_eight_mul_sinh_mul_sq`). The gauge
    remainder is at least `−(27/5)∫F²` (`gaugeRemainder_ge_neg_const_mul_sq`).

    The cost itself is the finite-horizon pairing of the two-pole Chebyshev defect with the lag
    weight of the test, and for `C²` tests the critical-scale receiver against its curvature
    (`reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc`,
    `reflectedPrimePolarCost_eq_criticalScalePrefix`,
    `reflectedPrimePolarCost_eq_criticalScalePrefix_Ioc`). Its unconditional pure-mass size is the
    prime number theorem, sharpened in `SharedDerivativeEnergyAndGlobalAllocationSynthesis` by two
    exact mechanisms:
    - **Sharp Cauchy–Schwarz pole-charge bound:** `poleCharge F ≤ (2 sinh r − 2r)∫F² ≤ (e^r − 2r)∫F²`
      (`poleCharge_le_two_sinh_sub_two_r_mul_sq`, `poleCharge_le_exp_sub_two_r_mul_sq`), improving
      `8 sinh r ≤ 4e^r` by a factor of `4`;
    - **Bipartite high-lag halving law for odd tests:** for every odd test supported in `[−r, r]` and
      every lag `t ≥ r`, `|A_F(t)| ≤ ½∫F²` (`abs_autoCorrelation_le_half_of_le`), upgrading the
      high-range defect floor from `¼` to `½` (`half_le_shiftDefect_of_odd`,
      `sum_atom_mul_autoCorr_le_half_of_odd`) and halving the prime sum on `r ≤ log n < 2r`
      (`abs_sum_relevantShifts_autoCorrelation_le_bipartite`).
    Together these lower the explicit Chebyshev pure-mass bound from `72e^r∫F²` to
    `(35e^r + 34e^{r/2} − 2r)∫F² ≤ 69e^r∫F²`
    (`abs_reflectedPrimePolarCost_le_thirtyFive_exp_add_thirtyFour_exp_half`,
    `abs_reflectedPrimePolarCost_le_sixtyNine_mul_exp_mul_sq`) and lower the asymptotic PNT pure-mass
    prefactor from `(8 + ε)e^r + C_ε` to `(3 + ε)e^r + C_ε`
    (`exists_abs_reflectedPrimePolarCost_le_three_add_eps_mul_exp`).

    In the Sobolev normalisation, both the first-order Chebyshev pairing (`∫F² + ½∫F'²`) and the
    second-order pole-tilted critical-scale pairing (`¼∫F² + ∫F'²`) reach the de la Vallée Poussin
    sub-envelope rate `K e^r e^{−c√r}` across all apertures
    (`exists_abs_reflectedPrimePolarCost_le_exp_sub_sqrt_mul_sobolev`,
    `exists_abs_reflectedPrimePolarCost_le_exp_sub_sqrt_mul_poleTiltedSobolev`). Paying a single
    shared derivative-energy reserve `α∫(F')²` (`α ≥ ½ K e^r e^{−c√r}`) reduces the all-test deficit
    to the pure-mass sub-envelope rate `K e^r e^{−c√r}∫F²`
    (`exists_shared_derivative_payment_sub_envelope`), and on the exponentially growing bandwidth
    cone `∫(F')² ≤ 2e^{c√r}∫F²` half of the de la Vallée Poussin saving absorbs the derivative energy
    automatically in pure mass (`exists_abs_reflectedPrimePolarCost_le_sub_envelope_of_dirichlet_le`).
    Under test compression `F_a(x) = F(ax)` (`a ≥ 1`), support stays inside `[−r, r]` while `∫F_a²`
    scales by `a⁻¹` and `∫(F_a')²` by `a` (`integral_sq_and_deriv_sq_compressTest`), explaining why
    finite-horizon integrability of `E` alone cannot eliminate `∫(F')²` across all tests without
    shared derivative-energy payment.

    Four allocations follow unconditionally. The global allocation holds with margin
    `(1/1000)∫F²` on `(0, 181/500]` (`globalIncidenceAllocation_of_le_threeHundredSixtyTwoThousandths`).
    At the overlapping two-prime window `r = 23/40`, whose relevant shifts are `{2, 3}`, the cost
    plus `(1/62)∫_{S₂}F²` is at most `2 stripSurplus_{S₂} + poleCharge`
    (`reflectedPrimePolarCost_le_stripSurplus_add_poleCharge_twentyThreeFortieths`). The graded
    allocation `GradedIncidenceAllocation (1/2) 75` holds at every aperture
    (`gradedIncidenceAllocation_half_seventyFive`, improving `78` to `75`). And the global allocation
    holds at every aperture with either the first-order (`∫F² + ½∫F'²`) or second-order pole-tilted
    (`¼∫F² + ∫F'²`) de la Vallée Poussin Sobolev deficit
    (`exists_globalIncidenceAllocation_with_deLaValleePoussin_deficit`,
    `exists_globalIncidenceAllocation_with_poleTilted_deLaValleePoussin_deficit`). Rate `½` in the
    graded form is the ambient strip `Θ ≤ 1`. The content is that the ledger reaches the PNT rate
    with explicit constants; every improvement must lower the exponent.
60. **Which data see a sign flip.** Every complete-period quadratic form of a divisor row is an
    even function of each Selberg coordinate, so it cannot distinguish rows that differ by a sign
    character `Y(q) ↦ ±Y(q)`, and conversely equal lag covariances force such a character
    (Bézout–Valuation Incidence, pillar 12; the parity pairs of Trans-Horizon Incidence Mechanics
    agree on all of them at every horizon). The prime-comb energy is not of this kind: flipping one
    Selberg mode changes it by an explicit atom, and for the rows `Y = δ₂ ± δ₃` the two comb
    energies differ by `4A(log 3 − log 2)` (`combEnergy_singleModeSignFlip_sub`,
    `completePeriod_parity_and_transHorizon_separation`). On the translate side the same parity
    appears as a two-atom law: the three-shift Gram along the parity-twisted ray gives
    `(A(a) − A(b))² ≤ 2A(0)(A(0) − A(b − a))` (`sq_two_atom_sub_le`), and its average with the
    untwisted law cancels the ratio lag, `A(a)² + A(b)² ≤ 2A(0)²` (`sq_two_atom_add_sq_sub_le`).
    The incidence face reads signs through the ratio lag `log(b/a)`; period statistics never do.

---

## 4. Foundational pillar theorems

Unconditional; RH appears only inside equivalences.

1. **The lattice skeleton is positive.** On lattice pairs the product atom never dominates the
   ratio atom (`productEnergy_le_ratioEnergy`, `skeletonEnergy_nonneg`); the crossing kernel is
   classified exactly, the atoms flipping only `{2,4}` and `{3,3}` (`latticeCrossing_inequality_iff`,
   `totalLatticeCrossingKernel_pos_iff`).
2. **Atom against pole, and the unpaid axis.** At the midpoint the atom exceeds the pole exactly for
   `n ∈ {2,3,4,5,7}`, and with the archimedean density exactly for the nine moduli
   `{2,3,4,5,7,8,9,11,13}` (`totalAntiDiagonalKernel_midpoint_pos_iff_mem`); for `n ≥ 23` the unpaid
   points lie within `≍ 2(1+Λ(n))/n` of the axes (`totalAntiDiagonalKernel_pos_imp_near_axis`).
3. **Each atom pays its own strip.** The micro-fold Harnack inequality pays a prime-power atom from
   the strip surplus of its own microstrip (`two_mul_primePowerShift_le_stripSurplus`); odd-part-only
   payment is false already at the first prime (`not_forall_oddPart_le_stripSurplus_logTwo`).
4. **Odd positivity past the first prime.** Every odd `C²_c` test supported in
   `[−181/500, 181/500]` has `Ẑ(F) ≥ (1/1000)∫F²`
   (`fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths`); the joint prime-2/3 strip
   costs are paid through `23/40` (`two_mul_primeTwoThreeShifts_le_stripSurplus_twentyThreeFortieths`),
   which is a strip-cost theorem, not full odd positivity.
5. **The global allocation condition.** The exact ledger of the odd form, with all terms and the
   plateau quantifier retained, is RH-equivalent (`riemannHypothesis_iff_globalIncidenceAllocation`),
   and its graded deficit at rate `2σ` bounds the width by `σ`.
6. **The translate calculus.** A prime-power tower reduces to a first-power term with its Euler
   discount (`towerCharge_le_firstAtomStrip`, `fullZeroForm_ge_primeOnlyLedger`); the envelope is
   attained by resonant trains (`exists_resonantTrain_coupling_fails`), and on two aligned towers the
   two envelopes add.
7. **The Chebyshev ledger.** The prime–polar part of the ledger is the signed pairing of the
   two-pole Chebyshev defect with the test's lag weight, equivalently the critical-scale receiver
   against its curvature (`sum_vonMangoldt_sub_polar_eq_chebyshev`,
   `sum_vonMangoldt_sub_polar_eq_criticalScalePrefix`), and the defect is a complete invariant of the
   source (`eq_of_lagPrefix_eq`).
8. **The spectral symbol.** That pairing is the frequency integral of one explicit signed symbol
   against the nonnegative density `|F̂|²`, so a pointwise floor on the symbol is a floor for every
   test (`chebyshev_pairing_eq_spectral`, `chebyshev_pairing_ge_of_symbol_ge`).
9. **The reflected-prime/polar ledger at every aperture.** `Ẑ(F)` equals pool plus crossing potential
   plus remainder minus the reflected-prime/polar cost, at every aperture, and that cost is the
   Chebyshev pairing (`fullZeroForm_eq_reflectedPrimePolarLedger`,
   `reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc`).
10. **The tower law reads the sign of the first power.** The Euler envelope of a prime tower and
    of its Liouville twin are both attained (resonant and alternating trains), and the two bounds
    differ by `2√p log p A(log p)` (`sub_one_mul_twistedTowerCharge_le`,
    `geoLagCharge_alternatingTrain_eq`): the translate calculus separates the primes from their
    parity twin, while every complete-period quadratic statistic of a divisor row is blind to sign
    flips (`completePeriod_parity_and_transHorizon_separation`).

---

## 5. Traps

| Trap | What is true instead |
|---|---|
| Taking the polar weight to be `sinh(x/2) sinh(y/2)` | The variance integral runs over all ordered pairs, the jump integral over `t > 0` only; per unordered pair the polar weight is `2 sinh(x/2) sinh(y/2)`. The thresholds below are for this normalization; with the factor `1` every classification changes. |
| Reading `k > 0` as positive conductance | On crossing pairs the gauge factor `M(x)M(y)` is negative; negative conductance is `k > 0` there. |
| Expecting the negative archimedean region to be a thin collar everywhere | Below the threshold `s₀ ∈ (log 5, log 6)` every crossing pair is negative, balanced or not; the collar picture holds only beyond `s₀`. |
| Expecting the reflected pairs `(−log a, log a)` to be negative for several small `a` | Only `a = 2`; from `a = 3` on the variance term wins. |
| Expecting the product atom to dominate on lattice pairs | It never does: `Λ(ab)/√(ab) ≤ Λ(b/a)/√(b/a)` on every lattice pair, with equality only at `a = 1`. |
| Expecting the atoms to flip no lattice sign | They flip exactly `{2,4}` and `{3,3}`: the archimedean kernel is negative there, the total kernel positive. |
| Treating the lattice skeleton as the form | The archimedean self-energy of a bump of width `w` at a lattice point is of order `w log(1/w)` and dominates the atom terms (of order `w`) as `w → 0`; lattice positivity is small-support positivity, not RH content. |
| Expecting many crossing atoms inside one dyadic window | At most one pair of consecutive powers of `2` and one of `3`, each of size `O(1/X)`; the ratio atoms inside the window are `O(1)`. |
| Treating `ratioAtom a b` as symmetric | It is defined for `a ∣ b` with `a < b`; `productAtom` is symmetric. |
| Deducing a sign for a continuum pair from the lattice | The anti-diagonal `\|x\| + y = log n` is a segment; its lattice points are the factorizations of `n`, and the dominance law speaks only about those. |
| Expecting the pole to pay a prime atom near the axes | The polar weight vanishes at both ends of every anti-diagonal; near an axis only same-side atoms and the gauge can pay. |
| Reading "the pole pays the atom at the midpoint" as payment of the atom | It is a pointwise comparison of weights per unit gauge at one point; the atom is a Dirac mass along the whole segment and the pole's share depends on the gauge profile along it. |
| Confusing the five moduli with the nine | Atom alone against the pole: `{2,3,4,5,7}`. Atom plus archimedean density against the pole: `{2,3,4,5,7,8,9,11,13}`; the density adds `8`, `9`, `11`, `13`, and `6` is paid although every `n ≤ 5` is not. |
| Summing the per-strip Harnack inequalities of mechanisms 30 and 35 | The strips `[log n − r, r]` are nested; the sum counts the inner pairs once per atom. One copy of the surplus pays a family only under an allocation (mechanisms 37 and 40), and the odd parts of the thin band exceed the whole surplus for large `r` (mechanisms 39 and 41). |
| Expecting the union allocation to cover every thin family | It fails already for `{23, 25}`: `2Λ(23)/√23 + 2Λ(25)/5 > λ₀`. The shell (mechanism 36) is needed there. |
| Reading the edge-tent obstruction as a failure of the form | On the edge tent every atom of the band is zero; what fails is the payment of the odd parts alone. The even parts cancel them. |
| Reading the ledger (mechanism 43) as a positivity theorem | It is an exact identity, and the condition it defines is equivalent to `Ẑ(F) ≥ 0` test by test. Its content is the shape of what must be paid, the costs and the pole, against what can pay, the pool, the crossing potential, the gains and the signed remainder. Positivity is proved only where a certificate bounds the remainder (the windows). |
| Reading the ledger's exact sign as the only target | Graded by the width it is a one-parameter family: a deficit at rate `2σ` at every aperture is the strip `½ + σ`, a deficit uniform in the aperture is RH. The exact allocation is the endpoint, not the statement. |
| Grading a bounded family of windows | The gradation quantifies over every aperture; windows with a bounded supremum of apertures stay worth zero in the width unit. |
| Expecting the tower law to estimate the prime side | Its envelope `z/(1−z)A(0)` is attained, by the resonant train on a multiplicative progression; only the first-power fold defect `A(0) − A(L)` is information. |
| Expecting the proper prime powers to carry their own obstruction | Beyond the Euler constants they do not: the whole tower of `p` is controlled by `A(log p)`, so the cost side reduces to the primes below the horizon. |
| Using the Möbius row as a test direction on a divisor lattice | On the resonant direction the divisor-lattice form of the Möbius row is `(Σ_{d ∣ q} μ_d)²A(0) = 0` for every `q ≠ 1`: the comb is blind exactly where the charges are largest. The trivial row gives the maximum `τ(q)²A(0)`. |
| Expecting oddness, edge decay or the strip structure to give a power saving in the floor | The sharp half-mass bound caps correlations beyond the aperture at `a(0)/2`, still a constant; on the edge tent the pole charge and the prime correlation are both `≍ e^{r}` with opposite signs. The rate-`1` obstruction is the prime–polar balance, and a sub-trivial rate is a fixed zero-free strip. |
| Treating the comb-energy reduction as a bound | Its nonpositive and polynomial premises fail on the stated test classes. Exponential comb energy can coexist with a small first-power charge; retain the overlap geometry and prime–polar compensation (mechanisms 50–51). |
| Expecting the comb second moment to preserve signed payment | Its exponential size is known. The missing estimate concerns the signed first-power prime–polar pairing, or a coherently subtracted remainder, not the raw aggregate. |
| Reading the Chebyshev ledger as the full Weil energy | It is the prime side against the pole plane; the archimedean density is not in it. A bound on the ledger is one input of the incidence ledger, not positivity of `Ẑ`. |
| Expecting the symbol criterion to supply a sign | It reduces the sign over all tests to one explicit function of frequency; at `ξ = 0` that function is the Chebyshev–Mertens comparison, a PNT-level difference. The reduction is exact, the floor is the open problem. |
| Bounding `E` by its size | `E` is unbounded because the atoms `log p` are; band tests read only its increments and curvature, so the usable estimates are approximation errors of the receiver across a band. |
| Expecting the single-tower envelope to bound an aligned pair of towers | On the bi-lattice train both towers resonate to the full fraction `(M − k)/M → 1` and the two Euler envelopes **add**; the prime-side bound is sharp already on two aligned towers. |

---

## 6. Questions the theory answers and the tools it builds

### 6.1 Questions

1. **On which pairs of points is the conductance negative?** On lattice pairs, exactly the classified
   ones; on the continuum, near the axes of the anti-diagonals and, below the threshold
   `s₀ ∈ (log 5, log 6)`, on every crossing pair.
2. **What in the arithmetic pays the negative part?** Locally, the strip surplus of each atom, the
   even part of the atom, Schur lending between origin, strip and middle; globally the question is
   whether one copy of the surplus pays every strip, which it does not without the pole and the
   prime–polar balance.
3. **What remains after every local payment?** One signed functional: the two-pole Chebyshev defect
   paired with the test's lag weight — equivalently one frequency integral of an explicit symbol.
4. **What does the ledger see of a source?** Everything: its defect determines it index by index;
   the test models differ from `ζ` by a prime count or a pole position.
5. **At what rate can the deficit be bounded?** The question the theory exists for: `Ce^{2σr}∫F²` at
   every aperture for one `σ < ½`, the strip `½ + σ`; the unconditional rate is `1`.

### 6.2 Tools

Built and reusable:

- *The pair kernel* `k = ω − atoms − polar weight`, read per unordered pair, with the lattice and
  anti-diagonal classifications.
- *The odd fold*, micro-fold Harnack inequalities, Schur rectangles and lending, curved and quartic
  surplus potentials.
- *Shared-surplus allocation*: nested strips, shells, chains, the light cone.
- *The exact ledger* of the odd form at every aperture, and its graded forms.
- *The translate calculus*: tower and bi-tower laws, resonant and bi-lattice trains, divisor-lattice
  Gram positivity.
- *The Chebyshev ledger*: lag Abel summation of every order, calibrations at any pole, source
  rigidity and realisation, the ideal source, the aperture–lag ladder and quadratic gap, the Euler
  comb payment law, the spectral symbol.

To be built:

- one budget paying all strips, the pole and the signed remainder on every odd compact profile;
- a lower bound on the signed spectral symbol in the frequency regions an aperture-`r` test can reach;
- a bounded Schur constant for the prime-ratio correlations (the replacement hypothesis);
- a signed estimate for the half-power cross-prime aggregate;
- the archimedean self-energy asymptotic of lattice bump profiles, with the origin and axis packets.

---

## 7. Open problems

1. **Pairs between lattice points.** Bound the anti-diagonal atom `Λ(n) n^{−1/2}` on a crossing pair
   `(x, y)` with `|x| + y = log n` that is not a lattice pair by the same-side atoms at the ratios
   `|x − y'| = log m` reachable from it and by the variance. This is the prime-side inequality of the
   open core; in a smeared gauge it is RH itself, so the problem is to find the sub-inequalities that
   are unconditional. The first prime window is paid through `181/500` for odd tests; the next
   question is a complete certificate at larger apertures, not another single-atom comparison. Mechanism 21 localizes it: for `n ≥ 23` the
   unpaid points lie within `L_n ≍ 2(1 + Λ(n))/n` of the axes.
2. **The atom against the pole, integrated.** For an odd gauge `M`, compare the atom mass
   `Λ(n) n^{−1/2} ∫₀^{log n} |M(−a) M(log n − a)| da` with the polar mass
   `∫₀^{log n} |M(−a) M(log n − a)| P(a) da` along the anti-diagonal. Determine the gauges for which
   the pole pays every atom outside the five moduli, and the amount the same-side atoms must pay for
   the five; the axis law says the answer depends on the decay of `M` at `0`. In the shifted
   ground-state gauge of `ArithmeticCriticalityTheory` the five moduli stay atom-dominated after
   integration against the collar kernel `m_a(x)m_a(log n − x)`, for every shift `a`
   (`collarPolarMass_lt_collarAtomMass_of_mem_atomDominatedModuli`); which prime powers outside the
   five the pole pays in the integrated sense is open.
3. **The archimedean part of the bump bridge.** For an odd gauge with `|M(x)| ≤ Ce^{−|x|}` and the even
   lattice profile `u_w = Σ_{a ∈ S} c_a(β((x − log a)/w) + β((x + log a)/w))`, `S ⊆ {a ≥ 2}`, the prime
   part of `J_M(u_w)` normalized by `w` tends to
   `∫β² (2 Σ_a c_a² M(log a) 𝒢(M)(log a) − 4 Σ_{a<b} c_a c_b M(log a)M(log b) netAtom(a,b)
   − 2 Σ_a c_a² M(log a)² netAtom(a,a))` (`tendsto_gaugePrimeJump_latticeBumpProfile_netAtom`); the
   last term is the crossing pair `(−log a, log a)` at the gap `log a²`. The general centre form is
   `tendsto_gaugePrimeJump_bumpProfile`. Open: the archimedean self-energy `≍ w log(1/w)` that
   dominates the limit, as an asymptotic.
4. **Lattice conductance at fixed width.** Combine mechanism 22 with the archimedean self-energy
   `≍ w log(1/w)` of a bump of width `w` into one statement about the conductance matrix of a
   lattice profile at fixed `w`, including the axis pairs `(0, log b)`. For the odd integer-log
   lattice train with labels from `2`, the complete Weil energy is calibrated against the singleton
   bump at an explicit polynomial resolution: with `j = 128(N+2)⁴(k+1)`,
   `|(Q(T_N) − 2E(c)Q(β_j))/M_j + 2I_N(c)| ≤ E(c)/(k+1)`, where `I_N` is the ratio-plus-reverse-ratio
   minus product incidence form (`fullEnergy_latticeTrain_uniform`, in
   `RHTower/ArithmeticIncidenceNarrowBumpBridge`). Open: the origin and axis packets, which an odd
   gauge reaches only through first jets, and the explicit self-energy asymptotic.
5. **Windows across scales.** The ratio atoms at `m ≥ 4` and the product atoms couple different
   dyadic windows; describe the coupling graph between windows and the size of its edges.
6. **The shared surplus between the light cone and the thin band (resolved in `LightConeSquareRootScaleAndSignedBandObstruction`).**
   (a) *Two-sided logarithmic capacity law:* any payable family of strips in `[r, 2(r − ε)]` has total weight at most
   `2 log(4/ε) + 84` (`sum_le_of_isPayableOddPartFamily`), while the geometric ratio-`6` chain achieves weight at least
   `(7/(10 log 6)) log(1/(12ε))` (`exists_payableOddPartFamily_log_lower_bound`).
   (b) *Exact square-root width `δ ≍ e^{−r}`:* Selberg sieve on prime shifts (`card_prime_lightConeBand_le_sieve`) and
   exponent injectivity on proper prime powers (`card_properPrimePow_lightConeBand_le`) widen the payable light cone to
   `δ ≤ (1/60)e^{−r}` for large `r` and uniformly to `δ ≤ c₀ e^{−r}` for all `r ≥ 2`
   (`eventually_sum_vonMangoldtAtom_lightConeBand_le_squareRoot`, `exists_squareRoot_lightCone_allocation`); conversely,
   for every `C ≥ 64000`, `T(r − 2Ce^{−r}, r)` frequently fails to pay the odd parts at width `δ = Ce^{−r}`
   (`frequently_lightConeBox_oddPart_sharing_fails_at_squareRoot`).
   (c) *Signed band obstruction:* the bipolar edge-dipole `bipolarEdgeTentOdd` makes every shift product in `thinBand r`
   pointwise nonnegative (`bipolarEdgeTentOdd_mul_shift_nonneg`) and strictlypositive on `thinBandCore r` while keeping
   `T(0, r) ≤ r`, so `Σ_{thinBand r} 2Λ(n)/√n ∫ F F(· + log n) > T(0, r)` for all large `r`
   (`exists_bipolarEdgeTent_signed_thinBand_sharing_fails`); the signed band charge is governed by the global identity
   `thinBand_signedCharge_eq_tsum_sub_complement`.

### Research topics

1. **Beyond the first prime window.** The variation inequality for all even profiles is proved past
   `log 2/2` (`181/500`, mechanisms 27–34). A larger window is not by itself progress toward the
   shared target: the strip payment of the atoms ends before `log 2` (mechanism 40) and does not
   globalize (mechanisms 39, 41), and what remains at every aperture is the even–odd balance of the
   atoms (mechanism 42). Up to `2/5` the prime atom
   is dominated by the strip surplus (mechanism 28), so the support is limited only by the
   archimedean potential `U_h^{off}` (mechanism 29). The archimedean odd sector alone is expected to stay positive
   up to `≈ 0.375` (second eigenvalue of the logarithmic Laplacian on an interval). Past `log 2/2` the fold of mechanism 23
   meets the atom on the anti-diagonal `a + b = log 2` of the inside pairs, where the folded
   conductance is `2M(a)M(b)(ω(|a − b|) − ω(a + b) + 4 sinh(a/2) sinh(b/2))` minus the atom.
2. **The integrated atom-versus-pole law** in the shifted ground-state gauge of
   `ArithmeticCriticalityTheory`: which `n` the pole pays in the integrated sense, and what the
   same-side atoms must pay for `n ∈ {2, 3, 4, 5, 7}`.
3. **The bump bridge.** `J_M + V_μ` on lattice bump profiles in terms of `netAtom` and the
   archimedean self-energy, so that the pair statements of §3 become statements about `Z`.
4. **Signed-gauge estimates.** The ground-state representation allows sign-changing
   gauges. Control its signed remainder and propagate local Harnack bounds across growing prime
   shifts without spending the same surplus twice.
5. **Selectivity audit.** For each theorem of §3, what it says for `ζ(s−a)ζ(s+a)` (shifted atoms
   and polar weight), for a Beurling system with an off-line zero, and for the Liouville twist.
   Done for two items: the odd windows below `log 2` separate `ζ` from the shifted pair through the
   pair's own screw kernel (`odd_window_selective`), and the tower law separates each prime tower
   from its Liouville twin at the first power (mechanism 46). Open for the strip-surplus and Schur
   certificates, which are nonselective in the window range (they hold for every weight with the
   same atom at `2`), and for the Chebyshev ledger, whose defect separates every source but whose
   estimates are so far size estimates.
6. **Paying the ledger past the windows.** The global condition of mechanism 43 is the target in
   its exact shape. Past `221/400` the costs of several relevant shifts must be paid at once from
   the pool, the gains and the remainder. The light cone (mechanism 38) pays the costs of the band
   `2r − 2δ ≤ log n < 2r` from the pool alone; mechanism 42 charges every other cost to its strip
   mass; what pays the strip masses is the remainder `∫ F²(−𝒲P + prime part)` on the strips, whose
   pointwise floor is the plateau potential of mechanism 27, together with the gains
   `2Λ(n)/√n ∫_{S_n} F²` (the atom pays its own strip at `t = 1`, mechanism 35). In the two-atom range `½ log 3 < r < log 2`, joint strip payment is available at `23/40`,
   but it is not positivity of the full form: the crossing potential, remainder and pole still
   have to be included. The three-shift Gram inequality
   `(A(log 2) + A(log 3))² ≤ 2A(0)(A(0) + A(log(3/2)))`
   (`FirstOpenWindowTwoAtomLaw`) identifies the free ratio lag that couples these costs. The scoreable
   form of the same problem is the **rate**: bound the ledger's deficit by `C e^{2σ r}∫F²` at every
   aperture for one `σ < ½`, which is the strip `½ + σ`, and by a constant times the mass for RH.
   The unconditional rate is `1`; the obstruction at that rate is the prime–polar balance, not the
   allocation of the surplus.
7. **The discount in the tower laws.** The envelopes of mechanisms 45, 46, 48 and 51 are attained —
   on one multiplicative progression, and on two at once, where the two Euler envelopes add — so the
   content is the fold defect `A(0) − A(log p)` and, for two towers, the ladder charge at the lag
   `log p`. Turn the reduced cost side of mechanism 47 — the primes below the horizon weighted by
   `log p/(p − 1)` and `√p log p/(p − 1)` against `A(log p)` — into a lower bound for the ledger at
   growing aperture, and determine which choices of the free weights on a squarefree divisor
   lattice (mechanism 49) make the subset form pay the first-power charges. The unit is the rate
   obtained in topic 6; the test models of `BiScaleUncertainty` decide selectivity, since the
   translate calculus itself is blind to the arithmetic of the shifts.
8. **The coherent comb remainder.** Raw polynomial comb control is ruled out by the sharp
   exponential family. Use the translation or resolvent law from Compensation Theory to identify
   the coherent part before squaring, and estimate its signed pairing with the test and the pole.
   State any remaining bound in the mass normalization, with its aperture exponent and errors.
   A bound for an average over tests does not by itself pay each test in the positivity criterion.
9. **Signed Chebyshev payment.** Use the exact lag Abel identity to bound the prime–polar
   difference together. Determine which autocorrelation constraints improve the pairing beyond
   a size estimate on `E`, and state whether the resulting bound is in the mass norm or requires
   a derivative or logarithmic Fourier weight. In spectral coordinates the target is a lower bound
   on `primeSymbol_N(ξ) − 2K_{2r}(2πξ)` where an aperture-`r` test can put its mass: the symbol is a
   prime Dirichlet polynomial against a polar kernel that pays only for `|ξ| ≤ 1/(8r)`, where odd
   tests carry cubically small mass, and at `ξ = 0` it is the Chebyshev–Mertens comparison
   `Σ_{n≤N}Λ(n)/√n − 4 sinh r`.

---

## 8. Principles

1. **Search the corpus before proving:** `scripts/formal_tools.py research "<query>"` from the repository root. The jump
   form, the gauge-free kernel, the half-line folding (`RHTower.CHMDReflectedPrimeSingularPart`,
   `RHTower.CHMDPrimeDivisorCuts`) and the density lemmas already exist.
2. **Name the pair.** Every statement says which pairs it concerns: same-side or crossing, lattice or
   continuum, which window.
3. **Separate density from atoms.** The archimedean kernel is a function, the prime part a sum of
   atoms; do not add a density value to an atom weight without a profile that gives both a
   dimension.
4. **Check the normalization against the Lean identity.** Pair weights are read off the proved
   decomposition `Z = J_M + V_μ`, with its exact ranges of integration, never off a docstring.
5. **Unconditional statements on honest classes.** Integers, real pairs, `C²` profiles with compact
   support; no hypothesis that restates the sign to be proved.
6. **Keep the other programmes in view.** The gauge and the generators live in the arithmetic
   criticality theory; the window tests in the square-root threshold programme; the half-line
   folding and the divisor cuts in CHMD; the sieve coordinates in the Bézout–valuation and
   trans-horizon programmes.
