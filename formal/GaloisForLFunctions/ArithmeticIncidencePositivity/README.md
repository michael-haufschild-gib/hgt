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

## The shared target: the sign of the critical arithmetic form

Seven programmes of this corpus work on one object. The Riemann Hypothesis is the nonnegativity of
one critical arithmetic form, and the form can be read in three equivalent faces:

- the **incidence face** (Arithmetic Incidence Positivity, `ArithmeticIncidencePositivity`):
  conductance by conductance, on pairs of points `(x, y)` of the logarithmic line, with the
  arithmetic edges indexed by divisibility (`a ∣ b`) and by products (`ab` a prime power), and the
  pole as the only positive source on crossing pairs;
- the **lag face** (Square-Root Threshold, `SquareRootThreshold`): one window inequality `P_v ≥ 0`
  per scale on the prime side, for the difference tests of one generic width, at height `T` and
  bandwidth `λ = log X / log T`;
- the **aperture face** (Arithmetic Criticality Theory, `ArithmeticCriticalityTheory`; Arithmetic
  Positivity Theory, `ArithmeticPositivityTheory`; the odd Weil-weight route OWU in `RHTower`): the
  ground-energy path `μ(A)` of the restricted Weil form at aperture `A`, which must never cross zero,
  and the gauge and source theories that would prove it.

The finite arithmetic programmes (Bézout–Valuation Incidence, `BezoutValuationIncidence`;
Trans-Horizon Incidence Mechanics, `TransHorizonIncidenceMechanics`; Bi-Scale Uncertainty,
`BiScaleUncertainty`) supply the additive, single-modulus structure of the integers that the three
faces cannot see on their own: Bézout relations, residue classes, pronic Gram matrices, horizon
mechanics, and the two-scale constraint of the integer grid against the hyperbolic weight.

**The mechanisms the shared target needs**, with the programme that owns each:

1. A prime-side inequality with no slack: payment of each anti-diagonal atom `Λ(n) n^{−1/2}` by
   same-side atoms and the variance, on all even profiles, in sign-changing gauges
   (`ArithmeticIncidencePositivity` with `ArithmeticCriticalityTheory`).
2. Single-modulus bilinear dispersion on the pronic Gram, through the reciprocity
   `{N/pq} ↔ p̄/q + q̄/p` (`BezoutValuationIncidence`).
3. A no-crossing law for the ground-energy path, equivalently the absence of a first negative lag
   for `ζ` (`ArithmeticCriticalityTheory`, `ArithmeticPositivityTheory` and OWU on the aperture side;
   `SquareRootThreshold` on the lag side).
4. A definite spectral realization with a prime modification as large as `S(T)` (the operator
   routes HF and CHMD in `RHTower`, on the complete sources of `ArithmeticPositivityTheory`).
5. A parity-breaking additive input at a single modulus (`TransHorizonIncidenceMechanics` with
   `BezoutValuationIncidence`; `BiScaleUncertainty` for the node criticality `log 4` against `log 6`).

**Criteria every contribution to the shared target must meet.**

- *Selectivity.* State what the result gives for `ζ(s−a)ζ(s+a)`, for a Beurling system with an
  off-line zero, and for the Liouville-twisted weight; a statement surviving all three is not
  about RH.
- *No family average.* One character, modulus one, shift zero.
- *Square-root precision beyond the diagonal*, at every scale rather than almost every.
- *Node criticality.* The mechanism distinguishes `log 4` from `log 6`; sampling-density and
  generic uncertainty arguments are excluded in advance.
- *Complete expression, no margin, no archimedean subsidy.* Mean, diagonal, mixed terms, Gamma and
  polar charges, endpoints and history are retained; a gain of size `log(1/w)` or `log M` at the
  archimedean place against a bounded prime cost is nonselective by construction.
- *Units.* Positivity is measured by the aperture `A` or the support through which the inequality
  holds for all profiles; cancellation by the exponent `θ` obtained or the lag `V` beyond which
  `P_v ≥ 0` is proved; localization by the depth `δ(n, R)` excluded below height `T(n, R)`.
  Identities, finite classifications and nonselective positivity count as zero in these units.
- *Calibration.* Reproduce the corresponding theorem over `F_q[T]`, or say why it cannot be done.

### This programme's role

AIP is the incidence face. It owns the pair geometry of the form: which pairs carry negative
conductance, how large it is, and what pays it. Its results are the exact inputs of mechanism 1:
the anti-diagonals and axis intervals the pole does not pay, the five moduli `{2,3,4,5,7}` and the
nine moduli `{2,3,4,5,7,8,9,11,13}`, the lattice pairs the atoms flip, and the window incidence of
the lag tests of `SquareRootThreshold`. It takes the gauge, the generators and the identity
`Z = J_M + V_μ` from `ArithmeticCriticalityTheory` and must hand back a profile-level inequality,
not a pointwise one. In the shared units every present theorem of AIP is infrastructure; its
progress begins with the first selective statement, listed first in §5.

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
anti-diagonal. Measured at the midpoint, where it is largest, it pays the atom `Λ(n)/√n` for every
`n ≥ 2` except `2, 3, 4, 5, 7`, and it pays the atom together with the archimedean density for every
`n ≥ 2` except `2, 3, 4, 5, 7, 8, 9, 11, 13`.

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
| Archimedean pair kernel | `k_arch(x,y) = ω(|x−y|) + 2 sinh(x/2) sinh(y/2)` | `archPairKernel` |
| Crossing symbol | `S(s) = cosh(s/2) − ω(s)` | `crossingSymbol` |
| Crossing threshold | the unique root `s₀ ∈ (log 5, log 6)` of `S = 1` | `crossingThreshold` |
| Ratio atom | `Λ(b/a)/√(b/a)` on the same-side pair `(log a, log b)`, `a ∣ b` | `ratioAtom` |
| Product atom | `Λ(ab)/√(ab)` on the crossing pair `(−log a, log b)` | `productAtom` |
| Net atom | `ratioAtom − productAtom` | `netAtom` |
| Lattice skeleton energies | `Σ_{a<b} (·)(c a − c b)²` with ratio, product or net atoms | `ratioEnergy`, `productEnergy`, `skeletonEnergy` |
| Dyadic window | `(X/2, 2X)` as a predicate on integers | `InDyadicWindow` |
| Two-bump window | `|log n − v| ≤ 2w` | `SquareRootThreshold.lagPrimeWindow` |
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

**Words.**
* **Pair `(x, y)`:** two points of the real line; **same-side** if `xy > 0`, **crossing** if
  `x < 0 < y`. For a crossing pair, `s = |x| + y` is the **sum** (the jump length) and `e = x + y`
  the **imbalance**; the pair is **balanced** when `e = 0`.
* **Conductance:** `M(x)M(y)k(x,y)` of the unordered pair; **negative conductance** on a crossing
  pair means `k(x,y) > 0`.
* **Lattice pair:** both points in `{± log a : a ≥ 1}`. The lattice pair `(log a, log b)` is a
  **ratio pair** when `a ∣ b`; `(−log a, log b)` is a **product pair** when `ab` is a prime power.
* **Tower:** the set `{p^i : i ≥ 0}` of powers of one prime. Product pairs live inside towers.
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
    exact order `2(1 + Λ(n))/n`.

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

---

## 4. Traps

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
| Deducing a sign for a continuum pair from the lattice | The anti-diagonal `|x| + y = log n` is a segment; its lattice points are the factorizations of `n`, and the dominance law speaks only about those. |
| Expecting the pole to pay a prime atom near the axes | The polar weight vanishes at both ends of every anti-diagonal; near an axis only same-side atoms and the gauge can pay. |
| Reading "the pole pays the atom at the midpoint" as payment of the atom | It is a pointwise comparison of weights per unit gauge at one point; the atom is a Dirac mass along the whole segment and the pole's share depends on the gauge profile along it. |
| Confusing the five moduli with the nine | Atom alone against the pole: `{2,3,4,5,7}`. Atom plus archimedean density against the pole: `{2,3,4,5,7,8,9,11,13}`; the density adds `8`, `9`, `11`, `13`, and `6` is paid although every `n ≤ 5` is not. |

---

## 5. Open problems

1. **Pairs between lattice points.** Bound the anti-diagonal atom `Λ(n) n^{−1/2}` on a crossing pair
   `(x, y)` with `|x| + y = log n` that is not a lattice pair by the same-side atoms at the ratios
   `|x − y'| = log m` reachable from it and by the variance. This is the prime-side inequality of the
   open core; in a smeared gauge it is RH itself, so the problem is to find the sub-inequalities that
   are unconditional. The smallest instance is the first prime window: a gauge argument for supports
   past `log 2 / 2`, paying the single atom `Λ(2)/√2`. Mechanism 21 localizes it: for `n ≥ 23` the
   unpaid points lie within `L_n ≍ 2(1 + Λ(n))/n` of the axes.
1′. **The atom against the pole, integrated.** For an odd gauge `M`, compare the atom mass
   `Λ(n) n^{−1/2} ∫₀^{log n} |M(−a) M(log n − a)| da` with the polar mass
   `∫₀^{log n} |M(−a) M(log n − a)| P(a) da` along the anti-diagonal. Determine the gauges for which
   the pole pays every atom outside the five moduli, and the amount the same-side atoms must pay for
   the five; the axis law says the answer depends on the decay of `M` at `0`.
2. **The bump bridge.** For an even profile built from bumps of width `w` at the points `± log a`,
   express the prime part of `J_M` in the limit `w → 0`, normalized by `w`, as a diagonal term
   `2 Σ_a c_a² M(log a) 𝒢_prime(M)(log a)` (the prime generator of the gauge) minus the pair term
   `4 Σ_{a<b} c_a c_b M(log a)M(log b) netAtom(a,b)`, and identify the archimedean self-energy
   `≍ w log(1/w)` that dominates the limit.
3. **Collar ratio.** The two ends of the sandwich differ by `sinh(s/2)/sinh(s/2 − 3e^{−3s/4})`;
   show that the collar end `c(s)`, the root of `P_s(c) = ω(s)`, satisfies
   `c(s) = ℓ(s)(1 + O(e^{−s}))`, and give the explicit second-order term.
3′. **The range `14 ≤ n ≤ 22`.** Mechanism 21 needs the quarter point paid, proved for `n ≥ 23`;
   determine the exact set of `n` for which the quarter point is paid, and describe the unpaid set
   when the midpoint is paid but the quarter point is not.
4. **Lattice conductance at fixed width.** Combine mechanism 22 with the archimedean self-energy
   `≍ w log(1/w)` of a bump of width `w` into one statement about the conductance matrix of a
   lattice profile at fixed `w`, including the axis pairs `(0, log b)`.
5. **Parity.** Which complete-period quadratic forms of the sieve theory (variance, Bézout
   successor form, two-lag covariances) are even functions of the Selberg coordinates, hence
   invariant under every sign character on the coordinates, while the trans-horizon response is
   not; exhibit the pair of rows this separates.
6. **Windows across scales.** The ratio atoms at `m ≥ 4` and the product atoms couple different
   dyadic windows; describe the coupling graph between windows and the size of its edges.

### Research topics toward the shared target

1. **The first selective statement.** The variation inequality for all even profiles with support
   between `7/25` (mechanism 23) and `log 2/2`, and past `log 2/2`, paying the atom `Λ(2)/√2` without
   the pole-free margin; the unit is the support reached. Past `log 2/2` the fold of mechanism 23
   meets the atom on the anti-diagonal `a + b = log 2` of the inside pairs, where the folded
   conductance is `2M(a)M(b)(ω(|a − b|) − ω(a + b) + 4 sinh(a/2) sinh(b/2))` minus the atom.
2. **The integrated atom-versus-pole law** in the shifted ground-state gauge of
   `ArithmeticCriticalityTheory`: which `n` the pole pays in the integrated sense, and what the
   same-side atoms must pay for `n ∈ {2, 3, 4, 5, 7}`.
3. **The bump bridge.** `J_M + V_μ` on lattice bump profiles in terms of `netAtom` and the
   archimedean self-energy, so that the pair statements of §3 become statements about `Z`.
4. **Sign-changing gauges.** A ground-state representation for forms with negative conductances on
   an arithmetic set of pairs, and a Harnack-type propagation across `log 2, log 3, …`
   (mechanism 1, with `ArithmeticCriticalityTheory`).
5. **Selectivity audit.** For each theorem of §3, what it says for `ζ(s−a)ζ(s+a)` (shifted atoms
   and polar weight), for a Beurling system with an off-line zero, and for the Liouville twist.

---

## 6. Principles

1. **Search the corpus before proving:** `../scripts/formal_tools.py research "<query>"`. The jump
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
