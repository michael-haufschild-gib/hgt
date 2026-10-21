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

**Why one theory.** Each existing layer stops where the corpus proves it stops. Sieve and bilinear
methods see the additive structure of `ℕ` only after averaging over a family, and below half
damping no sign-blind datum decides the receiver. Multiplicative, spectral and explicit-formula
methods hold verbatim for Beurling systems with off-line zeros. Dirichlet-form and criticality
identities hold for every even positive kernel, and positivity on restricted families is paid by an
archimedean gain that is absent on the RH-complete cone. A closing theorem must at once see both
operations of `ℕ` at a single modulus, carry a sign structure (one negative square, the pole plane,
the signs of the Möbius row), and be resolved at the zero spacing, at square-root precision at every
scale. No existing field has its basic objects built with all three; the seven programmes build
them.

**The mechanisms the shared target needs**, with the programme that owns each:

1. A prime-side inequality with no slack: payment of each anti-diagonal atom `Λ(n) n^{−1/2}` by
   same-side atoms and the variance, on all even profiles, in sign-changing gauges, with a
   Harnack-type propagation across the prime shifts `log 2, log 3, …`
   (`ArithmeticIncidencePositivity` with `ArithmeticCriticalityTheory`).
2. Single-modulus bilinear dispersion on the pronic Gram, through the reciprocity
   `{N/pq} ↔ p̄/q + q̄/p`, for the actual Möbius or prime row; it reduces exactly to the
   single-modulus statistics `Σ_p |Λ_p(c')|/p` of that row (`BezoutValuationIncidence`).
3. A no-crossing law for the ground-energy path, equivalently the absence of a first negative lag
   for `ζ` (`ArithmeticCriticalityTheory`, `ArithmeticPositivityTheory` and OWU on the aperture side;
   `SquareRootThreshold` on the lag side).
4. A definite spectral realization with a prime modification as large as `S(T)`: a Hilbert space
   and a self-adjoint operator whose spectral measure is the critical-zero measure, with
   non-unit-modulus Euler factors (`ArithmeticPositivityTheory` for the source class and the
   realization problem; the operators of the routes HF, CHMD and Connes–Consani–Moscovici in
   `RHTower`). Every certificate of positivity is the critical-zero measure, so this is mechanism 3
   seen from the other side.
5. A sign-reading additive input at a single modulus: below half damping a bound on the receiver
   must read the signs of the coefficients, through first-order data at prime moduli (`k ↦ pk`) or
   odd-degree additive moments (`k ↦ k + v`) (`TransHorizonIncidenceMechanics` with
   `BezoutValuationIncidence`; `BiScaleUncertainty` for the node criticality `log 4` against
   `log 6`).

**Criteria every contribution to the shared target must meet.**

- *Selectivity.* State what the result gives for `ζ(s−a)ζ(s+a)`, for a Beurling system with an
  off-line zero, and for the Liouville-twisted weight; a statement surviving all three is not
  about RH (test models: `BiScaleUncertainty`).
- *No family average.* One character, modulus one, shift zero.
- *Square-root precision beyond the diagonal.* Prime sums of length at least the height,
  controlled beyond the mean-value regime: one inequality per window at every scale on the lag
  family, `θ = 2` on the Gram.
- *Every scale, not almost every.* A statement about an exceptional set, a proportion or a typical
  member is infrastructure (the every-height problem: `SquareRootThreshold`).
- *Node criticality.* The mechanism distinguishes `log 4` from `log 6`; sampling-density and
  generic uncertainty arguments are excluded in advance.
- *Signs read.* Below half damping the mechanism uses first-order data at prime moduli or
  odd-degree additive moments; magnitude, two-point and translated-moment data are blind, since the
  parity pairs exist at every damping `ε ≤ 1/2`.
- *Complete expression, no margin, no archimedean subsidy.* Mean, diagonal, mixed terms, Gamma and
  polar charges, endpoints and history are retained; a gain of size `log(1/w)` or `log M` at the
  archimedean place against a bounded prime cost is nonselective by construction.
- *Units.* Positivity is measured by the aperture `A` or the support through which the inequality
  holds for all profiles; cancellation by the exponent `θ` obtained or the lag `V` beyond which
  `P_v ≥ 0` is proved; localization by the depth `δ(n, R)` excluded below height `T(n, R)` and by
  the visibility lag `V₀(w, η, δ₀)`; damping by the smallest `ε` at which the receiver is bounded.
  Identities, finite classifications and nonselective positivity count as zero in these units.
- *Calibration.* Reproduce the corresponding theorem over `F_q[T]`, or say why it cannot be done
  (`BiScaleUncertainty`).
- *Pairs.* Every invisibility theorem comes with a visibility witness, every identity with the
  estimate it enables or the sharp boundary it proves, every obstruction with its replacement
  hypothesis proved sufficient.

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
   the five; the axis law says the answer depends on the decay of `M` at `0`. In the shifted
   ground-state gauge of `ArithmeticCriticalityTheory` the five moduli stay atom-dominated after
   integration against the collar kernel `m_a(x)m_a(log n − x)`, for every shift `a`
   (`collarPolarMass_lt_collarAtomMass_of_mem_atomDominatedModuli`); which prime powers outside the
   five the pole pays in the integrated sense is open.
2. **The bump bridge.** For an even profile built from bumps of width `w` at the points `± log a`,
   express the prime part of `J_M` in the limit `w → 0`, normalized by `w`, as a diagonal term
   `2 Σ_a c_a² M(log a) 𝒢_prime(M)(log a)` (the prime generator of the gauge) minus the pair term
   `4 Σ_{a<b} c_a c_b M(log a)M(log b) netAtom(a,b)`, and identify the archimedean self-energy
   `≍ w log(1/w)` that dominates the limit.
3. **Collar ratio (settled).** For `s ≥ 4 log 2` the collar is exactly `(0, c) ∪ (s − c, s)` with
   `P_s(c) = ω(s)`, `ℓ ≤ c ≤ 2ℓ` and `|c − ℓ − (coth(s/2)/2)ℓ²| ≤ 8ℓ³` (`collarEnd_second_order`);
   the second-order coefficient is exact, `(coth(s/2)/2)ℓ(s) = e^{−s}/(1 − e^{−s})³`
   (`half_coth_mul_collarInnerEnd`), so `|c/ℓ − 1 − e^{−s}/(1 − e^{−s})³| ≤ 37e^{−2s}` and
   `c(s)/ℓ(s) = 1 + e^{−s} + O(e^{−2s})` (`collarEnd_ratio`).
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

1. **Beyond the first prime window.** The variation inequality for all even profiles is proved past
   `log 2/2` (`181/500`, mechanisms 27–34); the unit is the support reached. Up to `2/5` the prime atom
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
