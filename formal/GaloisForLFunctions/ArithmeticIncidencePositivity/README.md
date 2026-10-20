# Arithmetic Incidence Positivity (`GaloisForLFunctions.ArithmeticIncidencePositivity`)

**One question.** The zero form of `ζ` is a jump form whose conductance between two points is a
gauge factor times a kernel built from the archimedean density and the prime atoms. On which pairs
of points is that conductance negative, how large is the negative part, and what in the arithmetic
of the integers pays it?

Arithmetic incidence positivity (AIP) is a theory of *pairs*. Where the arithmetic criticality theory
treats the critical form as one quadratic functional of a profile, AIP reads it conductance by
conductance, as a weighted graph on the real line whose arithmetic edges are indexed by the
incidence relations of the integers: the pair of points `(log a, log b)` is coupled through the ratio
`b/a` when `a ∣ b`, and the pair `(−log a, log b)` through the product `ab`. The sign problem of the
critical form is the sign problem of this graph. Every statement in AIP is unconditional and names the
pairs it concerns.

---

## 1. Why: motivation

**The zero form is a jump form.** In an odd gauge `ω`, positive on `(0, ∞)`, with test coordinate
`M = Φω` and `μ = M sinh(x/2)`, the zero form of an even profile `u` is

    Z(Φ(ωu)) = ∫ dm(t) ∫ M(x)M(x+t)(u(x) − u(x+t))² dx + ∫∫ μ(x)μ(y)(u(x) − u(y))² dx dy,

where `dm` is the jump measure: the archimedean density `ω(t) = e^{−t/2}/(1 − e^{−2t})` on `(0, ∞)`
plus the prime atoms `Λ(n) n^{−1/2}` at `t = log n` (`ArithmeticCriticalityTheory`,
`zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy`). Both terms carry the factor `M(x)M(y)`:
the conductance of the pair `(x, y)` per unit `M ⊗ M` is the **gauge-free kernel**

    k(x, y) = dm(|x − y|) + sinh(x/2) sinh(y/2).

RH is the nonnegativity of this jump form on every even profile, in any one such gauge.

**Same side, across.** For `M` odd and positive on `(0, ∞)` the gauge factor `M(x)M(y)` is positive
when `x` and `y` lie on the same side of the origin and negative when they lie across it. A same-side
pair has `k > 0` (both terms positive): positive conductance. A crossing pair `x < 0 < y` has
negative conductance exactly where `k > 0`, that is where the jump measure at the distance `|x| + y`
exceeds the product `sinh(|x|/2) sinh(y/2)`. The negative conductances of the form are therefore
confined to the crossing pairs, on the prime anti-diagonals `|x| + y = log n` (an atom of infinite
density) and on the set where the archimedean density `ω(|x| + y)` beats `sinh(|x|/2) sinh(y/2)`.

**Incidence.** On the logarithmic lattice `{± log a}` the two kinds of pairs are arithmetic
relations. The same-side pair `(log a, log b)` carries an atom iff `b/a` is a prime power: `a` divides
`b` with prime-power quotient. The crossing pair `(−log a, log b)` carries an atom iff `ab` is a
prime power, which forces `a` and `b` to be powers of one prime. So the prime conductances of the
form are the divisibility relations of the integers read in two ways, by ratio and by product. The
field's thesis is that the sign of the critical form should be understood through this incidence
structure: which pairs of integers carry negative conductance, how it compares with the positive
conductance on the same pair, and how the window structure of the primes enters.

**Polar compensation.** The pole of `ζ` enters the form as the variance term; per unit gauge its
weight on the crossing pair `(−a, s − a)` is the **polar weight** `sinh(a/2) sinh((s − a)/2)`. It
is the only positive source on crossing pairs. It pays the archimedean crossing density `ω(s)`
pointwise everywhere except on a collar of the two axes of length `O(e^{−3s/4})`, and it vanishes at
the axes, so it never pays a prime atom near the ends of its anti-diagonal. Measured at the midpoint,
where it is largest, it pays the atom `Λ(n)/√n` for every `n ≥ 2` except the ten moduli
`2, 3, 4, 5, 7, 9, 11, 13, 17, 19`, whose atoms exceed the polar weight on the whole anti-diagonal.

**Where the difficulty sits.** The pair picture separates what is already decided from what is not.
On lattice pairs the negative atom is never larger than the positive atom on the same pair, and
the negative archimedean conductance is carried by finitely many pairs. In the continuum the pole
pays the archimedean density off the collars. What remains is the prime atom near the axes of its
anti-diagonal, for all `n`, and along the whole anti-diagonal for the ten moduli: it must be paid by
same-side atoms at other ratios and by the gauge, with no slack to lose.

---

## 2. What: objects and language

The objects come from `RHTower` and `ArithmeticCriticalityTheory`. Do not redefine them.

| Object | Meaning | Lean |
|---|---|---|
| Archimedean density | `ω(t) = e^{−t/2}/(1 − e^{−2t})`, `t > 0` | `RHTower.archLevyDensity` |
| Prime atom | `Λ(n)/√n` at `t = log n`, `n ≥ 2` | `RHTower.vonMangoldtAtom` |
| Signed jump energy | `J_M(u) = ∫ dm(t) ∫ M(x)M(x+t)(u(x) − u(x+t))²` | `ArithmeticCriticalityTheory.signedJumpEnergy` |
| Variance energy | `∫∫ (u(x) − u(y))² μ(x)μ(y)` | `ArithmeticCriticalityTheory.varianceEnergy` |
| Archimedean pair kernel | `k_arch(x,y) = ω(|x−y|) + sinh(x/2) sinh(y/2)` | `archPairKernel` |
| Crossing symbol | `S(s) = cosh(s/2) − 2 ω(s)` | `crossingSymbol` |
| Crossing threshold | the unique root `s₀ ∈ (2 log 3, 4 log 2)` of `S` | `crossingThreshold` |
| Ratio atom | `Λ(b/a)/√(b/a)` on the same-side pair `(log a, log b)`, `a ∣ b` | `ratioAtom` |
| Product atom | `Λ(ab)/√(ab)` on the crossing pair `(−log a, log b)` | `productAtom` |
| Net atom | `ratioAtom − productAtom` | `netAtom` |
| Lattice skeleton energies | `Σ_{a<b} (·)(c a − c b)²` with ratio, product or net atoms | `ratioEnergy`, `productEnergy`, `skeletonEnergy` |
| Dyadic window | `(X/2, 2X)` as a predicate on integers | `InDyadicWindow` |
| Two-bump window | `|log n − v| ≤ 2w` | `SquareRootThreshold.lagPrimeWindow` |
| Polar weight | `sinh(a/2) sinh((s−a)/2)` on the crossing pair `(−a, s−a)` | `crossingPolarWeight` |
| Off-collar region | crossing pairs with `k_arch ≤ 0` | `offCollar` |
| Collar of an anti-diagonal | `{a ∈ (0,s) : k_arch(−a, s−a) > 0}` | `antiDiagonalCollar` |
| Payment scale | `Λ(n)/√n` over `sinh²(log n / 4)` | `polarPaymentScale` |
| Ten moduli | `{2, 3, 4, 5, 7, 9, 11, 13, 17, 19}` | `atomDominatedModuli` |
| Collar ends | `ℓ(s) = 2ω(s)/sinh(s/2)`, `L(s) = 2ω(s)/sinh(s/2 − 6e^{−3s/4})` | `collarInnerEnd`, `collarOuterEnd` |
| Total lattice crossing kernel | `k_arch(−log a, log b) + Λ(ab)/√(ab)` | `totalLatticeCrossingKernel` |
| Total anti-diagonal kernel | `ω(log n) + Λ(n)/√n − P(a)` on the anti-diagonal of `n` | `totalAntiDiagonalKernel` |
| Thirteen moduli | `{2, …, 9, 11, 13, 17, 19, 23}` | `totalDominatedModuli` |
| Unpaid set of a level | `{a ∈ (0,s) : P_s(a) < E}` | `unpaidSet` |
| Level of `n` | `E_n = ω(log n) + Λ(n)/√n` | `antiDiagonalLevel` |
| Unpaid ends | `ℓ = 2E/sinh(s/2)`, `L = 2E/sinh(s/2 − min(s/4, 2E/sinh(s/4)))` | `unpaidInnerEnd`, `unpaidOuterEnd` |

**Words.**
* **Pair `(x, y)`:** two points of the real line; **same-side** if `xy > 0`, **crossing** if
  `x < 0 < y`. For a crossing pair, `s = |x| + y` is the **sum** (the jump length) and `e = x + y`
  the **imbalance**; the pair is **balanced** when `e = 0`.
* **Conductance:** `M(x)M(y)k(x,y)`; **negative conductance** on a crossing pair means `k(x,y) > 0`.
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
  `sinh(|x|/2) sinh(y/2)`. **Payment** means that the polar weight on a pair is at least the negative
  conductance on it; the **payment scale** of `n` is the ratio of the atom to the largest polar weight
  on its anti-diagonal.

---

## 3. How: mechanisms

### The archimedean kernel

1. **Product-to-sum.** `sinh(x/2) sinh(y/2) = (cosh((x+y)/2) − cosh((x−y)/2))/2`, so for `x < y`
   `k_arch(x,y) = ω(y−x) + (cosh((x+y)/2) − cosh((y−x)/2))/2` (`archPairKernel_eq_of_lt`). On
   same-side pairs both terms of `k_arch` are positive (`archPairKernel_pos_of_sameSide`).
2. **Sign law.** For `x < y`, `k_arch(x,y) > 0 ⟺ cosh((x+y)/2) > S(y−x)` (`archPairKernel_pos_iff`).
   A crossing pair has negative conductance iff its imbalance is large enough for its sum: the
   symbol `S(s)` is the balanced value of the kernel-defining threshold.
3. **The symbol is monotone and crosses `1` once.** `S` is strictly increasing on `(0, ∞)`
   (`cosh(s/2)` grows, `ω` decays), `S(2 log 3) = 119/120` and `S(4 log 2) = 3311/2040`, so `S`
   has a unique root `s₀`, the crossing threshold (`crossingThreshold_mem`,
   `crossingSymbol_crossingThreshold`). Since `cosh ≥ 1`: every crossing pair with sum below `s₀`
   has negative conductance (`archPairKernel_pos_of_lt_threshold`); at the threshold exactly the
   balanced pair is neutral (`archPairKernel_pos_iff_of_eq_threshold`); beyond it balanced pairs
   have positive conductance (`archPairKernel_balanced_neg_iff`) and only the unbalanced ones,
   close to an axis, remain negative.
4. **Collar bound.** For `s ≥ 4 log 2` a negative crossing pair has `min(|x|, y) < 6 e^{−3s/4}`
   (`min_lt_of_archPairKernel_pos`). Two estimates: near an axis,
   `c sinh(s/4) ≤ cosh(s/2) − cosh(s/2 − c) < 2ω(s)` with `c = min(|x|,y)`; for a balanced-type pair,
   `cosh(s/2) − cosh(s/4) ≥ 3s²/32` beats `2ω(s) ≤ 128/255`.

### The lattice

5. **Reflection law.** The reflected lattice pair `(−log a, log a)` has sum `2 log a` and imbalance
   `0`; it has negative archimedean conductance iff `2 log a < s₀`, that is iff `a ∈ {2, 3}`
   (`archPairKernel_reflection_pos_iff`).
6. **Closed form on lattice crossing pairs.**
   `k_arch(−log a, log b) = (4(ab)² − (a−1)(b−1)((ab)²−1)) / (4√(ab)((ab)²−1))`
   (`archPairKernel_neg_log_log`), so the conductance is negative iff
   `(a−1)(b−1)((ab)²−1) < 4(ab)²` (`archPairKernel_neg_log_log_pos_iff`). The axis pairs `a = 1` or
   `b = 1` always qualify; for `a, b ≥ 2` exactly the five pairs `{2,2}, {2,3}, {2,4}, {2,5}, {3,3}`
   do (`archPairKernel_neg_log_log_pos_iff_of_two_le`), two of them by one unit: `396 < 400` and
   `320 < 324`.
7. **Tower lemma.** If `ab` is a prime power, `a = p^i` and `b = p^j` for one prime `p`
   (`exists_prime_pow_of_isPrimePow_mul`); then `b/a = p^{j−i}` is a prime power as well, and
   `Λ(ab) = Λ(b/a) = log p`.
8. **Dominance law.** For `1 ≤ a < b`, `productAtom a b ≤ ratioAtom a b`
   (`productAtom_le_ratioAtom`): the crossing atom of a lattice pair is never larger than the
   same-side atom of the same pair, because `√(ab) ≥ √(b/a)`. Strict for `a ≥ 2` and `ab` a prime
   power (`productAtom_lt_ratioAtom`); equality at `a = 1`, where the two pairs `(0, log b)` and
   `(0, log b)` coincide (`productAtom_one_left`). Hence the prime skeleton
   `Σ_{a<b} netAtom(a,b)(c a − c b)²` of a lattice profile is a nonnegative graph Laplacian
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
    `k_arch = ω(s) − P_s(a)` with the polar weight `P_s(a) = sinh(a/2) sinh((s−a)/2)
    = (cosh(s/2) − cosh(s/2 − a))/2` (`archPairKernel_antiDiagonal_eq`, `crossingPolarWeight_eq`).
    `P_s` is symmetric under `a ↦ s − a`, vanishes at both ends, and has its maximum `sinh²(s/4)` at
    the midpoint (`crossingPolarWeight_midpoint`, `crossingPolarWeight_le_midpoint`).
13. **Pointwise payment off the collar.** Where `k_arch(x, y) ≤ 0` on a crossing pair,
    `ω(y − x) ≤ sinh(|x|/2) sinh(y/2)`; in a gauge with `M(x)M(y) ≤ 0` across the origin the
    archimedean crossing conductance is at most the variance conductance on that pair, hence for
    every profile the archimedean crossing energy over the off-collar region is at most the
    variance energy over it (`lintegral_archCrossingDensity_offCollar_le`). The archimedean
    negativity that survives the pole lives on the collar.
14. **Collar measure.** For `s ≥ 4 log 2` the collar of the anti-diagonal lies within `6 e^{−3s/4}`
    of its two ends (`antiDiagonalCollar_subset`); its length is at most `12 e^{−3s/4}`
    (`volume_antiDiagonalCollar_le`), and the archimedean conductance the pole leaves unpaid on the
    anti-diagonal has total mass at most `12 ω(s) e^{−3s/4}` (`lintegral_antiDiagonalCollar_le`).
15. **Small and large anti-diagonals.** For `2 ≤ n ≤ 9` the whole anti-diagonal `|x| + y = log n`
    has negative archimedean conductance, because `log 9 = 2 log 3 < s₀`
    (`archPairKernel_antiDiagonal_pos_of_le_nine`); for `n ≥ 16` only the end collars of length
    `< 6 n^{−3/4}` do (`antiDiagonal_collar_of_sixteen_le`).
16. **Axis law.** The polar weight tends to `0` at the ends of every anti-diagonal
    (`tendsto_crossingPolarWeight_zero`): no pole mass is available against a prime atom near the
    axes.
17. **Payment scale.** The ratio of the atom to the midpoint polar weight is
    `4Λ(n)/(√n − 1)²` (`polarPaymentScale_eq`), at most `16 log n / n` for `n ≥ 4`
    (`polarPaymentScale_le`).
18. **Exact classification.** `(√n − 1)² < 4Λ(n)` iff `n ∈ {2, 3, 4, 5, 7, 9, 11, 13, 17, 19}`
    (`sqrt_sub_one_sq_lt_four_vonMangoldt_iff`): the primes up to `19` and the squares `4`, `9`. For
    these the atom exceeds the polar weight at every point of the anti-diagonal
    (`crossingPolarWeight_lt_vonMangoldtAtom`, `antiDiagonal_total_pos_of_mem`); for every other
    `n ≥ 2` the pole pays the atom at the midpoint (`vonMangoldtAtom_le_crossingPolarWeight_midpoint`).
    Inputs: `Λ(p^k) = log p`; `log r ≤ sinh(log r)` on fourth roots for `p ≥ 23`
    (`four_mul_log_le_sqrt_sub_one_sq`); `log p ≤ p − 1` for `k ≥ 2`; eight explicit comparisons.
19. **Collar sandwich.** From `a sinh(s/2 − a) ≤ 2P_s(a) ≤ a sinh(s/2)` on `0 ≤ a ≤ s/2`
    (`le_two_mul_crossingPolarWeight`, `two_mul_crossingPolarWeight_le`; the upper bound is
    `sinh a − a ≤ cosh a − 1`): for `s ≥ 4 log 2`,
    `(0, ℓ) ∪ (s − ℓ, s) ⊆ collar ⊆ (0, L) ∪ (s − L, s)` (`innerEnds_subset_antiDiagonalCollar`,
    `antiDiagonalCollar_subset_outer`), with `ℓ(s) = 4e^{−s}/((1 − e^{−2s})(1 − e^{−s}))`
    (`collarInnerEnd_eq`), `4e^{−s} ≤ ℓ(s) ≤ (256/239) · 4e^{−s}`, and
    `L = ℓ · sinh(s/2)/sinh(s/2 − 6e^{−3s/4})` (`collarOuterEnd_eq`). The collar has exact order
    `4e^{−s}` at each axis; the unpaid archimedean mass is at most `2ω(s)L(s)`
    (`lintegral_antiDiagonalCollar_le_outer`), of order `8e^{−3s/2}`.
21. **The pole against the whole anti-diagonal.** On the anti-diagonal of `n` the total kernel
    `ω(log n) + Λ(n)/√n − P(a)`, with `ω(log n) = n²/((n² − 1)√n)` (`archLevyDensity_log_nat`), is
    smallest at the midpoint, where it equals `(4n²/(n² − 1) + 4Λ(n) − (√n − 1)²)/(4√n)`
    (`totalAntiDiagonalKernel_midpoint_eq`). It is positive everywhere iff
    `(√n − 1)² < 4n²/(n² − 1) + 4Λ(n)`, and for `n ≥ 2` this holds iff
    `n ∈ {2, …, 9, 11, 13, 17, 19, 23}` (`total_midpoint_inequality_iff`,
    `totalAntiDiagonalKernel_pos_forall_iff`): every modulus up to `9` and the primes `11` to `23`.
    For all other `n` the pole pays the whole negative conductance at the midpoint
    (`totalAntiDiagonalKernel_midpoint_nonpos`). The last prime is `23` (`14.4` against `16.5`);
    `29` is paid (`19.2` against `17.5`); from `30` on, `4x²/(x² − 1) + 4 log x ≤ (√x − 1)²`
    (`four_sq_div_add_four_log_le`, through `log r ≤ sinh(log r)` on the fourth root).
22. **Unpaid axis intervals.** The polar weight increases from the axis to the midpoint
    (`crossingPolarWeight_mono`), so the unpaid set of a level `E` is two axis intervals once the
    quarter point is paid, and the bounds of mechanism 19 sandwich its ends:
    `(0, ℓ) ∪ (s − ℓ, s) ⊆ unpaid ⊆ (0, L) ∪ (s − L, s)` with `ℓ = 2E/sinh(s/2)` and
    `L = 2E/sinh(s/2 − min(s/4, 2E/sinh(s/4)))` (`innerEnds_subset_unpaidSet`,
    `unpaidSet_subset_outer`, ratio `unpaidOuterEnd_eq`). For the full level
    `E_n = ω(log n) + Λ(n)/√n` of the anti-diagonal of `n`, the inner end is
    `ℓ_n = 4(n²/(n² − 1) + Λ(n))/(n − 1)` (`unpaidInnerEnd_level_eq`), between `4/(n − 1)` and
    `4(1 + 1/(n² − 1) + log n)/(n − 1)`, and the quarter point is paid for every `n ≥ 41`
    (`antiDiagonalLevel_le_quarter`, by the fourth-root bound and the polynomial
    `4.003r + 8(r² − 1) ≤ r⁵ − r⁴ − r² + r` for `r ≥ 2.53`). Hence for `n ≥ 41` the pole pays the
    whole negative conductance of the anti-diagonal of `n` except on two axis intervals of length
    between `ℓ_n` and `L_n` (`unpaid_level_subset_outer`, `totalAntiDiagonalKernel_pos_imp_near_axis`):
    the prime obstruction on the anti-diagonal of `n` is confined to a neighbourhood of the axes
    of exact order `4(1 + Λ(n))/n`.

### The lattice with its atoms

20. **Total lattice crossing law.** For `a, b ≥ 2` the total crossing kernel
    `k_arch(−log a, log b) + Λ(ab)/√(ab)` is positive exactly on the five pairs of mechanism 6
    (`totalLatticeCrossingKernel_pos_iff`): the prime atoms flip no lattice sign
    (`totalLatticeCrossingKernel_pos_iff_archPairKernel_pos`). In closed form the atom changes the
    condition to `(a−1)(b−1)(N²−1) > 4N² + 4Λ(N)(N²−1)`, `N = ab`; the three tower regimes are
    `p = 2` with `(a−1)(b−1) ≥ 7`, `N ≥ 16`, `p = 3` with `(a−1)(b−1) ≥ 16`, `N ≥ 27`, and `p ≥ 5`
    with `(a−1)(b−1) ≥ (p−1)²`, `N ≥ 25` and `log p ≤ 3 log 2 + p/8 − 1`
    (`lattice_atom_inequality`). The near miss is `{2, 8}`: `7` against `4 + 4/255 + 4 log 2 < 6.79`
    (`totalLatticeCrossingKernel_two_eight_nonpos`).

---

## 4. Traps

| Trap | What is true instead |
|---|---|
| Reading `k > 0` as positive conductance | On crossing pairs the gauge factor `M(x)M(y)` is negative; negative conductance is `k > 0` there. |
| Expecting the negative archimedean region to be a thin collar everywhere | Below the threshold `s₀ ∈ (2 log 3, 4 log 2)` every crossing pair is negative, balanced or not; the collar picture holds only beyond `s₀`. |
| Expecting the reflected pairs `(−log a, log a)` to be negative for all small `a` | Only `a = 2, 3`; from `a = 4` on the variance term wins. |
| Expecting the product atom to dominate on lattice pairs | It never does: `Λ(ab)/√(ab) ≤ Λ(b/a)/√(b/a)` on every lattice pair, with equality only at `a = 1`. The prime obstruction is not visible on the lattice. |
| Treating the lattice skeleton as the form | The archimedean self-energy of a bump of width `w` at a lattice point is of order `w log(1/w)` and dominates the atom terms (of order `w`) as `w → 0`; lattice positivity is small-support positivity, not RH content. |
| Expecting many crossing atoms inside one dyadic window | At most one pair of consecutive powers of `2` and one of `3`, each of size `O(1/X)`; the ratio atoms inside the window are `O(1)`. |
| Treating `ratioAtom a b` as symmetric | It is defined for `a ∣ b` with `a < b`; `productAtom` is symmetric. |
| Deducing a sign for a continuum pair from the lattice | The anti-diagonal `|x| + y = log n` is a segment; its lattice points are the factorizations of `n`, and the dominance law speaks only about those. |
| Expecting the pole to pay a prime atom near the axes | The polar weight vanishes at both ends of every anti-diagonal; near an axis only same-side atoms and the gauge can pay. |
| Reading "the pole pays the atom at the midpoint" as payment of the atom | It is a pointwise comparison of weights per unit gauge at one point; the atom is a Dirac mass along the whole segment and the pole's share depends on the gauge profile along it. |
| Expecting the ten moduli to be the primes below some bound | They are the primes up to `19` together with `4` and `9`; `8`, `16`, `25` and `27` are paid at the midpoint, `19` is kept by a margin of `0.4` in `(√p − 1)² < 4 log p`. |
| Expecting the atom to create new negative lattice pairs | On every lattice crossing pair with `a, b ≥ 2` the polar weight that beats the archimedean density also beats the density plus the atom; the closest case `{2, 8}` has a margin of `0.21` in the coefficient inequality. |
| Confusing the ten moduli with the thirteen | Atom alone against the pole: `{2,3,4,5,7,9,11,13,17,19}`. Atom plus archimedean density against the pole: `{2,…,9,11,13,17,19,23}`; the density adds `6`, `8` and `23`, and the composite moduli enter only through the density. |

---

## 5. Open problems

1. **Pairs between lattice points.** Bound the anti-diagonal atom `Λ(n) n^{−1/2}` on a crossing pair
   `(x, y)` with `|x| + y = log n` that is not a lattice pair by the same-side atoms at the ratios
   `|x − y'| = log m` reachable from it and by the variance. This is the prime-side inequality of the
   open core; in a smeared gauge it is RH itself, so the problem is to find the sub-inequalities that
   are unconditional. The smallest instance is the first prime window: a gauge argument for supports
   past `log 2 / 2`, paying the single atom `Λ(2)/√2`.
1′. **The atom against the pole, integrated.** For an odd gauge `M`, compare the atom mass
   `Λ(n) n^{−1/2} ∫₀^{log n} |M(−a) M(log n − a)| da` with the polar mass
   `∫₀^{log n} |M(−a) M(log n − a)| P(a) da` along the anti-diagonal. Determine the gauges for which
   the pole pays every atom outside the ten moduli, and the amount the same-side atoms must pay
   for the ten; the axis law says the answer depends on the decay of `M` at `0`.
2. **The bump bridge.** For an even profile built from bumps of width `w` at the points `± log a`,
   express the prime part of `J_M` in the limit `w → 0`, normalized by `w`, as a diagonal term
   `2 Σ_a c_a² M(log a) 𝒢_prime(M)(log a)` (the prime generator of the gauge) minus the pair term
   `4 Σ_{a<b} c_a c_b M(log a)M(log b) netAtom(a,b)`, and identify the archimedean self-energy
   `≍ w log(1/w)` that dominates the limit.
3. **Collar ratio.** The two ends of the sandwich differ by `sinh(s/2)/sinh(s/2 − 6e^{−3s/4})`;
   show that the collar end `c(s)`, the root of `P_s(c) = ω(s)`, satisfies
   `c(s) = ℓ(s)(1 + O(e^{−s}))`, and give the explicit second-order term.
3′. **The range `24 ≤ n ≤ 40`.** Mechanism 22 needs the quarter point paid, proved for `n ≥ 41`;
   determine the exact set of `n` for which the quarter point is paid (it fails for `10`, `29`, `31`
   and the thirteen moduli), and describe the unpaid set when the midpoint is paid but the quarter
   point is not.
4. **Lattice conductance at fixed width.** Combine mechanism 20 with the archimedean self-energy
   `≍ w log(1/w)` of a bump of width `w` into one statement about the conductance matrix of a
   lattice profile at fixed `w`, including the axis pairs `(0, log b)`.
5. **Parity.** Which complete-period quadratic forms of the sieve theory (variance, Bézout
   successor form, two-lag covariances) are even functions of the Selberg coordinates, hence
   invariant under every sign character on the coordinates, while the trans-horizon response is
   not; exhibit the pair of rows this separates.
6. **Windows across scales.** The ratio atoms at `m ≥ 4` and the product atoms couple different
   dyadic windows; describe the coupling graph between windows and the size of its edges.

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
4. **Unconditional statements on honest classes.** Integers, real pairs, `C²` profiles with compact
   support; no hypothesis that restates the sign to be proved.
5. **Keep the other programmes in view.** The gauge and the generators live in the arithmetic
   criticality theory; the window tests in the square-root threshold programme; the half-line
   folding and the divisor cuts in CHMD; the sieve coordinates in the Bézout–valuation and
   trans-horizon programmes.
