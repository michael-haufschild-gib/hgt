# Worlds of the Zero Configuration (WZC)

Namespace `GaloisForLFunctions.WorldsOfTheZeroConfiguration`; umbrella
`WorldsOfTheZeroConfiguration.lean`.

## 1. Motivation

A failure of the Riemann hypothesis has one of two shapes. In **world I** finitely many zeros
lie right of some line `Re s = ½ + h`: a finite, isolated top layer. In **world II** the zeros
approach a line `Re s = Θ∞ > ½`: a tail. The asymptotic abscissa law (AAL) says that world I is
empty, the law ZAL that world II is empty, and RH is the two together with the atoms B13 and
Landing.

For world I the corpus has complete *receivers* (statements about a finite layer that give AAL)
and no *producer*. What decides where a producer can come from is the **model theory** of a
finite layer: for each set of structures of `ζ`, is there a system with those structures and a
finite layer? A proof of AAL that uses only structures of a system with a finite layer is wrong.

WZC is the programme of the two worlds:

* it builds the models over the structure closest to `ζ` — the rational primes themselves, each
  taken zero, one or two times — and proves the laws that every such model obeys;
* it states, for each world, what a producer must use and what it cannot be built from;
* it keeps the instruments of the route (filters, currents, quanta, cameras, the scale) in one
  language, so that a statement about a finite layer or about a tail is tested on the models
  before work is spent on it.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Edit | `TwoSidedEdits.IsEdit e` | a sign `e : ℕ → {−1, 0, 1}` supported on the primes |
| Doubled, deleted primes | `plusSet e`, `minusSet e` | the primes with `e = 1`, with `e = −1` |
| System of an edit | `editSystem e` | the rational primes with the deleted primes removed and a second generator of norm `p` for each doubled prime; integer norms |
| Edit series, remainder | `LSeries (e ·)`, `editRem e` | `E(s) = Σ_p e(p) p^{−s}`; `Q(s) = Σ_p e(p)(−log(1 − p^{−s}) − p^{−s})`, holomorphic on `Re s > ½` |
| Target | `PrimeEdits.target ρ` | `m(k) = −2 Re k^{ρ−1}`: minus the coefficient of `ζ(s+1−ρ) + ζ(s+1−ρ̄)` |
| Greedy rounding | `GreedyRounding.sgn`, `disc` | signs at the sites of a set that keep `Σ (m(k) − ε(k) w(k))` small |
| Greedy edit | `PrimeEdits.gedit m`, `gdisc m`; `edit ρ` | the greedy rounding of a target `m` on the primes with the weights `log p`; `edit ρ = gedit (target ρ)` |
| Prescribed factor | `L` in `exists_exp_geditSeries_eq` | a function without zeros on `Re s > 1` with `L′/L = −Σ m(k)k^{−s} −` holomorphic |
| Layer | `layerTarget J ρ`, `layerFactor J ρ`, `IsLayerTwin B J ρ` | a finite family of points with multiplicities; `L = ∏ (s−ρ_j)(s−ρ̄_j)` |
| Square target | `SquareTarget.sqTarget a` | `2Λ(j)j^{2a}` at `k = j²`; Dirichlet series `−2ζ′/ζ(2s−2a)` |
| Pair with a tail | `tailTarget ρ a`, `tailFactor ρ a`, `IsTailTwin B ρ a`, `tailSet a` | `L = (s−ρ)(s−ρ̄)·u(2s−2a)`, `u(w) = (w−1)ζ(w)`; the tail is `{a + z/2 : ζ(z) = 0}` |
| Configuration that approaches the line | `landingTarget ρ`, `landingTail ρ N`, `IsLayerTwinOn c B J ρ`, `IsLandingTwin B ρ` | a sequence `ρ_j` with `Re ρ_j ↓ ½`, any heights; the pair `ρ_j` is on from `2^{j+1}`; on `Re s > Re ρ_N` the factor is `∏_{j<N} (s−ρ_j)(s−ρ̄_j)` |
| Late pair, cut regular part | `PrimeEdits.cutTarget ρ N`, `zetaCut N` | the target of `ρ` for `k > N` only; `Z_N(w) = ζ(w) − 1/(w−1) − Σ_{k≤N} k^{−w}`, entire |
| Sparse configuration | `IsSparseConfig ρ b A`, `cutoff`, `sparseTarget`, `sparseFactor`, `regSeries` | `½ < Re ρ_j ≤ b`, `|Im ρ_j| ≥ (j+1)^A`, `b + 1/(2A) < 14/15`; pair `j` on beyond `⌈|Im ρ_j|⌉²`; factor = canonical products over the points and their conjugates |
| Factor twin | `IsFactorTwin B L` | `(s−1)ζ_B(s) = (s−1)ζ(s) · C · L(s) · e^{H(s)}`, `C ≠ 0`, `H` holomorphic on `Re s > ½`; fake zeros = zeros of `L` |
| Pair twin | `IsPairTwin B ρ` | `(s−1)ζ_B(s) = (s−1)ζ(s) · C (s−ρ)(s−ρ̄) e^{H(s)}`, `C ≠ 0`, `H` holomorphic on `Re s > ½` |
| Fake zero set | `HasFakeZeroSet B Z` | the continuation of `(s−1)ζ_B` to `Re s > ½` vanishes, off `1` and the zeros of `ζ`, exactly on `Z` |
| Exponent | `BalanceLaw.expo T` | abscissa of `Σ_{p ∈ T} p^{−σ}` for a set `T` of primes |
| Fake | `SumProductArithmeticOfTheLogarithm.IsIntegerNormFakeAt B β` | integer norms, count `Ax + O(x^β)`, a zero of the continuation where `ζ ≠ 0` |
| Norm count, twin coefficients | `NormCount.freeFn S * freeFn Tᶜ`, `mobFn S * freeFn Tᶜ`; `CountFloor.normFn`, `twinFn` | `a(n)` = number of integers of norm `n`; `u = μ * a`, the coefficients of `ζ_B/ζ`; for an edit `a = 1_S * 1_T`, `u = μ_S * 1_T` |
| Remainder | `CountSieve.cnt`, `rem` | `N(x) = Σ_{n ≤ x} a(n)`, `R(x) = N(x) − Ax` |
| Seen prime | `CountSieve.IsSeen a u p` | on every multiple `pn` the divisors divisible by `p` carry a mass of one sign and size at least `a(n)`: deleted primes (`−`) and doubled primes (`+`) |

## 3. Language

- **World I / world II**: a finite isolated top layer / a tail. **Atoms**: ZAL, B13, Landing.
- **Edit**: a change of the multiplicities of the rational primes within `{0, 1, 2}`.
  **One-sided**: only deletions or only doublings. **Two-sided**: both.
- **Fake zero**: a zero right of the line of the continuation of `(s−1)ζ_B(s)` at a point where
  `ζ` does not vanish. **Top**: the fake zeros of largest real part.
- **Exponent** of a set of primes: its abscissa of convergence. **Thick** at `σ`: not summable at
  `σ`. **Balanced** edit: the doubled and the deleted primes have the same exponent.
- **Discrepancy** of an edit against a target: `Σ_{k ≤ n} (m(k) − e(k) log k)`.
- **Pair twin**: a system whose zeta function is that of `ζ` times one prescribed pair of zeros
  and a zero-free factor.
- **Count rate**: `N_B(x) = Ax + O(x^β)` with `β < 1`; `β` is a **count exponent**.
- **Thin at `θ`**: `Σ_p |e(p)| p^{−θ} < ∞` with `θ < 1`. Then `Σ_d |u(d)| d^{−θ} < ∞` for the twin
  coefficients.
- **Count floor**: a lower bound for the count exponents of a class of systems.

## 4. Mechanisms

1. **Greedy rounding.** Walk through the integers with the running discrepancy; double a prime
   when the discrepancy is at least `log p`, delete it when it is at most `−log p`. A rounded
   prime lowers the absolute discrepancy by its weight, so the rounded mass is at most the mass
   of the target (*thinness*). After the last index of small discrepancy every prime is rounded
   the same way, so the excess is the drift of the target minus the prime mass of an interval
   (*discrepancy*).
2. **Primes in short intervals pay the drift.** With `θ(y+L) − θ(y) ≥ (L − (y+L)^α)/2`
   (`α > 17/30`, Guth–Maynard in the corpus) an interval longer than `2n^α` carries prime mass
   above the drift of the target, and a shorter one has drift `O(n^{α−η})`, `η = 1 − Re ρ`.
3. **A prescribed factor is a logarithmic derivative.** `E′(s) = −Σ e(k) log k · k^{−s}` differs
   from `−Σ m(k) k^{−s}` by a Dirichlet series with partial sums `O(n^c)`. If
   `−Σ m(k)k^{−s} = L′/L +` holomorphic, then `exp E = C · L · e^{K}` with `K` holomorphic on
   `Re s > c`. For a pair, `Σ m(k)k^{−s} = −ζ(s+1−ρ) − ζ(s+1−ρ̄)` and `L = (s−ρ)(s−ρ̄)`. No
   zero-free region of `ζ` enters.
4. **Spikes inside the discrepancy.** A target may have spikes if they are sparse: the squares
   in `(b, n]` number at most `(n−b)/√n + 1`, and a spike `2Λ(j)j^{2a}` with `a ≤ 3/10` is
   `O(n^{2/5})`. The pole of `ζ(2s−2a)` at `a + ½` is paid by a smooth deletion `k^{a−1/2}`.
5. **Thin additions keep the count rate.** The count of a system with added generators is the
   count of the base summed over the integers of the addition; a set of doubled primes that is
   summable at `β` keeps the remainder `O(x^β)`.
6. **Landau on one side.** `exp(Σ_{p ∈ T} p^{−s})` does not continue across the exponent of `T`:
   a continuation would vanish there, and the factor is at least one on the real axis. Applied to
   the doubled primes this forbids a surplus; applied to the deleted primes it gives a real zero.
   The continuation need not be given: a count `Ax + O(x^β)` continues `(s−1)ζ_B` to `Re s > β`
   (the coefficients `a(n) − A` have partial sums `O(x^β)`), and the prime-power remainder of an
   edit that is summable at `θ` is holomorphic on `Re s > θ/2`. So the argument runs at every
   height above the count exponent.
7. **The remainder has a peak at every edited prime.** Summation by parts turns
   `Σ_{X<n≤2X} R(n) e(n/p)` into `Σ (a(n) − A) e(n/p)` divided by `1 − e(1/p)`. The divisors prime
   to `p` are equidistributed over the classes mod `p` (the multiples of `d` give a geometric sum,
   at most `p` and at most their number), and the divisors divisible by `p` leave `±AX/p` on the
   class `0`. So the sum is at least `AX/8π`. The frequencies `1/p` are Farey points: the large
   sieve bounds the number of peaks by `128π²(E/A)²`, `E = sup |R|`.
8. **Chebyshev's identity.** `N(x) − 2N(x/2) = Σ_d u(d) [⌊x/d⌋ odd]`. For nonnegative twin
   coefficients the terms `d ∈ (x/2, x]` are bounded by the remainder: additions are counted
   one by one. Putting the deleted primes back (`μ_S * 1_{Sᶜ} = 1`) makes the twin coefficients
   nonnegative at the cost of the exponent of the deleted primes.
9. **Switching pairs on.** Infinitely many pairs enter one target if the pair `ρ_j` is on only
   from `2^{j+1}`: at `k` at most `log₂ k` pairs are on. Without its first `N` pairs the target is
   `O(k^{x−1})` for every `x > Re ρ_N`, so its Dirichlet series is holomorphic right of `ρ_N` and
   is part of the regular term. The factorizations on the half-planes `Re s > Re ρ_N` agree and
   glue.
10. **Late entry at the balanced cutoff.** A pair that is on only beyond `N` has the same two
    poles and the regular part `Z_N(w) = (N^{1−w} − 1)/(w−1) − w∫_N^∞ {t}t^{−w−1}dt`, `w = s+1−ρ`.
    Far from the pair the first term is `N^{Re ρ − Re s}/|Im ρ|` and the second
    `|Im ρ| N^{Re ρ − Re s − 1}`; they balance at `N = |Im ρ|²`, where both are
    `|Im ρ|^{2(Re ρ − Re s) − 1} ≤ |Im ρ|^{2b−2}` on `Re s > ½`. The regular parts of a
    configuration are summable when `Σ_j |Im ρ_j|^{−(2−2b)} < ∞`, and the prescribed factor is the
    canonical product of the configuration. The exponent `2 − 2b` is that of the density
    hypothesis.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Thinness and discrepancy of the greedy rounding | `GreedyRounding.abs_disc_add_sum_le`, `abs_disc_le_of_window` | unconditional |
| The greedy edit at `ρ`: `O(n^{Re ρ})` edited primes, discrepancy `O(n^c)`, `c ≥ α − (1−Re ρ)` | `PrimeEdits.sum_abs_edit_le`, `exists_abs_editDisc_le_rpow` | unconditional |
| `exp(Σ_p e(p)p^{−s}) = C(s−ρ)(s−ρ̄)e^{K(s)}` | `PrimeEdits.exists_exp_editSeries_eq` | unconditional |
| Euler product and count of an edit | `TwoSidedEdits.editSystem_zetaSeriesC`, `editSystem_count` | unconditional |
| The greedy edit is a pair twin of `ζ` for `½ < Re ρ < 14/15` | `isPairTwin_editSystem` | unconditional |
| A non-real pair alone: a two-sided edit that is a fake at every `β > Re ρ` with fake zeros exactly `ρ, ρ̄` | `exists_isEdit_fake_with_zero_pair` | unconditional |
| A count rate does not force a real zero on top: for every `β > ½` a fake whose fake zeros are one non-real pair and whose continuation has no real zero in `(½, ∞)` | `exists_isEdit_fake_without_real_zero` | unconditional |
| Prescribed factor: discrepancy `O(n^c)` and `L′/L = −Σ m k^{−s} −` holomorphic give `exp E = C·L·e^{K}` | `PrimeEdits.exists_exp_geditSeries_eq` | unconditional |
| Every finite layer `ρ_j`, `½ < Re ρ_j ≤ b < 14/15`, with multiplicities, is the exact set of fake zeros of an edit with count `Ax + O(x^β)`, `β > b` | `exists_isEdit_layerTwin`, `exists_isEdit_fake_with_layer` | unconditional |
| A finite layer with a tail: an edit with fake zeros `ρ, ρ̄` and `a + z/2` (`ζ(z) = 0`), the tail infinite and left of `a + ½ < Re ρ` | `exists_isEdit_finite_layer_with_tail`, `tailSet_infinite` | unconditional |
| Every configuration that approaches the line: `Re ρ_j ↓ ½`, `Re ρ_0 < 14/15`, any heights, with multiplicities, is the exact set of fake zeros of an edit with count `Ax + O(x^β)`, `β > Re ρ_0` | `isLayerTwinOn_landing`, `exists_isEdit_landingTwin`, `exists_isEdit_fake_with_landing` | unconditional |
| The greedy edit of any target of size `O(k^{−η})`, `1/15 < η ≤ ½`, is a twin with the factor `L` of the target (`L′/L = −Σ m k^{−s} −` holomorphic on `Re s > ½`) | `isFactorTwin_gedit`, `IsFactorTwin.hasFakeZeroSet` | unconditional |
| Every sparse configuration (`½ < Re ρ_j ≤ b`, `|Im ρ_j| ≥ (j+1)^A`, `b + 1/(2A) < 14/15`) is the exact set of fake zeros of an edit with count `Ax + O(x^β)`, `β > b + 1/(2A)`; the factor is a canonical product | `IsSparseConfig.exists_isEdit_sparseTwin`, `exists_isEdit_fake_sparse` | unconditional |
| Infinitely many fake zeros on one vertical line `Re s = σ`, and none elsewhere; fake zeros whose real parts rise to `σ` without reaching it | `exists_isEdit_zeros_on_a_vertical_line`, `exists_isEdit_zeros_rising_to_a_line` | unconditional |
| A positive Euler factor does not continue across its real abscissa | `BalanceLaw.not_differentiableOn_exp_gdSeries` | unconditional |
| Thickness: a fake zero lies at or left of the larger exponent; edits of exponent `≤ ½` are no fakes | `BalanceLaw.re_le_of_fake_zero`, `not_isIntegerNormFakeAt_of_expo_le` | unconditional |
| No surplus of doubled primes; a surplus of deleted primes is a real zero | `BalanceLaw.expo_plus_le`, `zero_at_expo_minus` | unconditional |
| Balance law: no real zero ⇒ equal exponents; the greedy edit at a non-real `ρ` has both exponents `Re ρ` | `BalanceLaw.balance`, `expo_edit_eq` | unconditional |
| The count sees the edited primes: `a = 1 * u`, `R = O(x^β)`, `Σ |u(d)| d^{−θ} < ∞`, `θ < 1` ⇒ at most `cQ^{2β(2−θ)/(1−θ)}` seen primes up to `Q` | `CountSieve.peak_le_norm`, `card_le_of_scale`, `card_le_rpow` | unconditional |
| Norm count of an edit `1_S * 1_T`; deleted and doubled primes are seen; thin edits have positive density | `NormCount.intCount_eq`, `normCount_eq_zero`, `twinCoeff_prime_mul`, `sum_abs_twinCoeff_mul_rpow_le`, `density_pos` | unconditional |
| Primes that divide no norm of an integer-norm system with thin twin coefficients | `CountFloor.card_normless_le` | unconditional |
| Count floor: for an edit thin at `θ`, `κ₊, κ₋ ≤ 2β(2−θ)/(1−θ)`; `κ(1−κ) ≤ 2β(2−κ)` for `κ = max(κ₊, κ₋) < 1` | `CountFloor.expo_le_of_count`, `expo_mul_one_sub_le` | unconditional |
| Exponent zero: a thin edit has a remainder below every power iff `κ₊ = κ₋ = 0` | `CountFloor.expo_eq_zero_iff` | unconditional |
| A fake zero is paid in the count: `(1−θ) Re ρ ≤ 2β(2−θ)`, `(1−κ₋) Re ρ ≤ 2β(2−κ₋)`; a fake that is a thin edit has `β > (1−θ)/(4(2−θ))`; the greedy pair twin has `Re ρ(1−Re ρ) ≤ 2β(2−Re ρ)` | `CountFloor.mul_re_le_of_fake_zero`, `one_sub_expo_mul_re_le`, `lt_of_isIntegerNormFakeAt`, `greedy_count_floor` | unconditional |
| The count continues the zeta function: an integer-norm system with `N(x) = Ax + O(x^β)` has `(s−1)ζ_B` holomorphic on `Re s > β` | `BalanceLaw.exists_continuation_of_count` | unconditional |
| Landau's zero from the count: `max(κ₊, β) < κ₋` ⇒ `ζ_B(κ₋) = 0`. If `β < max(κ₊, κ₋)` then `κ₊ = κ₋`, or `κ₊ < κ₋` and `ζ_B(κ₋) = 0`; a delete-only edit with `β < κ₋` has the zero | `BalanceLaw.zero_at_expo_minus_of_count`, `balance_or_zero_of_count`, `zero_of_delete_only_of_count` | unconditional |
| Additions are paid in full: an edit without deleted primes has `κ₊ ≤ β`, so its count exponent is exactly `κ₊` | `CountSieve.sum_Ioc_half_le`, `CountFloor.expo_plus_le_of_add_only` | unconditional |
| Count balance: `κ₊ ≤ max(β, κ₋)` for every edit, without a continuation of `ζ_B` | `CountFloor.freeFn_mul_freeFn_compl`, `intCount_restored`, `expo_plus_le_max` | unconditional |

## 6. Traps

| Trap | Truth |
|---|---|
| A count rate forces a real zero on top of a finite layer | Only for one-sided edits (Landau). A balanced edit has a non-real pair alone |
| A system that only adds primes vanishes at its real abscissa | It has no holomorphic continuation there: its Euler factor is at least one on the real axis |
| Multiplicities `0, 1, 2` on the rational primes and integrality constrain a finite layer | Every pair with `½ < Re ρ < 14/15` is realized, alone |
| A thin edit can fake | A fake zero at `ρ` costs both sides the exponent `Re ρ`; edits of exponent `≤ ½` change no zero right of the line |
| The construction needs a zero-free region of `ζ` | The greedy edit matches the target on the integers, not on the primes; `ζ` enters through `ζ(w) − 1/(w−1)` only |
| An isolated top layer of an Euler product over the primes with a count rate repels the other zeros to the line | The pair with a half-scale tail: infinitely many fake zeros on `Re s ≥ a + ¼ > ½` below an isolated pair |
| A count rate and an Euler product over the primes make zeros that approach the line land on it | Every sequence with `Re ρ_j ↓ ½` is realized: infinitely many fake zeros off the line, finitely many right of each `½ + h` |
| World II over the rational primes needs a structured tail (a second zeta function) | Any sparse set of points is a tail: zeros on a vertical line, zeros rising to a line that they do not reach |
| The balance law is a statement about the half-plane right of the line | It holds at every height above the count exponent: a count that beats the thickness of an edit forces balance or a real zero at `κ₋`, also for `κ₋ ≤ ½` |
| Doubled primes can hide below the count remainder | Additions are paid in full: `κ₊ ≤ max(β, κ₋)`. Only deletions can hide, and only up to the count floor |
| A model can also carry the reflection | A discrete Beurling system with Riemann's functional equation is the rational primes (Hamburger rigidity, `ArithmeticPositiveDuality.beurlingSystem_rigidity_of_completed_functional_equation`). Every model here lacks the reflection |
| The models say something about `ζ` | They are relative to `ζ`: they bound what the structures they keep can prove |
| A count below `√x` follows from the discrepancy at frequency zero | It needs discrepancy at every frequency: the greedy edit gives `β > Re ρ > ½` |
| A fake can have a count remainder below every power | Not a thin edit: `β > (1−θ)/(4(2−θ))`; below every power means exponent zero, and then there is no fake zero |
| The remainder sees a fake zero | A fake zero is a zero of the Mellin transform `ζ(s)U(s)/s` of the remainder, not a pole. The floor comes from the edited primes; the zero enters through thickness, `Re ρ ≤ κ` |
| The density of a fake is positive by definition | The definition allows `A = 0`; for a thin edit `A > 0` is a theorem (put the deleted primes back), and the floor needs it |

## 7. Questions the programme aims to answer

1. Is there one inequality for a finite layer of `ζ` that fails on every model: AAL (B145, B170).
2. The model with a non-real top and a count rate (B183). Answered at every exponent above `½`.
   A thin edit cannot go below the count floor `(1−θ)/(4(2−θ))`; between the floor and `½` it
   needs a two-sided selection with discrepancy at every frequency.
3. Is world I with a tail empty: does a finite layer force ZAL (B141)? Not from an Euler
   product over the rational primes with a count rate: the pair with a half-scale tail.
4. B13 and Landing: which input beyond one structure do they need (B157, A120)? Not an Euler
   product over the rational primes with a count rate: every finite layer and every
   configuration that approaches the line is realized.
5. The cluster wall of the cameras (B59).
6. The half-planes of world II. Model side: every sparse tail is realized over the rational
   primes with a count rate, so a half-plane law for `ζ` uses more than these structures.

## 8. Tools

**Developed.** Greedy two-sided rounding with a window criterion; prime edits against a target
with a drift criterion; the prescribed factor of an edit series; finite layers with
multiplicities; square targets and half-scale tails; counts and zeta functions of sums of
systems; summability of integers supported on a thin set of primes; Euler products of kept
primes; exponents of sets of primes; the balance law; the large sieve over the edited primes
(peaks of the remainder at `1/p`); norm counts and twin coefficients as Dirichlet convolutions;
Chebyshev's identity for a system; the restored system of an edit; targets with pairs switched
on along a dyadic schedule; gluing of twins on a decreasing family of half-planes; pairs that
enter at the balanced cutoff `|Im ρ|²` and the size of their regular parts; canonical products
as prescribed factors; twins with a factor; the continuation of `(s−1)ζ_B` from the count; the
prime-power remainder of a thin edit left of the line.

**To build.** A two-sided selection of primes with square-root discrepancy at every frequency
and the Perron analysis of its count; factors beyond absolute convergence of the regular parts
(dense configurations); the weighted current at a growing isolated mode.

## 9. Open research topics

- The count of a pair twin below `√x`.
- Dense configurations. Sparse ones are realized up to `Σ_j |Im ρ_j|^{−(2−2b)} < ∞` (in Lean for
  heights `≥ (j+1)^A`): the exponent of the density hypothesis, where the regular parts stop
  converging absolutely on the line. Which densities beyond it are realized without structure
  is open; with structure the half-scale tail has `≍ T log T` fake zeros on one line. A density
  law for the fake zeros of edits with a given count exponent is open in both directions.
- The count exponent of deletions: is `β ≥ κ₋/2` for delete-only edits? A delete-only edit with
  `β < κ₋` has `ζ_B(κ₋) = 0`: its deleted primes imitate a zero. The floor `κ(1−κ)/(2(2−κ))` and
  the short-interval variance both stop at `κ/4` (independence of the primes up to `√X` only).
- The count exponent of a pair twin: between `Re ρ(1−Re ρ)/(2(2−Re ρ))` and `Re ρ`.
- The loss `1−θ` in the count floor: the twin coefficients in `(X, 2X]` enter the peak as
  `Σ u(d) e(d/p)`, bounded by their number; any saving there widens the range of the sieve.
- A count floor for integer-norm systems that are not thin edits.
- A statement about a finite layer of `ζ` that uses the exact count or the functional equation
  and fails for every edit.

## 10. Context

| Neighbour | Interface |
|---|---|
| ZeroConfigurationGeometry | worlds, abscissa laws, cameras; WZC continues its route |
| FloorFreeArithmetic | receivers of AAL, tangent data, finite strata under one structure |
| ExceptionalLayerTheory | filters, currents, atoms, the Deuring–Heilbronn question |
| SumProductArithmeticOfTheLogarithm | fakes: definition, deletions, the count remainder; WZC adds the two-sided class |
| ArithmeticPositiveDuality | one-offs over natural norms and repeated primes, the firewall; Hamburger rigidity of Beurling systems under the reflection |
| RHTower (Beurling systems, Landau, short intervals) | the systems, the Landau transfer, primes in `(x, x + x^α]` |
| HeckeLFunctions, HTGeometry | Dirichlet series with power-bounded partial sums; primitives on half-planes |
| BezoutValuationIncidence, RHTower.Sieve | the large sieve on the Farey points with the constant `N + Q² − 1` |

WZC is a programme of receivers and models. It contains no producer. Its count laws are laws of
the model class: they are relative to `ζ` and say nothing about the zeros of `ζ`.

**Where a producer can come from.** Each structure of `ζ` alone has models with a finite layer,
with a tail, and with zeros that approach the line:

| Structures kept | Models |
|---|---|
| reflection symmetry and temperedness; the functional equation with Gamma factor, order one and the zero count; no Euler product | symmetric configurations with any finite top layer; zeros off the line that approach it (model ladder of FloorFreeArithmetic and ZeroConfigurationGeometry) |
| Euler product over the rational primes, multiplicities `0, 1, 2`, integer norms, count `Ax + O(x^β)` with `β` above the top | two-sided edits (this programme) |
| Euler product, integer norms, count below the count floor | none among thin edits: no fake zero |
| Euler product and reflection | none: the system is the rational primes (ArithmeticPositiveDuality) |

So an argument for AAL, ZAL, B13 or Landing uses the Euler product together with the reflection,
or the Euler product together with a count below the floor. An argument that uses one row of
the first two holds for its models and is wrong.

## 11. Success criteria

- World I: AAL, or a model with every structure of `ζ` that a proposed proof uses.
- World II: a half-plane at every depth, placed on the scale.
- Model theory: every finite datum, and every tail that the structures allow, realized over the
  rational primes with a count rate; each law that all models obey proved. Done above `√x` for
  finite data, for one tail left of an isolated pair, for configurations that approach the line
  and for sparse configurations (world II); open below `√x` and for dense configurations.
- Count laws: the exact count exponent of each class of edits. Exact for add-only edits
  (`κ₊`); bounded below for thin edits (count floor); the sharp value for deletions and for
  pair twins is open.

## 12. What a contribution must be

- A theorem about `ζ` in world I or world II states which structure it uses and fails on the
  models that lack it: tempered symmetric configurations, the firewall, deletion fakes, pair
  twins.
- A model keeps integer norms and a count rate, names its fake zeros exactly, and says which
  structure of `ζ` it lacks.
- A law for models is proved for every edit, not for a construction.
- A count law bounds an exponent of the edit, or the real part of a fake zero, by the count
  exponent with explicit constants, or shows by a model that such a bound fails.
- Nothing in law is used as a point; no window below the logarithmic radius decides.
