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
| Edit | `TwoSidedEdits.IsEdit e`, `plusSet e`, `minusSet e` | a sign `e : ℕ → {−1, 0, 1}` supported on the primes; doubled primes `e = 1`, deleted primes `e = −1` |
| System of an edit | `editSystem e` | the rational primes with the deleted primes removed and a second generator of norm `p` for each doubled prime; integer norms |
| Edit series, remainder | `LSeries (e ·)`, `editRem e` | `E(s) = Σ_p e(p) p^{−s}`; `Q(s) = Σ_p e(p)(−log(1 − p^{−s}) − p^{−s})`, holomorphic on `Re s > ½`, and on `Re s > θ/2` if the edit is summable at `θ` |
| Target | `PrimeEdits.target ρ`, `layerTarget J ρ`, `cutTarget ρ N` | `m(k) = −2 Re k^{ρ−1}`: minus the coefficient of `ζ(s+1−ρ) + ζ(s+1−ρ̄)`; sums over a layer; a pair that is on for `k > N` only |
| Greedy edit | `GreedyRounding.sgn`, `PrimeEdits.gedit m`, `gdisc m`; `edit ρ` | the greedy rounding of a target on the primes with the weights `log p`, and its discrepancy `Σ_{k≤n}(m(k) − e(k) log k)` |
| Twin with a factor | `IsFactorTwinOn c B L`; `IsFactorTwin`, `IsPairTwin`, `IsLayerTwin`, `IsTailTwin`, `IsLandingTwin` | `(s−1)ζ_B(s) = (s−1)ζ(s) · C · L(s) · e^{H(s)}`, `C ≠ 0`, `H` holomorphic on `Re s > c`; the named cases have `c = ½` and `L` a pair, a layer `∏(s−ρ_j)(s−ρ̄_j)`, a pair times `u(2s−2a)`, a sequence of layers |
| Cut regular part | `PrimeEdits.zetaCut N` | `Z_N(w) = ζ(w) − 1/(w−1) − Σ_{k≤N} k^{−w}`, entire: the regular part of a pair that enters at `N` |
| Configurations | `landingTarget ρ`; `IsSparseConfig ρ b A`, `sparseTarget`, `sparseFactor` | `Re ρ_j ↓ ½` with any heights (pair `j` on from `2^{j+1}`); `½ < Re ρ_j ≤ b`, `|Im ρ_j| ≥ (j+1)^A`, `b + 1/(2A) < 14/15` (pair `j` on beyond `⌈|Im ρ_j|⌉²`, factor a canonical product) |
| Fake zero set, fake | `HasFakeZeroSet B Z`, `SumProductArithmeticOfTheLogarithm.IsIntegerNormFakeAt B β` | the continuation of `(s−1)ζ_B` to `Re s > ½` vanishes, off `1` and the zeros of `ζ`, exactly on `Z`; integer norms, count `Ax + O(x^β)`, a zero of the continuation where `ζ ≠ 0` |
| Exponent | `BalanceLaw.expo T` | abscissa of `Σ_{p ∈ T} p^{−σ}`; `κ₊`, `κ₋` for the doubled and the deleted primes |
| Norm count, twin coefficients | `NormCount.freeFn S * freeFn Tᶜ`, `mobFn S * freeFn Tᶜ`; `BalanceLaw.countDefect` | `a(n)` = number of integers of norm `n`; `u = μ * a`, the coefficients of `ζ_B/ζ`; for an edit `a = 1_S * 1_T`, `u = μ_S * 1_T`; `a(n) − A`, the coefficients of `ζ_B − Aζ` |
| Remainder, seen prime | `CountSieve.rem`, `IsSeen a u p` | `R(x) = N(x) − Ax`; a prime at which the divisors divisible by `p` carry, on every multiple `pn`, a mass of one sign and size at least `a(n)`: deleted and doubled primes |

## 3. Language

- **World I / world II**: a finite isolated top layer / a tail. **Atoms**: ZAL, B13, Landing.
- **Edit**: a change of the multiplicities of the rational primes within `{0, 1, 2}`.
  **One-sided**: only deletions or only doublings. **Two-sided**: both.
- **Fake zero**: a zero right of the line of the continuation of `(s−1)ζ_B(s)` at a point where
  `ζ` does not vanish. **Top**: the fake zeros of largest real part.
- **Exponent** of a set of primes: its abscissa of convergence. **Thick** at `σ`: not summable at
  `σ`. **Balanced** edit: the doubled and the deleted primes have the same exponent.
  **Logarithmic density** `m` at the scale `κ`: `Σ_{p ∈ T} p^{−σ} = m log(1/(σ−κ)) + O(1)` as
  `σ ↓ κ`; the primes have density one at the scale one.
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

All in Lean, unconditional. The card
`docs/drafts/pipeline/1-in-progress/wzc-worlds-of-the-zero-configuration-programme.md` has the
proofs.

**Tools.**

| Theorem | Lean |
|---|---|
| The greedy edit against a target of size `k^{−η}`: `O(n^{1−η})` edited primes, discrepancy `O(n^c)` for `c > 17/30 − η` | `GreedyRounding.abs_disc_add_sum_le`, `PrimeEdits.exists_abs_gdisc_le_rpow_of_abs_le` |
| Prescribed factor: `L′/L = −Σ m k^{−s} −` holomorphic ⇒ `(s−1)ζ_B = (s−1)ζ · C · L · e^{H}` on `Re s > max(17/30 − η, (1−η)/2)` | `PrimeEdits.exists_exp_geditSeries_eq`, `isFactorTwinOn_gedit` |
| Euler product and count of an edit | `TwoSidedEdits.editSystem_zetaSeriesC`, `editSystem_count` |

**Models.** Each is a two-sided edit of the rational primes with integer norms, a count
`Ax + O(x^β)` and an exact set of fake zeros.

| Model | Lean |
|---|---|
| A non-real pair alone, without a real zero on top, at every `β > ½` | `exists_isEdit_fake_with_zero_pair`, `exists_isEdit_fake_without_real_zero` |
| Every finite layer with multiplicities, `Re ρ_j ≤ b < 1` (exact right of the line for `b < 14/15`) | `exists_isEdit_fake_with_layer`, `exists_isEdit_layerTwinOn` |
| An isolated pair above an infinite half-scale tail `a + z/2`, `ζ(z) = 0` | `exists_isEdit_finite_layer_with_tail` |
| Every configuration that approaches the line: `Re ρ_j ↓ ½`, any heights | `exists_isEdit_fake_with_landing` |
| Every sparse configuration, with a canonical product as factor: zeros on a vertical line, zeros rising to a line, infinitely many strict fake zeros | `IsSparseConfig.exists_isEdit_fake_sparse`, `exists_isEdit_zeros_on_a_vertical_line`, `exists_isEdit_zeros_rising_to_a_line`, `exists_isEdit_fake_with_strict_zeros_on_a_line` |
| A finite layer edited away; in world I an edit with a larger zero-free half-plane than `ζ` | `exists_isEdit_layer_removed`, `exists_isEdit_zero_free_of_finite_layer` |
| The pair twin is holomorphic on `Re s > Re ρ/2` apart from the pole, and its zeros are not symmetric about the line | `isFactorTwinOn_edit`, `exists_continuation_not_symmetric` |

**Laws.** For every edit; `β` is a count exponent.

| Law | Lean |
|---|---|
| Thickness: a fake zero has `Re ρ ≤ max(κ₊, κ₋, ½)` | `BalanceLaw.re_le_of_fake_zero` |
| Balance: a positive Euler factor does not continue across its real abscissa; no surplus of doubled primes; a surplus of deleted primes is a real zero at `κ₋`; no real zero ⇒ `κ₊ = κ₋` | `BalanceLaw.not_differentiableOn_exp_gdSeries`, `expo_plus_le`, `zero_at_expo_minus`, `balance` |
| Logarithmic density: a fake zero on the line `Re s = κ` right of which the edit is summable costs `Σ_{p edited} p^{−σ} ≥ log(1/(σ−κ)) − C`; without a real zero at `κ`, each side at least `½ log(1/(σ−κ)) − C` (so for the greedy edit at a non-real `ρ`) | `BalanceLaw.exists_log_le_primeSum_add`, `exists_half_log_le_primeSum`, `exists_half_log_le_primeSum_edit` |
| The count continues `(s−1)ζ_B` to `Re s > β`. If `β < max(κ₊, κ₋)` then `κ₊ = κ₋`, or `ζ_B` has a zero of an order `m ≥ 1` at `κ₋` and `Σ_{p deleted} p^{−σ} = m log(1/(σ−κ₋)) + O(1)` | `BalanceLaw.exists_continuation_of_count`, `balance_or_zero_of_count`, `exists_order_of_count` |
| A fake below its top: if `β < Re ρ₀` for a fake zero `ρ₀` (always if `β ≤ ½`), then `κ₊ = κ₋`, or `ζ_B(κ₋) = 0` with `κ₋ > ½` at or right of every fake zero | `BalanceLaw.balance_or_real_top`, `balance_or_real_top_of_fake` |
| Additions are paid in full: `κ₊ ≤ max(β, κ₋)`; an add-only edit has count exponent exactly `κ₊` | `CountFloor.expo_plus_le_max`, `expo_plus_le_of_add_only` |
| Count floor: an edit thin at `θ` has at most `cQ^{2β(2−θ)/(1−θ)}` edited primes up to `Q`; `κ(1−κ) ≤ 2β(2−κ)`; a fake zero has `(1−κ₋) Re ρ ≤ 2β(2−κ₋)`; a thin fake has `β > (1−θ)/(4(2−θ))` | `CountSieve.card_le_rpow`, `CountFloor.expo_mul_one_sub_le`, `one_sub_expo_mul_re_le`, `lt_of_isIntegerNormFakeAt` |
| Exponent zero: a thin edit has a remainder below every power iff `κ₊ = κ₋ = 0`; then it has no fake zero | `CountFloor.expo_eq_zero_iff` |

## 6. Traps

| Trap | Truth |
|---|---|
| A count rate forces a real zero on top of a finite layer | Only for one-sided edits (Landau). A balanced edit has a non-real pair alone |
| A system that only adds primes vanishes at its real abscissa | It has no holomorphic continuation there: its Euler factor is at least one on the real axis |
| Multiplicities `0, 1, 2`, integrality and a count rate constrain the zeros right of the line | Realized: any finite layer; an isolated pair above a tail; zeros that approach the line; any sparse tail (a vertical line, zeros rising to a line) |
| A thin edit can fake | A fake zero at `ρ` costs the exponent `Re ρ`; edits of exponent `≤ ½` change no zero right of the line |
| The construction needs a zero-free region of `ζ` | The greedy edit matches the target on the integers, not on the primes; `ζ` enters through `ζ(w) − 1/(w−1)` only |
| The balance law is a statement about the half-plane right of the line | It holds at every height above the count exponent. A count below `κ₋` without balance quantizes the deleted primes: the logarithmic density of `m` copies of the primes at the scale `κ₋` |
| Doubled primes can hide below the count remainder | Additions are paid in full: `κ₊ ≤ max(β, κ₋)`. Only deletions can hide, and only down to the count floor |
| The zeta function of a pair twin stops at the line | It is holomorphic on `Re s > Re ρ/2` apart from the pole. What keeps its count above `√x` is growth on vertical lines, not a singularity |
| The bound `14/15` limits the real part of a fake zero | It limits the half-plane of the factorization: for `Re ρ ≤ b < 1` the layer is the exact zero set in `Re s > max(b − 13/30, b/2)` |
| `ζ` has the largest zero-free half-plane among the systems over its primes | In world I it does not: the edit that removes the top layer has integer norms, a count rate and a larger zero-free half-plane. "No edit with a count rate beats `ζ`" implies AAL; it is a statement about `ζ`, not a law of edits |
| A model can also carry the reflection | A discrete Beurling system with Riemann's functional equation is the rational primes (`ArithmeticPositiveDuality.beurlingSystem_rigidity_of_completed_functional_equation`). The zeros of a pair twin are not symmetric |
| The models say something about `ζ` | They are relative to `ζ`: they bound what the structures they keep can prove |
| A count below `√x` follows from the discrepancy at frequency zero | It needs discrepancy at every frequency: the greedy edit gives `β > Re ρ > ½` |
| A fake can have a count remainder below every power | Not a thin edit: `β > (1−θ)/(4(2−θ))`; below every power means exponent zero |
| The remainder sees a fake zero | A fake zero is a zero of the Mellin transform `ζ(s)U(s)/s` of the remainder, not a pole. The floor comes from the edited primes; the zero enters through thickness |
| The density of a fake is positive by definition | The definition allows `A = 0`; for a thin edit `A > 0` is a theorem, and the floor needs it |

## 7. Questions the programme aims to answer

1. Is there one inequality for a finite layer of `ζ` that fails on every model: AAL (B145, B170).
2. The model with a non-real top and a count rate (B183). Answered at every exponent above `½`.
   Below `√x`: an edit that is not exactly balanced (`κ₊ ≠ κ₋`) has a real zero on top; a thin
   edit cannot go below the count floor `(1−θ)/(4(2−θ))`; a balanced one between the floor and
   `½` needs a two-sided selection with discrepancy at every frequency.
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

- The count of a pair twin below `√x`. Its zeta function is holomorphic on `Re s > Re ρ/2` apart
  from the pole; the count is below `√x` if `exp(Σ_p e(p)p^{−s})` grows polynomially on a line
  `Re s = c < ½`. The greedy edit controls its discrepancy at frequency zero only.
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
