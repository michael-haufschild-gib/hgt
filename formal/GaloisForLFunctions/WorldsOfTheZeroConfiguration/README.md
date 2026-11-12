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
| Pair twin | `IsPairTwin B ρ` | `(s−1)ζ_B(s) = (s−1)ζ(s) · C (s−ρ)(s−ρ̄) e^{H(s)}`, `C ≠ 0`, `H` holomorphic on `Re s > ½` |
| Fake zero set | `HasFakeZeroSet B Z` | the continuation of `(s−1)ζ_B` to `Re s > ½` vanishes, off `1` and the zeros of `ζ`, exactly on `Z` |
| Exponent | `BalanceLaw.expo T` | abscissa of `Σ_{p ∈ T} p^{−σ}` for a set `T` of primes |
| Fake | `SumProductArithmeticOfTheLogarithm.IsIntegerNormFakeAt B β` | integer norms, count `Ax + O(x^β)`, a zero of the continuation where `ζ ≠ 0` |

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
- **Count rate**: `N_B(x) = Ax + O(x^β)` with `β < 1`.

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
6. **Spikes inside the discrepancy.** A target may have spikes if they are sparse: the squares
   in `(b, n]` number at most `(n−b)/√n + 1`, and a spike `2Λ(j)j^{2a}` with `a ≤ 3/10` is
   `O(n^{2/5})`. The pole of `ζ(2s−2a)` at `a + ½` is paid by a smooth deletion `k^{a−1/2}`.
4. **Thin additions keep the count rate.** The count of a system with added generators is the
   count of the base summed over the integers of the addition; a set of doubled primes that is
   summable at `β` keeps the remainder `O(x^β)`.
5. **Landau on one side.** `exp(Σ_{p ∈ T} p^{−s})` does not continue across the exponent of `T`:
   a continuation would vanish there, and the factor is at least one on the real axis. Applied to
   the doubled primes this forbids a surplus; applied to the deleted primes it gives a real zero.

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
| A positive Euler factor does not continue across its real abscissa | `BalanceLaw.not_differentiableOn_exp_gdSeries` | unconditional |
| Thickness: a fake zero lies at or left of the larger exponent; edits of exponent `≤ ½` are no fakes | `BalanceLaw.re_le_of_fake_zero`, `not_isIntegerNormFakeAt_of_expo_le` | unconditional |
| No surplus of doubled primes; a surplus of deleted primes is a real zero | `BalanceLaw.expo_plus_le`, `zero_at_expo_minus` | unconditional |
| Balance law: no real zero ⇒ equal exponents; the greedy edit at a non-real `ρ` has both exponents `Re ρ` | `BalanceLaw.balance`, `expo_edit_eq` | unconditional |

## 6. Traps

| Trap | Truth |
|---|---|
| A count rate forces a real zero on top of a finite layer | Only for one-sided edits (Landau). A balanced edit has a non-real pair alone |
| A system that only adds primes vanishes at its real abscissa | It has no holomorphic continuation there: its Euler factor is at least one on the real axis |
| Multiplicities `0, 1, 2` on the rational primes and integrality constrain a finite layer | Every pair with `½ < Re ρ < 14/15` is realized, alone |
| A thin edit can fake | A fake zero at `ρ` costs both sides the exponent `Re ρ`; edits of exponent `≤ ½` change no zero right of the line |
| The construction needs a zero-free region of `ζ` | The greedy edit matches the target on the integers, not on the primes; `ζ` enters through `ζ(w) − 1/(w−1)` only |
| An isolated top layer of an Euler product over the primes with a count rate repels the other zeros to the line | The pair with a half-scale tail: infinitely many fake zeros on `Re s ≥ a + ¼ > ½` below an isolated pair |
| The models say something about `ζ` | They are relative to `ζ`: they bound what the structures they keep can prove |
| A count below `√x` follows from the discrepancy at frequency zero | It needs discrepancy at every frequency: the greedy edit gives `β > Re ρ > ½` |

## 7. Questions the programme aims to answer

1. Is there one inequality for a finite layer of `ζ` that fails on every model: AAL (B145, B170).
2. The model with a non-real top and a count rate (B183). Answered at every exponent above `½`;
   below `√x` it needs a two-sided selection with discrepancy at every frequency.
3. Is world I with a tail empty: does a finite layer force ZAL (B141)? Not from an Euler
   product over the rational primes with a count rate: the pair with a half-scale tail.
4. B13 and Landing: which input beyond one structure do they need (B157, A120)?
5. The cluster wall of the cameras (B59).
6. The half-planes of world II.

## 8. Tools

**Developed.** Greedy two-sided rounding with a window criterion; prime edits against a target
with a drift criterion; the prescribed factor of an edit series; finite layers with
multiplicities; square targets and half-scale tails; counts and zeta functions of sums of
systems; summability of integers supported on a thin set of primes; Euler products of kept
primes; exponents of sets of primes; the balance law.

**To build.** A two-sided selection of primes with square-root discrepancy at every frequency
and the Perron analysis of its count; tails that approach the line (a model for Landing); the
weighted current at a growing isolated mode; a model with both the count and a reflection.

## 9. Open research topics

- The count of a pair twin below `√x`.
- Edits whose fake zeros approach the line without reaching it (Landing), or are finitely many
  with no further one (B13 is vacuous for edits: every finite layer is realized).
- The least count remainder of a balanced edit.
- A statement about a finite layer of `ζ` that uses the exact count or the functional equation
  and fails for every edit.

## 10. Context

| Neighbour | Interface |
|---|---|
| ZeroConfigurationGeometry | worlds, abscissa laws, cameras; WZC continues its route |
| FloorFreeArithmetic | receivers of AAL, tangent data, finite strata under one structure |
| ExceptionalLayerTheory | filters, currents, atoms, the Deuring–Heilbronn question |
| SumProductArithmeticOfTheLogarithm | fakes: definition, deletions, the count remainder; WZC adds the two-sided class |
| ArithmeticPositiveDuality | one-offs over natural norms and repeated primes, the firewall |
| RHTower (Beurling systems, Landau, short intervals) | the systems, the Landau transfer, primes in `(x, x + x^α]` |
| HeckeLFunctions, HTGeometry | Dirichlet series with power-bounded partial sums; primitives on half-planes |

WZC is a programme of receivers and models. It contains no producer.

## 11. Success criteria

- World I: AAL, or a model with every structure of `ζ` that a proposed proof uses.
- World II: a half-plane at every depth, placed on the scale.
- Model theory: every finite datum, and every tail that the structures allow, realized over the
  rational primes with a count rate; each law that all models obey proved. Done above `√x` for
  finite data and for one tail; open below `√x`.

## 12. What a contribution must be

- A theorem about `ζ` in world I or world II states which structure it uses and fails on the
  models that lack it: tempered symmetric configurations, the firewall, deletion fakes, pair
  twins.
- A model keeps integer norms and a count rate, names its fake zeros exactly, and says which
  structure of `ζ` it lacks.
- A law for models is proved for every edit, not for a construction.
- Nothing in law is used as a point; no window below the logarithmic radius decides.
