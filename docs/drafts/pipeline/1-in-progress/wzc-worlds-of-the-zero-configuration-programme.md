# Worlds of the Zero Configuration (WZC) programme

- **ID:** wzc-programme
- **Stage:** 1-in-progress
- **Type:** PROGRAMME
- **Source:** docs/reports/review-1111/obstacles-summary.md §2.17 (questions 1–6; items B145, B170,
  B183, B141, B13, B138, B157, A120, B59)
- **Statement:** theory of the two failure worlds of RH (world I: a finite isolated top layer;
  world II: a tail), of the three atoms ZAL, B13, Landing, and of their models; search for the one
  inequality for a finite layer that uses the exact count or the functional equation.

## Goal
Folder `formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/`, umbrella
`WorldsOfTheZeroConfiguration.lean`, foundational README. Answer the questions of §2.17 or reduce
each to a named residual; a producer for AAL or ZAL is the success criterion.

## Corpus facts the programme starts from (do not redo)
- Worlds and atoms: `ExceptionalLayerTheory.riemannHypothesis_iff_three_atoms`,
  `asymptoticAbscissaLaw_orthogonal_factorization_tfae`,
  `ZeroConfigurationGeometry` `quasiRH_iff_zetaAsymptoticAbscissa_lt_one`.
- World-I receivers: FloorFreeArithmetic (non-attainment, unit gap, moments, quadrichotomy, quantum,
  tangent data of `μ`, `λ`).
- World-I models: tempered symmetric configurations with any top layer; natural-norm Euler products
  with any divisor; rational primes with repetition (`ArithmeticPositiveDuality.RationalPrimeOneOff`,
  count in the mean only); the firewall `ζ(s)/(ζ(s+1−ρ₀)ζ(s+1−ρ̄₀))`; prime-deletion fakes
  (`SumProductArithmeticOfTheLogarithm.IsIntegerNormFakeAt`, real zero on top:
  `exists_real_fake_zero_of_keptPrimeSystem`); add-only systems vanish at the real abscissa.
- Tools: `HeckeLFunctions.growthCont` (Dirichlet series with partial sums `O(x^θ)`),
  `HTGeometry.isExactOn_rightHalfPlane`, `RHTower.exists_theta_window_lower_seventeenThirtieths`
  (`θ(y+L) − θ(y) ≥ (L − (y+L)^α)/2`, `α > 17/30`), `sumSystem`, `keptPrimeSystem`,
  `keptPrimeSystem_count_sub_le_of_summable`.

## Questions and state
| # | Question | State |
|---|---|---|
| Q2 | B183: integer norms, a count rate, one non-real pair of fake zeros and no real fake zero | Theorem A in Lean at every exponent `β > ½` (unconditional). Below `√x`: Theorem B, not done (needs a two-sided selection with discrepancy at every frequency and the Perron analysis of the corpus's deletion fakes with signed weights; conditional on a zero-free half-plane like `exists_integerNormFakeAt_lt_half_of_zeroFree`) |
| Q2′ | Which edits can have a non-real top | Balance law in Lean (Theorem C); at every height above the count exponent: Theorem J in Lean (a count below `max(κ₊, κ₋)` forces `κ₊ = κ₋` or `ζ_B(κ₋) = 0`) |
| Q1 | B145 / B170: AAL | open; no producer |
| Q3 | B141: `¬AAL ⇒ ZAL` | open for `ζ`; model side answered: Theorem D in Lean (an edit of the rational primes with a count rate, an isolated pair on top and an infinite tail that does not approach the line) |
| Q2″ | Every finite datum over the rational primes | Theorem E in Lean (finite layers with multiplicities) |
| Q2‴ | Which count exponents can an edit have | Theorem F in Lean (count floor): thin at `θ` ⇒ `κ₊, κ₋ ≤ 2β(2−θ)/(1−θ)`; a fake that is a thin edit has `β > (1−θ)/(4(2−θ))`; remainder below every power ⇔ exponent zero. Theorem H in Lean: add-only edits `κ₊ ≤ β` (count exponent exactly `κ₊`); every edit `κ₊ ≤ max(β, κ₋)`. Sharp value for deletions and pair twins open |
| Q4 | B13, Landing; B157, A120 | open for `ζ`; model side: Theorem G in Lean (every sequence with real parts decreasing to `½`, any heights, is the exact fake zero set of an edit with a count rate) |
| Q5 | B59: cluster wall of the cameras | a peer session works on box cameras in MZF; not started here |
| Q6 | half-planes of world II | the questions of §2.18 for `ζ` not started here; model side: Theorem G′ in Lean (every sparse configuration: zeros on a vertical line, zeros rising to a line) |

## Lean modules (`formal/GaloisForLFunctions/WorldsOfTheZeroConfiguration/`)
| Module | Content |
|---|---|
| `GreedyRoundingOfASignedTarget` | abstract greedy rounding: thinness, discrepancy `≤ τ + B` under the window criterion |
| `PrimesRoundAnOscillatingDensity` | `target ρ`, `edit ρ`; `O(n^{Re ρ})` edited primes; discrepancy `O(n^c)` from the prime window bound |
| `TheEditSeriesHasAPrescribedZeroPair` | `exp(Σ e(p)p^{−s}) = C(s−ρ)(s−ρ̄)e^{K}`; `zetaRegular` |
| `ThinAdditionsKeepTheCountRate` | count and zeta of `sumSystem`; count rate under thin additions; integers supported on a thin set of primes are summable |
| `TwoSidedPrimeEdits` | `IsEdit`, `editSystem`, Euler product `ζ_B = ζ exp(E + Q)`, count, not norm-equivalent to the primes |
| `ANonRealPairAloneOnTopOfATwoSidedEdit` | `IsPairTwin`, `HasFakeZeroSet`; Theorem A and its unconditional corollary |
| `TheBalanceLawOfTwoSidedEdits` | Landau for `exp D`; thickness; no surplus of doubled primes; real zero for a surplus of deleted primes; balance; exponents of the greedy edit |
| `EveryFiniteLayerIsRealizedByATwoSidedEdit` | `layerTarget`, `layerFactor`, `IsLayerTwin`; every finite family `½ < Re ρ_j ≤ b < 14/15` with multiplicities |
| `TheSquareTargetOfAHalfScaleCopy` | `sqTarget a`: Dirichlet series `2Σ Λ(j) j^{−(2s−2a)}`; spikes of an interval |
| `AFiniteLayerWithATailOverTheRationalPrimes` | `tailTarget`, `tailFactor`, `IsTailTwin`, `tailSet`; Theorem D |
| `TheCountSeesTheEditedPrimes` | abstract (`a = 1 * u`): seen primes, peak of the remainder at `1/p`, Rankin bound for the weighted mass, large sieve, power form `cQ^{2β(2−θ)/(1−θ)}`; Chebyshev's identity for `u ≥ 0` |
| `TheNormCountOfAnEditIsAConvolution` | norm count `1_S * 1_T`, twin coefficients `μ_S * 1_T`, deleted primes divide no norm, doubled primes leave `u` invariant, Rankin form of the mass, count = partial sums, positive density |
| `ThinEditsPayAPowerInTheCount` | Theorem F for edits and for integer-norm systems with thin twin coefficients; exponent zero; fake zeros paid in the count |
| `AdditionsArePaidInFull` | Theorem H: dyadic counts give the exponent; Chebyshev for a system with `u ≥ 0`; add-only edits; `μ_S * 1_{Sᶜ} = 1`, the restored system; count balance |
| `EveryConfigurationThatApproachesTheLineIsRealized` | Theorem G: `landingTarget`, `landingTail`, `IsLayerTwinOn`, `IsLandingTwin`; gluing of half-planes (`exists_glue`) |
| `TheTailOfZetaBeyondACutoff` | `zetaCut N` (entire), `norm_zetaCut_le`, `cutTarget`, `lseriesHasSum_cutTarget`, the balanced cutoff `norm_zetaCut_sq_le` |
| `ACountBelowTheDeletionExponentIsARealZero` | Theorem J: `countDefect`, `exists_continuation_of_count`, `differentiableOn_editRem_of_summable`, `zero_at_expo_minus_of_count`, `balance_or_zero_of_count`, `zero_of_delete_only_of_count` |
| `EverySparseConfigurationIsRealized` | `IsFactorTwin`, `isFactorTwin_gedit` (general: any target of size `k^{−η}` with a factor), `IsSparseConfig`, Theorem G′, vertical line and rising points |

Module 2 holds the general greedy edit `gedit m` with the drift criterion (`abs_gdisc_le`,
`exists_abs_gdisc_le_rpow_of_abs_le`); module 3 the prescribed factor theorem
`exists_exp_geditSeries_eq` (hypothesis `logDeriv L = −LSeries m − Φ₀`).

Axioms of `exists_isEdit_fake_without_real_zero`, `exists_isEdit_fake_with_zero_pair`,
`exists_isEdit_fake_with_layer`, `exists_isEdit_finite_layer_with_tail`: propext,
Classical.choice, Quot.sound.

## Theorem A (two-sided prime edits with a non-real pair alone)
**Statement.** Let `½ < β₀ < 14/15`, `γ₀ ≠ 0`, `ρ₀ = β₀ + iγ₀`, `ζ(ρ₀) ≠ 0`, and `β > β₀`. There are
disjoint sets `S₋`, `S₊` of rational primes such that the system `B` with the primes of `S₋` deleted
and the primes of `S₊` doubled has: integer norms; `N_B(x) = Ax + O(x^β)`, `A > 0`; and
`(s−1)ζ_B(s) = (s−1)ζ(s)·C·(s−ρ₀)(s−ρ̄₀)·exp(H(s))` with `C ≠ 0` and `H` holomorphic on `Re s > ½`.
So the fake zeros of `B` in `Re s > ½` are exactly `ρ₀`, `ρ̄₀`, both simple; `B` has no real fake
zero.

**Proof.**
1. *Target.* `η = 1 − β₀`, `m(k) = −(k^{ρ₀−1} + k^{ρ̄₀−1}) = −2k^{−η}cos(γ₀ log k)` for `k ≥ n₀`,
   `m(k) = 0` below. For `Re s > β₀`: `Σ m(k)k^{−s} = −ζ(s+1−ρ₀) − ζ(s+1−ρ̄₀) + P(s)`, `P` a
   Dirichlet polynomial.
2. *Greedy rounding.* `δ(0) = 0`; at `k`: `d = δ(k−1) + m(k)`; if `k` is prime and `d ≥ log k`,
   put `k` in `S₊`-side (`ε(k) = 1`), if `k` is prime and `d ≤ −log k`, `ε(k) = −1`; otherwise
   `ε(k) = 0`; `δ(k) = d − ε(k) log k`. So `δ(n) = Σ_{k≤n}(m(k) − ε(k) log k)`.
3. *Thinness.* A step with `ε ≠ 0` lowers `|δ|` by `log k`, a step without raises it by at most
   `|m(k)|`: `|δ(n)| + Σ_{k≤n}|ε(k)| log k ≤ Σ_{k≤n}|m(k)| ≤ (2/β₀)n^{β₀}`.
4. *Discrepancy.* Let `α > 17/30` with the window bound `θ(y+L) − θ(y) ≥ (L − (y+L)^α)/2` for
   `y ≥ X`, and `n₀ ≥ max(X+1, 8^{1/η}, 4^{1/(1−α)})`. Call `k` low if `δ(k) ≤ log(k+1)`. A prime
   `k` without `ε(k) = 1` has `δ(k) < log k`, so it is low. Let `a ≤ n` be the last low index. On
   `(a, n]` every prime has `ε = 1`, so `δ(n) = δ(a) + Σ_{a<k≤n}m(k) − (θ(n) − θ(a))`. With
   `a' = max(a, n₀−1)`, `ℓ = n − a'`: if `ℓ ≤ 2n^α` the drift is `≤ 2n^α·2(a'+1)^{−η} ≤ 8n^{α−η}`;
   if `ℓ > 2n^α` then `θ(n) − θ(a') ≥ ℓ/4 ≥` drift. So `δ(n) ≤ log(n+1) + 8n^{α−η}`, and
   symmetrically below.
5. *Continuation.* `c(k) = ε(k) log k − m(k)` has partial sums `O(x^{c₀})`, `c₀ = α − η + ε'`; by
   summation by parts `Σ c(k)k^{−s}` is holomorphic on `Re s > c₀`. With `E(s) = Σ ε(p)p^{−s}`:
   `E′(s) = −Σ ε(k) log k·k^{−s} = ζ(s+1−ρ₀) + ζ(s+1−ρ̄₀) − P(s) − Σ c(k)k^{−s}`
   `= 1/(s−ρ₀) + 1/(s−ρ̄₀) + Φ(s)`, `Φ` holomorphic on `Re s > c₀` (`ζ(w) − 1/(w−1)` is entire).
   Let `K` be a primitive of `Φ` on the half-plane. Then `exp(E − K)/((s−ρ₀)(s−ρ̄₀))` has zero
   derivative on `Re s > 1`: `exp(E(s)) = C(s−ρ₀)(s−ρ̄₀)exp(K(s))`.
6. *Euler product.* `ζ_B(s) = ζ(s)·∏_{S₋}(1−p^{−s})·∏_{S₊}(1−p^{−s})^{−1} = ζ(s)exp(E(s) + Q(s))`,
   `Q(s) = Σ ε(p)(−log(1−p^{−s}) − p^{−s})`, absolutely convergent on `Re s > β₀/2` by step 3.
7. *Count.* `N_B(x) = Σ_{b ∈ ⟨S₊⟩} N_{ℙ∖S₋}(x/b)`; Rankin for `ℙ∖S₋` and `Σ_{b∈⟨S₊⟩} b^{−β} < ∞`.
With `α = 3/5`: `c₀ < ½` for `β₀ < 9/10`.

**Reading.** A count rate at every exponent above `½`, integer norms, multiplicities `0, 1, 2`
over the rational primes do not force a real zero on top of a finite layer: the Landau mechanism of
the deletion fakes is a property of one-sided edits. Below `√x` the count needs discrepancy at
every frequency (random selection) and a zero-free half-plane of `ζ`: Theorem B, not started.

## Theorem C (balance law) — in Lean
For an edit with a holomorphic continuation `G` of `(s−1)ζ_B` to `Re s > ½`, `κ₊`, `κ₋` the
exponents of the doubled and the deleted primes:
1. every fake zero has `Re ρ ≤ max(κ₊, κ₋, ½)`; exponents `≤ ½` give no fake;
2. `κ₊ ≤ max(κ₋, ½)`;
3. `κ₋ > max(κ₊, ½) ⇒ G(κ₋) = 0`;
4. no real zero of `G` in `(½, ∞)` ⇒ `max(κ₊, ½) = max(κ₋, ½)`; the greedy edit at a non-real
   `ρ` with `ζ(ρ) ≠ 0` has `κ₊ = κ₋ = Re ρ`.
Proof: right of both exponents `G = (s−1)ζ·exp(D₊ − D₋ + Q)`. `exp D`, `D ≥ 0` coefficientwise,
does not continue across its real abscissa (corpus `eulerFactor_abscissa_eq_zero` plus
`|exp D| ≥ 1` on the real axis). Apply to `exp D₊ = G e^{D₋−Q}/u` and to `exp D₋ = u e^{D₊+Q}/G`.

**Remark on the corpus.** `FloorFreeArithmetic.eulerFactor_abscissa_eq_zero` (AO1) has
contradictory hypotheses: a function equal to `exp D` right of `σ_c` and holomorphic on a disc
around `σ_c` does not exist. "A system that only adds primes vanishes at its real abscissa" is
vacuous; the true statement is that it does not continue.

## Theorem D (a finite layer with a tail over the rational primes) — in Lean
`exists_isEdit_finite_layer_with_tail`: for `¼ < a ≤ 3/10`, `a + ½ < Re ρ ≤ 9/10`, `β ∈ (Re ρ, 1)`
there is an edit with count `Ax + O(x^β)` and
`(s−1)ζ_B = (s−1)ζ · C(s−ρ)(s−ρ̄)·u(2s−2a)·e^{H}`, `u(w) = (w−1)ζ(w)`, `H` holomorphic on
`Re s > ½`. Fake zeros: `ρ, ρ̄` and the tail `a + z/2`, `ζ(z) = 0`; the tail is infinite
(`tailSet_infinite`, from infinitely many zeros of `ξ` and the functional equation) and lies in
`Re s < a + ½ < Re ρ`.
Target `m = −2Re k^{ρ−1} + [k = j²]·2Λ(j)j^{2a} − k^{a−1/2}`; its series is
`−ζ(s+1−ρ) − ζ(s+1−ρ̄) − 2ζ′/ζ(2s−2a) − ζ(s+½−a)`; the pole of `ζ(2s−2a)` at `a + ½` is paid by
the smooth deletion. With `α = 3/5`: smooth part `≤ 3k^{−1/10}`, spikes `≤ 10 n^{2/5}`, at most
`(n−b)/√n + 1` squares in `(b, n]`, discrepancy `O(√n)`.
Not proved: that infinitely many tail points are fake zeros in the strict sense (`ζ ≠ 0` there);
a coincidence `ζ(z) = ζ(a + z/2) = 0` is not excluded pointwise. A count of zeros would give it
(`N(T)/2 − N(T/2) → ∞`).

## Theorem E (every finite layer) — in Lean
`exists_isEdit_layerTwin`, `exists_isEdit_fake_with_layer`: for a finite family `ρ_j`, `j ∈ J`
(repetitions allowed), `½ < Re ρ_j ≤ b < 14/15`, `β ∈ (b, 1)`: an edit with count `Ax + O(x^β)`
and `(s−1)ζ_B = (s−1)ζ · C ∏_j (s−ρ_j)(s−ρ̄_j) · e^{H}`.

## Theorem F (count floor: the count sees the edited primes) — in Lean
Setting: `a = 1 * u` (`a(n)` = number of integers of norm `n`, `u` = coefficients of `ζ_B/ζ`),
`N(x) = Ax + R(x)`, `b_p(n) = Σ_{d∣n, p∤d} u(d)`. A prime is *seen* if `a(pn) − b_p(pn)` has one
sign for all `n` and absolute value `≥ a(n)`: deleted (`a ≥ 0`, `a = 0` on multiples of `p`; then
`b_p(n) ≥ a(n)`), doubled (`u(pd) = u(d)`; then `a(pn) − b_p(pn) = a(n)`).

Statement (`CountSieve.card_le_rpow`): `|R(x)| ≤ Cx^β`, `Σ_d |u(d)| d^{−θ} ≤ Z`, `0 ≤ θ < 1`,
`β + (1−θ)/(2−θ) < 1` ⇒ `#{p ≤ Q seen} ≤ c Q^{2β(2−θ)/(1−θ)}`.

Proof. `I = (X, 2X]`, `E = max_{x≤2X}|R|`, `ω = e(1/p)`, `G = Σ_{n∈I} R(n)ω^n`.
1. Summation by parts: `(1−ω)G = Σ_{n∈I}(a(n) − A)ω^n + R(X)ω^{X+1} − R(2X)ω^{2X+1}`.
2. `Σ a(n)ω^n = Σ b_p(n)ω^n + M_p`, `M_p = Σ_{n∈I, p∣n}(a(n) − b_p(n))`.
3. `Σ b_p(n)ω^n = Σ_{d≤2X, p∤d} u(d) Σ_{n∈I, d∣n} ω^n`; the inner sum is geometric with ratio a
   `p`-th root of unity `≠ 1`, so it is `≤ min(p, X/d + 1)` (`2/|ζ−1| ≤ p` from
   `p = |Σ_{j<p}(1−ζ^j)|`). Rankin: `min(p, X/d) ≤ p^{1−θ}(X/d)^θ`, so the sum is
   `≤ 3Z X^θ p^{1−θ}`.
4. `|M_p| ≥ N(2X/p) − N(X/p) ≥ A(X/p − 1) − 2E`.
5. `|1−ω| ≤ 2π/p`: `|G(1/p)| ≥ AX/8π` if `A + Ap + 4E + 3ZX^θp^{1−θ} ≤ (3/4)AX/p`.
6. Large sieve at the Farey points `1/p` (`largeSieve_fareySet_sharp`):
   `#D (AX/8π)² ≤ (X + Q²) X E²`; with `16Q² ≤ X`, `64QE ≤ AX`, `48ZQ^{2−θ}X^θ ≤ AX`:
   `#D ≤ 128π²(E/A)²`.
7. `X = ⌈M Q^{(2−θ)/(1−θ)}⌉`. ∎

Edits: `a = 1_S * 1_T`, `u = μ_S * 1_T`, `Σ|u(d)|d^{−θ} ≤ Z_S Z_T`; density `A > 0` (put the deleted
primes back: the new system represents every integer and thin additions keep the count rate).
Consequences in Lean: `κ₊, κ₋ ≤ 2β(2−θ)/(1−θ)`; `κ(1−κ) ≤ 2β(2−κ)`; exponent zero ⇔ remainder below
every power; fake zero: `(1−θ)Re ρ ≤ 2β(2−θ)`, `(1−κ₋)Re ρ ≤ 2β(2−κ₋)`; thin fake:
`β > (1−θ)/(4(2−θ))`; greedy pair twin: `Re ρ(1−Re ρ) ≤ 2β(2−Re ρ)`.

Not sharp. The loss `1−θ` is the term `Σ_{d∈(X,2X]} u(d)e(d/p)`, bounded by the number of its
terms. Tried and failed: the large sieve over all `c/p` without equidistribution (only
`Σ_{p seen} 1/p ≤ 16(E/A)²`); a second moment of that term over `p` (same exponent: bad primes
`≲ Q²X^{θ−1}`); other Chebyshev weights (terms `d ≤ x/2` uncontrolled for signed `u`); Möbius
inversion `M_u(x) = Σ μ(m)N(x/m)` (needs cancellation in `μ`). Neutral edits (delete `p`, double
the next prime) have a remainder of mean-square size `x^{κ/4}`: the `L²` exponent `κ/4` of the
sieve is the truth for them. Heuristic for a low-discrepancy charged edit: `κ/(2+2κ)` in mean
square, `κ/(1+κ)` at worst.

## B183 below `√x`: where it stands
Upper bounds go through `M_u(y) = Σ_{d≤y} u(d)`: hyperbola gives `β ≤ θ/(θ+1−c)` if
`M_u(y) = O(y^c)`; `β < ½` needs `c < 1−θ`.
- The greedy edit controls the discrepancy at frequency `0` only. From `u·log = u * λ`:
  `M_u(y)(log y + O(1)) = ∫_1^y M_u/t − 2Re[y^ρ∫_y^∞ M_u t^{−ρ−1}] + Σ_{d≤y} u(d)Δ(y/d)`; the last
  sum is bounded only through `|δ|`, and the bootstrap `b ↦ b′` has the single fixed point `b = θ`.
- A randomized rounding has computable variance, but its mean factor is a Dirichlet series over
  the primes with smooth weights: analytic with `O(log t)` growth only for
  `Re s > Re ρ − 1 + Θ_ζ`. With `Θ_ζ ≤ 7/8` there is room for `Re ρ < 9/16`; conditional on a
  zero-free half-plane, so not a theorem of the corpus.
- Growth law (not formalized): a remainder `O(x^β)` makes `ζ_B` holomorphic on `Re s > β` with
  linear growth; for `β < κ` this is a one-sided bound `Re E(σ+it) ≤ C log t` on the sparse prime
  sum left of its abscissa. Resonance gives only `Ω((log t)^{1−σ/κ})`: no contradiction. The
  smooth model (target mass on all integers) has super-polynomial growth at resonant heights;
  the edit, a sparse prime sum, does not inherit it.

## Theorem G (every configuration that approaches the line) — in Lean
`exists_isEdit_landingTwin`, `exists_isEdit_fake_with_landing`: `ρ_j = σ_j + iγ_j`, `σ_j` antitone,
`½ < σ_j`, `σ_0 < 14/15`, `inf σ_j = ½`; no condition on `γ_j`; repetitions allowed. For every
`β ∈ (σ_0, 1)` there is an edit with count `Ax + O(x^β)` whose continuation `G` of `(s−1)ζ_B` to
`Re s > ½` is, on each half-plane `Re s > σ_N`,
`(s−1)ζ · C_N ∏_{j<N}(s−ρ_j)(s−ρ̄_j) · e^{H_N}` (`IsLandingTwin`). Fake zeros: exactly
`{ρ_j, ρ̄_j}`; a fake if `ζ(ρ_j) ≠ 0` for one `j`.
- Target `m(k) = Σ_{j < log₂ k} τ_{ρ_j}(k)` (pair `j` on from `2^{j+1}`);
  `|m(k)| ≤ (4/ε) k^{σ_0+ε−1}`.
- For each `N`: `m = layerTarget_{j<N} + tail_N`, `|tail_N(k)| ≤ C_{N,x} k^{x−1}` for every
  `x > σ_N` (beyond `2^N` the pairs `N ≤ j < log₂ k`, each `≤ 2k^{σ_N−1}`; below `2^N` at most `N`
  pairs of size `≤ 2`). So `LSeries(tail_N)` is holomorphic on `Re s > σ_N` and joins `Φ₀`:
  `L_N′/L_N = −LSeries(m) − (Σ_{j<N} regular parts − LSeries(tail_N))`, `L_N = ∏_{j<N}`.
- Prescribed factor at `c = σ_N` (discrepancy `O(n^{1/2})`): `exp E = C_N L_N e^{K_N}`, `K_N`
  holomorphic on `Re s > σ_N`.
- The continuations on the half-planes agree (identity theorem from `Re s > 1`) and glue; no
  `ρ_j`, `j ≥ N`, lies in `Re s > σ_N`. ∎

Reading: infinitely many zeros off the line with real parts approaching the line (the shape that
Landing excludes for `ζ`) are compatible with an Euler product over the rational primes with
multiplicities `0, 1, 2`, integer norms and a count rate. The half-planes work because the real
parts decrease; for real parts that do not decrease (world II: `σ_j ↑ Θ∞`; a vertical line) the
later pairs have poles right of the earlier ones and the factor must be a canonical product: G′.

## Theorem G′ (every sparse configuration) — in Lean
`IsSparseConfig ρ b A`: `½ < Re ρ_j ≤ b`, `|Im ρ_j| ≥ (j+1)^A`, `b + 1/(2A) < 14/15` (then `A > 1`
and `A(2−2b) > 1`). `exists_isEdit_sparseTwin`: for `β ∈ (b + 1/(2A), 1)` an edit with count
`A′x + O(x^β)` and `(s−1)ζ_B = (s−1)ζ · C · L · e^{H}`, `L = P·P̄` the genus-one canonical
products over `ρ_j` and over `ρ̄_j`, `H` holomorphic on `Re s > ½`. Fake zeros: exactly
`{ρ_j, ρ̄_j}`. Instances in Lean: `σ ± i(j+1)^A` (a vertical line) and
`σ − (σ−½)/(j+2) ± i(j+1)^A` (real parts rising to `σ`, not attained).
- Cutoff `N_j = ⌈|Im ρ_j|⌉²`; target `m(k) = Σ_{j : N_j < k} τ_{ρ_j}(k)`; at `k` at most
  `k^{1/(2A)}` pairs are on (`(j+1)^{2A} ≤ N_j`): `|m(k)| ≤ 2k^{b+1/(2A)−1}`.
- One pair: `Σ_{k>N} τ_ρ(k)k^{−s} = −[1/(s−ρ) + Z_N(s+1−ρ)] − [conj]`,
  `Z_N(w) = ζ(w) − 1/(w−1) − Σ_{k≤N}k^{−w} = (N^{1−w} − 1)/(w−1) − w∫_N^∞{t}t^{−w−1}dt`
  (corpus `riemannZeta_eq_sum_add_tail`), so
  `|Z_N(w)| ≤ (N^{1−Re w} + 1)/|w−1| + |w|N^{−Re w}/Re w`.
- Balanced cutoff: for `Re s > ½`, `|s| ≤ T`, `t = |Im ρ| ≥ 2T + 3`, `N = ⌈t⌉²`:
  `|w−1| ≥ t/2`, `|w| ≤ 2t`, `N^{1−Re w} ≤ 2t^{2b−1}`, `N^{−Re w} ≤ t^{2b−3}`:
  `|Z_N(s+1−ρ)| ≤ 10 t^{2b−2}`. With `1/|ρ| ≤ t^{2b−2}`: the term
  `R_j(s) = Z_{N_j}(s+1−ρ_j) − 1/ρ_j` is `≤ 11 (j+1)^{−A(2−2b)}`.
- `Φ₀ = Σ_j (R_j + R̄_j)` is holomorphic on `Re s > ½` (finite head plus a tail that converges
  uniformly on `{Re s > ½, |s| < T}`).
- For `Re s > 1` the sums over `j` and `k` commute (majorant
  `2(j+1)^{−2Aθ}·k^{θ+b−1−Re s}`, `1/(2A) < θ < Re s − b`), so
  `−Σ m(k)k^{−s} − Φ₀ = Σ_j [(1/(s−ρ_j) + 1/ρ_j) + conj] = L′/L` (corpus
  `logDeriv_canonicalProductE1Indexed`).
- `isFactorTwin_gedit` (general): `|m(k)| ≤ Ak^{−η}`, `1/15 < η ≤ ½`, `L′/L = −Σ mk^{−s} − Φ₀` ⇒
  the greedy edit is a twin with the factor `L`. ∎

Reading: world II (infinitely many zeros right of a line) has models over the rational primes
with a count rate for every sparse tail; the tail need not come from a second zeta function.
The threshold `Σ|Im ρ_j|^{−(2−2b)} < ∞` is the density-hypothesis exponent `N(σ,T) ≪ T^{2(1−σ)}`:
it is where the regular parts stop converging absolutely on the line. The Lean statement uses
the stronger hypothesis `|Im ρ_j| ≥ (j+1)^A`, `b + 1/(2A) < 14/15` (the discrepancy needs
`η > 1/15`). Dense configurations exist with structure (Theorem D: `≍ T log T` fake zeros on
`Re s = a + ¼`).

## Theorem H (additions are paid in full; count balance) — in Lean
Chebyshev: `a = 1 * u` ⇒ `N(x) − 2N(x/2) = Σ_d u(d)[⌊x/d⌋ odd]`; for `u ≥ 0` the terms
`d ∈ (x/2, x]` have `⌊x/d⌋ = 1`: `Σ_{x/2<d≤x} u(d) ≤ N(x) − 2N(x/2) ≤ 3Cx^β + A`
(`CountSieve.sum_Ioc_half_le`, `CountFloor.sum_Ioc_half_le_of_count`).
1. Add-only edit (`S = ∅`): `u = 1_T ≥ 0` and `u(p) = 1` at doubled primes, so
   `#{doubled p ∈ (x/2, x]} ≤ 3Cx^β + A`, `κ₊ ≤ β` (`expo_plus_le_of_add_only`). With the count of
   an edit (`β > κ₊` is a count exponent) the count exponent of an add-only edit is exactly `κ₊`.
2. Restoring: `μ_S * 1_{Sᶜ} = 1` (`mobFn_mul_freeFn_compl`), so the system with the deleted
   primes added again has norm count `1 * 1_T` (`intCount_restored`); thin additions at
   `η > κ₋` keep the rate `η`. Chebyshev there: `κ₊ ≤ η` for every `η > max(β, κ₋)`:
   `κ₊ ≤ max(β, κ₋)` (`expo_plus_le_max`). No continuation of `ζ_B` is used (the balance law
   `κ₊ ≤ max(κ₋, ½)` needs one).
Deletions are not paid in full by this argument: for `u = μ_S` the identity has signed terms.
Open: `β ≥ κ₋/2`? (delete-only: `N(x) = Σ_d μ_S(d)⌊x/d⌋`).

## Theorem J (Landau's zero from the count) — in Lean
1. `exists_continuation_of_count`: integer norms, `N(x) = Ax + O(x^β)`, `0 ≤ β ≤ 1` ⇒
   `G(s) = A·u(s) + (s−1)·growthCont(a − A)(s)` is holomorphic on `Re s > β` and equals
   `(s−1)ζ_B(s)` on `Re s > 1` (`Σ_{k≤x}(a(k) − A) = N(⌊x⌋) − A⌊x⌋`).
2. `differentiableOn_editRem_of_summable`: `Σ|e(p)|p^{−θ} < ∞`, `θ > 0` ⇒ `Q` holomorphic on
   `Re s > θ/2` (`|r(p^{−s})| ≤ p^{−θ}/(2(1 − 2^{−θ/2}))` for `Re s ≥ θ/2`).
3. `zero_at_expo_minus_of_count`: `max(κ₊, β) < κ₋ =: κ` ⇒ `G(κ) = 0`. Take `θ = 3κ/2`,
   `c₀ = max(β, 3κ/4) < κ`; on `Re s > κ`: `G = u·exp(D₊ − D₋ + Q)`; if `G(κ) ≠ 0` then
   `exp D₋ = u e^{D₊+Q}/G` continues across `κ`, against `not_differentiableOn_exp_gdSeries`.
   The lemmas `continuation_eq`, `zero_iff_of_re_gt`, `zero_of_minus_heavy` of the balance module
   now take a base line `c₀` and the holomorphy of `Q` on `Re s > c₀`.
4. `balance_or_zero_of_count`: `β < max(κ₊, κ₋)` ⇒ `κ₊ ≤ κ₋` (Theorem H) and (`κ₊ = κ₋` or
   `G(κ₋) = 0`). Delete-only: `β < κ₋` ⇒ `ζ_B(κ₋) = 0`.

Reading: an edit beats its thickness in the count only at balance or with Landau's zero; for
delete-only edits "deletions are paid in full, or the deleted primes imitate a zero". Valid for
`κ₋ ≤ ½` too.

## Next conjectures
- C-a: a density law or a dense model: fake zeros of an edit with count exponent `β` in
  `Re s ≥ σ`, between `T^{2(1−σ)}` (realized without structure) and `T log T` (half-scale tail).
- C-b: the count exponent of a pair twin (between the floor and `Re ρ`).
- C-c: infinitely many strict fake zeros in the tail (zero count).
- C-d: a count floor for integer-norm systems that are not thin edits.

## Log
- 2026-11-11 — created; Theorem A proved on paper.
- 2026-11-12 — Theorem A and Theorem C in Lean (7 modules, wired into the umbrella and
  `MainTheorems`); README written.
- 2026-11-12 — general greedy edit and prescribed factor; Theorems D and E in Lean (10 modules).
- 2026-11-12 — Theorem F (count floor) in Lean (13 modules).
- 2026-11-12 — Theorems H (additions, count balance) and G (configurations approaching the line)
  in Lean (15 modules).
- 2026-11-12 — Theorem G′ (sparse configurations, canonical product; world II models) in Lean
  (17 modules).
- 2026-11-12 — Theorem J (count continuation, Landau's zero from the count) in Lean (18 modules).
