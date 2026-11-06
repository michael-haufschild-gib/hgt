# Arithmetic Auxiliary Dynamics (AAD)

Namespace `GaloisForLFunctions.ArithmeticAuxiliaryDynamics`; umbrella `ArithmeticAuxiliaryDynamics.lean`.
Every theorem is unconditional. RH and zero-free strips appear only inside implications and equivalences.

## 1. Motivation

Every sign route to RH uses a positive form, a passive medium or an operator. This field asks what is left
when all of them are removed. Over `𝔽_q` something is left: Stepanov's proof. An auxiliary is constructed,
forced to vanish beyond its size, and that count gives purity, with no Hodge index. The vertical periodicity
of the zeros does the rest, and a curve has it automatically.

AAD studies how the rational integers force zeros of `ζ` by two operations with no sign:

- **Construction.** An integer object forced to vanish beyond its size.
- **Transport.** A vertical return moving a zero to new heights.

The split matches RH. Construction aims at the count (ZAL side), transport at one-offs (AAL side). A proof in
this field would be Weil's theorem in Stepanov's order over `ℤ`.

The central object is the **producer**: an integer stencil whose factorial ratio is an integer vanishing at
primes to a controlled order. The field computes what producers can and cannot do. The headline is exact:
the rate of a producer is the Mertens level, so **construction over `ℤ` has the same strength as a zero-free
region, at every scale from Vinogradov–Korobov to the quasi-Riemann hypothesis.**

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Stencil | `c : ℕ →₀ ℤ` | the ratio `∏ ⌊n/k⌋!^{c(k)}`, or the Dirichlet polynomial `D_c(s) = Σ c(k) k^{-s}` (`dirichletPoly`) |
| Multiplicity | `stepWeight c r` | `g(r) = Σ c(k) ⌊r/k⌋`, the order of the auxiliary at primes of `(n/(r+1), n/r]` |
| Increment | `increment c r` | `h = c * 1`, the discrete derivative of `g` |
| Producer | `IsProducer c m B` | balanced (`D_c(1) = 0`), `g ≥ 0`, `g ≥ m` on `[1, B)` |
| Alphabet | `AlphabetLE c K` | letters in `[1, K]` |
| Slope, excess, rate | `stencilSlope`, `excess`, `normSlope`, `rate` | `D_c′(1)`; `T = slope − m(1 − 1/B)`; `A = slope/(m(1−1/B))`; `ε = A − 1` |
| Peak, peak ratio | `peak`, `peakRatio` | `w = −D_c(0) = sup g`; `x = w/m` |
| Coefficient moments | `coeffMass`, `firstMoment`, `harmonicMass` | `Σ|c(k)|`; `Σ|c(k)|k`; `Σ|c(k)|/k` |
| Best rate | `bestRate K`, `HasRate f` | `A(K) − 1`; a family of producers of rate `≤ f(K)` |
| Möbius part | `mobiusPart T r` | `F_T(r) = −Σ_{b≤T} (μ(b)/b)(r mod b)` |
| Entangled letters | `entangled T G r`, `moebiusWeight` | `G P`, `P ≤ T` prime, all of weight `T/G` |
| Mertens level | `IsMertensLevel δ` | `|M(y)| ≤ δ(T) y` on `y ≥ T` and `|m(T)| ≤ δ(T)` |
| Fake prime measure | `IsFakePrimeMeasure K u` | nonnegative `u` with `Σ u(r)(r mod k) = log k`, `k ≤ K`: the dual variables |
| Sieve weight | `h ≥ 0`, `meanValue c` | a stencil with monotone multiplicity and `V = D_c(1) > 0` |
| Hecke dilation | `dilate j c` | `T_j : g ↦ g(⌊r/j⌋)` |
| Return set, returns on a disc | `zetaReturnSet`, `ReturnsOnDisc` | shifts with `ζ(· + iτ) ≈ ζ` on a disc |
| Hurwitz limit | `exists_gauge_point` | limits of translates, read as points of the gauge torus |
| Carlitz factorial | `carlitzSize`, `carlitzOrder` | `∏_{f monic, deg f = n} f` over `𝔽_q[T]` |

External: `stepWeight`, `IsBalanced`, `stencilSlope`, `stencilErrorConst` (ArithmeticKreinLangerTheory); `nairIntegral` (ArithmeticOfSquareRootPrecision); `adams`, `GaugeTorus` (ArithmeticGaugeTheory); `zetaReturnSet` (RHTower); `exists_abs_mertensM_le_vk_rate` (BezoutValuationIncidence); `mobiusMertens_subpower_of_zeroFree` (RHTower).

## 3. Language

- **Size against multiplicity.** The ledger: an auxiliary vanishing to order `m` on a set has size at least `m` times the counted mass.
- **Rate.** The excess of the normalized slope over the main term.
- **Peak.** The largest multiplicity, reached far out on the period.
- **Forced jump.** The increment `c(1)` at an integer divisible by no letter.
- **Entanglement.** Letters sharing a common factor, so that small residues at all letters must coincide.
- **Mertens level.** The size of `M(y)/y` and `m(T)` from `T` on.
- **Certificate.** A producer with `ε ‖s‖ < 1` certifies `ζ(s) ≠ 0` on `Re s = 1`.
- **Fibre over the identity.** A return is a limit of translates whose gauge point is `1`.
- **Siegel half, Liouville half, integrality exponent.** As in ArithmeticOfSquareRootPrecision.

## 4. Mechanisms

**Construction.**

1. **Rigidity.** `c = μ * h`, so coefficients are the Möbius inversion of the increments, and a constant window forces `c = m μ` on the window.
2. **Forced jumps.** At a rough `r`, `h(r) = c(1)`. All primes beyond the alphabet jump, and each costs slope. All multiplicity lives in fractional parts: `g(r) = −Σ c(k) {r/k}`.
3. **Palindrome.** `g(L − 1 − r) + g(r) = w` on a period, so `sup g = −D_c(0)` and the mean of `g` is `w/2`.
4. **Coefficient mass.** The pronic series weighs `g(r)` by `r^{-2}`, inversion needs `r^{-1}`: `Σ|c(k)| ≤ 2K (m(1 + log K) + (K + 1) T)`.
5. **Mellin.** `D_c(s) ζ(s) = Σ g(r)(r^{-s} − (r+1)^{-s})` on `Re s > 0`, proved by exact partial sums along multiples of a period.
6. **Mollifier.** A producer inverts `ζ` on `Re s = 1` by an integer Dirichlet polynomial: `‖D_c ζ(s) − m(1 − B^{-s})‖ ≤ ‖s‖ T`.
7. **Uncertainty.** At a zero, interpolating between `s = 1` (slope) and `s = 0` (peak): `m ‖1 − B^{-ρ}‖ ≤ ‖ρ‖ (4 + 1/β) w^{1−β} T^β`.
8. **Mean value.** `|Σ_{r<n} g(r) − n w/2| ≤ E/8`, hence `w² ≤ 144 T E` when `w ≥ 4m`: a large peak costs slope.
9. **Entanglement.** With letters `G P`: if some residue at `G P` is `≥ G`, it pays `T ≥ −F_T(r)` alone. If all are `< G`, they all equal `s = r mod G`, so `r ≡ s` modulo every squarefree `b ≤ T` and `F_T(r) = F_T(s)`: the far problem returns to the near range.
10. **Near law.** By the hyperbola method, `|F_T(s) − 1| ≤ s (|m(T)| + 2η (1 + log s))` when `|M(y)| ≤ η y` on `y ≥ T`.

**Transport.**

11. **Propagation.** A return on a disc with locally bounded translates spreads to the whole upper quadrant, by Vitali and the identity theorem.
12. **Phases.** Dirichlet coefficients are read off at large `Re s`, so every phase returns.
13. **Pole.** The translates converge to `ζ` on `Re s > 1`, so they cannot stay bounded near `s = 1`.

## 5. The questions and their answers

| # | Question | Answer | Lean |
|---|---|---|---|
| 1 | What replaces Frobenius? | Over `𝔽_q[T]`, Frobenius **is** the factorial stencil `1 − qX`: size exactly `q^n`, multiplicity exactly `1_{deg P ∣ n}`, rate `0`, because `1/ζ` is a polynomial and norms are quantized. Over `ℤ` the same object is `1/ζ` truncated to a finite stencil, every integer is a cut, and the rate is at least `c K^{-3/4}`. Nothing replaces it at rate zero. | `carlitzOrder_sub`, `card_pow_eq_sum_irrDeg`, `exists_three_quarters_floor` |
| 2 | What is the exact rate `A(K) − 1`? Is it a capacity? | `c₁ K^{-3/4} ≤ A(K) − 1 ≤ exp(−(log K)^α)` for all `α < 3/5`. It is polynomial iff `ζ` has a zero-free strip. It is a linear program whose dual is a fake prime measure, not a capacity: stencils already pass the capacity-type ceiling `e^{-0.87n}`. | `exists_bracket_bestRate`, `exists_hasRate_rpow_iff`, `IsFakePrimeMeasure.le_normSlope` |
| 3 | Where does the factor 2 of sieve parity go? | It belongs to the monotone cone. `h ≥ 0` is never balanced, so the sieve cone and the producer cone are disjoint. On the sieve side, `1_{λ=−1} = (1−λ)/2` moves the factor to `Σ c(k) λ(k) L(⌊x/k⌋)`, a stencil read against Liouville sums. A signed producer has `h < 0` somewhere and reaches slope `1`. | `eq_zero_of_balanced_of_increment_nonneg`, `two_mul_coeff_one_mul_card_le`, `two_mul_card_le_mean` |
| 4 | Why do primes recur at a zero, if they do? | They must. A return with locally bounded translates is a simultaneous return of all phases, and it is paid by a spike near `1 + iτ`. Returns at an off-line zero have density zero inside Bohr sets of positive density, so the phases are never the obstruction: the tail fails at almost every Bohr time. | `tendsto_phaseDefect_zero`, `not_bounded_near_pole`, `tendsto_phase_one_of_limit_zeta` |
| 5 | Is a single off-line zero a contradiction with `N(x) = ⌊x⌋`? | Not through a stencil identity. The mode `x^ρ/ρ` is annihilated, `D_c(ρ) ζ(ρ) = 0`, and its truncation moves any ledger by at most `w/β`, uniformly in `n`. Only a family of stencils sees a zero, through the rate law. | `hasSum_ledgerMode_eq_zero`, `IsProducer.norm_ledgerMode_self_le` |
| 6 | Does an explicit parity-selective auxiliary beat Vinogradov–Korobov? | Explicit integer producers on polynomial alphabets reach it: `exp(−(log K)^α)` for every `α < 3/5`. Past it, the rate is a zero-free region past it, and conversely through `M`. Beating VK by a stencil means certifying a stencil without its Möbius sums. | `exists_moebius_producer_of_level`, `hasRate_vk`, `exists_re_le_of_hasRate_exp` |

## 6. The scale of the rate

| Input | Output | Lean |
|---|---|---|
| `Θ < 1` | rate `K^{-(1−Θ)/32}` | `hasRate_of_zeroFree` |
| RH | rate `K^{-1/64}` | `hasRate_of_riemannHypothesis` |
| rate `K^{-a}` | `Re ρ ≤ 1 − 2a/3` | `re_le_of_hasRate_rpow_sharp` |
| rates `K^{-a}` for all `a < 3/4` | RH | `riemannHypothesis_of_hasRate_sharp` |
| any `a > 3/4` | impossible | `not_hasRate_rpow_of_three_quarters_lt` |
| rate `exp(−(log K)^α)` | `Re ρ ≤ 1 − c (log ‖ρ‖)^{1−1/α}` | `exists_re_le_of_hasRate_exp` |
| nothing (VK for `M`, `m`) | rate `exp(−(log K)^α)`, `α < 3/5` | `hasRate_vk` |

## 7. Pillar theorems

| Theorem | Lean |
|---|---|
| Rigidity: `c = μ * h`; a constant window is Möbius | `coeff_eq_moebius_increment`, `coeff_eq_of_constant_window` |
| Forced jumps and the rough floor | `increment_of_isRough`, `IsProducer.sum_rough_le_excess`, `exists_floor_normSlope` |
| Palindrome; peak; mean `w/2` | `IsProducer.stepWeight_reflect`, `IsProducer.stepWeight_le_peak`, `IsProducer.two_mul_sum_range_stepWeight` |
| Coefficient mass law; sharp Chebyshev bound | `IsProducer.coeffMass_le`, `IsProducer.psi_le_sharp` |
| Mellin transform of a stencil | `hasSum_mellin` |
| Mollifier and certified non-vanishing on `Re s = 1` | `IsProducer.norm_mollifier_le`, `IsProducer.le_norm_dirichletPoly_mul_zeta` |
| Uncertainty law; absolute constant `ε x ≥ c₀` | `IsProducer.uncertainty_law`, `IsProducer.zero_law`, `exists_uncertainty_constant` |
| Mean-value law | `abs_sum_range_stepWeight_sub_le`, `IsProducer.peak_sq_le` |
| Three-quarters floor; necessary alphabet `K ≫ |τ|^{4/3}` | `exists_three_quarters_floor`, `exists_necessary_alphabet` |
| Rational weights clear to integer producers | `exists_producer_of_weights` |
| The explicit Möbius producer | `moebiusWeight_nonneg`, `exists_moebius_producer`, `exists_moebius_producer_of_level` |
| **The rate is the Mertens level; polynomial rate ⇔ zero-free strip** | `eventually_producer_of_level`, `exists_hasRate_rpow_iff` |
| **Explicit integer producers at the VK rate** | `isMertensLevel_vk`, `hasRate_vk`, `exists_bracket_bestRate` |
| Weak duality with fake prime measures | `IsFakePrimeMeasure.hasSum_slope`, `IsFakePrimeMeasure.le_normSlope`, `mod_prime_eq` |
| Disjoint cones; parity ledger | `eq_zero_of_balanced_of_increment_nonneg`, `meanValue_pos`, `two_mul_coeff_one_mul_card_le` |
| Blindness of the ledger to zeros and to the twin | `hasSum_ledgerMode_eq_zero`, `IsProducer.norm_ledgerMode_self_le`, `IsProducer.abs_ledger_twin_le` |
| No positive Hecke amplification | `stepWeight_dilate`, `IsProducer.add_dilate`, `IsProducer.normSlope_add_dilate` |
| No early return of a producer's letters | `IsProducer.harmonicMass_le`, `IsProducer.le_of_phase_return` |
| Returns are returns of the primes; the pole's price | `tendsto_translateDiff_zero`, `tendsto_phaseDefect_zero`, `not_bounded_near_pole` |
| Hurwitz limit set embeds in the gauge torus | `exists_tendsto_phase`, `exists_gauge_point`, `coeff_eq_zero_of_hasSum_zero` |
| Frobenius as a factorial stencil; exact ledger | `carlitzOrder_sub`, `carlitzSize_eq_sum_order`, `card_pow_eq_sum_irrDeg` |
| Battery: golden obeys transport and fails the count; continuous counts have no multiplicity | `goldenL_shift`, `goldenL_deepZero`, `golden_fails_count`, `continuous_multiplicity_eq_zero` |

## 8. Tools

**Developed.**

- Stencil calculus: increments, Möbius inversion, palindrome, moments of coefficients, Hecke action.
- **Size bounds for signed stencils past sup-norm**: the mean-value law, the coefficient mass law, the uncertainty law.
- **An explicit positivizer**: entangled letters turn a signed Möbius sawtooth into an integer producer at polynomial alphabet.
- `exists_producer_of_weights`: exact clearing of rational sawtooth weights, with no rounding error.
- Dictionary between rates and zero-free regions in both directions.
- **Zero and multiplicity estimates**: order exactly one at `s = 1` for a producer (`slope > 0`); multiplicity is a Möbius image, so full multiplicity at torsion points costs support `2^{qr}` (`arithmeticAuxiliary_multiplicity_vanishes_iff`, ArithmeticHarmonicAnalysis).
- **Effective Kronecker at arithmetic scale**: the letters of a producer of rate `ε` have no simultaneous return of precision `θ` before height `1/(2ε)` unless `|ζ(1 + iτ)| ≳ 1/θ`.
- **Universality at prescribed base points, in rigid form**: a global limit of translates on the quadrant is determined by a gauge point.
- Duality: fake prime measures as certificates of floors.

**To build.**

- A bound on `E_T` or on the far tail of a stencil that does not pass through `M(x)`.
- Sharp alphabet: `K ≈ T³/δ` is what entanglement costs; a smaller entangled family would raise the RH rate.
- A local form of the transport theorem: returns on a disc with polynomially bounded translates and polynomially small error.
- The stencil of a curve with nontrivial `P(u)`: the Stepanov chain (`stepanov_order_hyperelliptic`) written as a graded stencil.

**A tool that turned out to be empty.** Siegel's lemma with parity constraints has nothing to do here. By rigidity a window is `c = μ * h` with no free parameter, and by `exists_producer_of_weights` integrality is free: the problem is a real linear program, and integer size plays no role.

## 9. Open research topics

1. **Certification without Möbius sums.** The Möbius producer is explicit. Its rate is certified by `M(x)`. Is there a non-Möbius family, with non-constant multiplicity on its window, whose rate has an independent proof? Rigidity restricts it: `h ≠ δ₁` on the window is required, at the cost of excess.
2. **The exact exponent.** Under RH the rate exponent lies in `[1/64, 3/4]`. The heuristic for optimal entanglement is `1/7`. Which `a` does RH give, and does `a` near `3/4` hold for any family?
3. **The first moment.** The floor `K^{-3/4}` comes from the worst case `|h(k)| ≈ ε K` at `k ≈ K`. Forced jumps and the structure `h(n) = f(gcd(n, L))` should exclude it. A better first-moment bound lowers the floor, and any floor below `3/4` changes the RH reading.
4. **Parity.** The ledger is blind to the twin below `w √n`. What input outside the multiplicity reads parity in a signed construction?
5. **Bounded returns.** Are there return sequences at a zero with locally bounded translates? Any such sequence lies in all Bohr sets and carries a spike at the pole. Excluding them on the top layer would give AAL.
6. **Curves in stencil language.** Is the Stepanov auxiliary the stencil of a graded `D(u)`, and what is the Mertens level of `(1−u)(1−qu)/P(u)`?
7. **A dual extremal.** Which fake prime measure attains `A(K)`, and is its limit a Beurling system?

## 10. Traps

| Trap | Fact |
|---|---|
| The alphabet alone costs the error term | The peak and coefficient mass are bounded by the alphabet and rate: `Σ|c(k)|/m ≤ 2K(1 + log K + (K+1)ε)` |
| Rate `K^{-1/2}` is RH | The scale ends at `3/4`: `a ↑ 3/4` gives RH, and RH gives at least `1/64`. The rate alone does not read `½` at `a = ½` |
| Integrality forces factorial alphabets | Far `r` are controlled by entangled letters: the alphabet is `≈ T³/δ` |
| Non-explicit Farkas stencils are all that exists | The Möbius producer is explicit; Farkas is no longer needed |
| A stencil past VK would be independent of primes | Its rate is the Mertens level. The known family contains `μ` by rigidity |
| Better sup-norm control of `g` helps | `w ≳` window: the peak is large at far `r` even for good stencils; `w² ≤ 144 T E` relates it to slope |
| The Hecke algebra amplifies | Positive dilations multiply the normalized slope by `1 + a/j` |
| The sieve's 2 obstructs producers | `h ≥ 0` is a different, disjoint cone |
| Exact identities see zeros | The ledger of the mode of a zero vanishes for every balanced stencil |
| Multiplicity sees parity | `g(⌊n/d⌋)` never reads `Ω(d)` |
| Transport proves purity | The golden fake returns exactly and fails the count |
| Multiplicity survives continuous counts | `Σ c(k) x/k = 0`: all of it is the sawtooth |
| Returns at a zero may avoid the primes | Bounded returns are returns of every phase |
| Rate is a capacity | Sawtooth moments are not potentials; capacity ceilings are passed |

## 11. Place in the research

| Direction | Programme | What |
|---|---|---|
| Uses | ArithmeticKreinLangerTheory | stencils, factorial ratios, ledgers, pronic series, ceilings |
| Uses | RHTower | Mertens bounds, `mobiusMertens_subpower_of_zeroFree`, return sets, zeta partial sums, Weil–Kloosterman function-field sums |
| Uses | BezoutValuationIncidence | Vinogradov–Korobov rates for `M` and `m` |
| Uses | HTGeometry | Vitali on connected domains, Stirling-free asymptotics |
| Uses | ArithmeticOfSquareRootPrecision | golden calibration, Liouville identity |
| Used by | ArithmeticKreinLangerTheory | `TheParityProducerHasAQuantitativeCost` takes the coefficient bound and `IsProducer` from here |

| Neighbour | Relation |
|---|---|
| ArithmeticProduction | necessary lengths and parity filters; AAD proves the corresponding laws for stencils |
| ArithmeticOfSquareRootPrecision | precision classes; the Nair lattice is the univariate face, and the stencil cone passes its ceilings |
| ArithmeticInnerFunctionTheory | its complement: it keeps positivity, since a Blaschke mass is a positive quantity |
| ArithmeticGaugeTheory, ArithmeticHarmonicAnalysis | the gauge torus and Adams multiplicity; AAD maps limits of translates into the torus |
| ArithmeticDiscreteness | repulsion amplifies a zero; AAD shows the ledger does not see it |
| ZeroConfigurationGeometry | the structure of the failure of AAL; `not_asymptoticAbscissaLaw_iff_bilateral_spectralGap` is the world transport must exclude |

Compared with Nyman–Beurling: the signed `L²` distance is RH-equivalent, and its integer-free form is in `RHTower/BaezDuarte*`. AAD works at `L¹` with `g ≥ 0`, where the uncertainty law is the interpolation between `L¹` and `L^∞`.

## 12. Success criteria and contributions

A contribution belongs to this field only if it

- uses no quadratic form with a sign, no self-adjoint operator and no Hadamard positivity;
- can be read over `𝔽_q`, where Hasse–Weil must come out in the same language;
- separates rational primes from continuous Beurling systems and from discrete near-fakes;
- is tested on the battery: golden, Liouville twin, continuous counts;
- states which scale of the rate it moves, or which class of arguments it excludes.

The programme has answered its questions in the form they were asked. It succeeds further if it either certifies a producer without Möbius sums, past a known zero-free region, or proves that no such certificate exists in a stated class.

## 13. Big picture

Construction over `ℤ` is now exact. Producers exist explicitly at polynomial alphabet, integrality costs nothing, and the rate equals the Mertens level. So the rational integers do force zeros through a factorial ratio, with no sign, and they force exactly what is known about `1/ζ`: a stencil past a zero-free region and a zero-free region past a stencil are the same object. Rigidity explains why. Every stencil with a constant window contains `μ`, because a window of constant multiplicity is the inverse of `ζ`. The Stepanov step over `𝔽_q` works because that inverse is a polynomial. Over `ℤ` it is an infinite series, and truncating it costs at least `K^{-3/4}`.

So a stencil is not a source of information about `ζ`: it is `1/ζ` in integer clothes, and the construction route has no force beyond a bound on `M(x)`, unless a certificate is found that does not pass through `M(x)`. That is the open core of the construction half.

Transport has a parallel result. A return of `ζ` at a zero with bounded translates is a return of every prime phase, so returns are never blocked by the primes. Almost-periodicity is abundant, and the tail decides. On the fake side transport is free and construction fails, which is why neither half can stand alone.
