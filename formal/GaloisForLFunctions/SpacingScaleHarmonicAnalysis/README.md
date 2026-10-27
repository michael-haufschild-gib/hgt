# Arithmetic Harmonic Analysis at the Spacing Scale (SSHA)

**One question.** The prime place and the archimedean place of `ℚ` regularize the same diagonal.
On a test built from narrow atoms at the points `log n`, `n ≤ N`, the archimedean place pays a
self-energy `log(1/w)` per unit mass and the prime place charges at most `log N`. Below the spacing
`δ_N = log(1 + 1/N)` of the atoms nothing arithmetic is seen; at the spacing the two divergences
match; beyond it the atoms overlap and the tests see the zeros. **How far does the archimedean
place pay the prime place, what does the matching leave, where does positivity stop being
unconditional, and where does a form first see the arithmetic gauge?**

SSHA is the harmonic analysis of Weil's form on the **atomic family**: the `N`-dimensional space of
tests `f_x = Σ_{n ≤ N} x_n g(· − log n)` built from one bump `g` of width `w`, read at three scales —
the width `w`, the spacing `δ_N ≍ 1/N`, the logarithmic length `log N` — and through the **overlap
ratio** `ϱ = w/δ_N`. Its organizing sentence:

> *At the spacing every divergence is matched with constant one, and what is left is a joint
> estimate between two kernels that live on different vectors: the archimedean cross kernel, large
> only at the top scale, and the prime kernel, large only across scales. A Schur weight tilted
> across scales separates them, and Weil's form is nonnegative up to the pole on every atomic test
> of width `c₀δ_N`, for every `N`. On the atomic families of one fixed bump — unbounded overlap —
> positivity is the Riemann hypothesis. The arithmetic gauge is invisible to the Markov form on
> every family closed under `|·|`, and reaches the prime form only through non-ratio lags.*

Namespace `GaloisForLFunctions.SpacingScaleHarmonicAnalysis`; umbrella
`SpacingScaleHarmonicAnalysis.lean`. Everything is unconditional; RH and its partial forms appear
only inside equivalences.

---

## 1. Place in the research

The frontier ([obstacles summary](../../../docs/reports/review-2710/obstacles-summary.md), §4)
lists what of Weil's argument over `𝔽_q` exists over `ℤ`. The global index "local + archimedean"
existed below the spacing — the archimedean self-energy pays the prime form on atomic tests of width
`N^{−O(1)}` — and was open at and beyond it. The same scale is where the arithmetic gauge first
becomes visible to Weil forms and where tests begin to see zeros up to height `≍ N`; every positive
mechanism of the corpus stops at a threshold, and the thresholds line up there. SSHA owns that
scale: Q1 of the report (how far the archimedean place pays the prime place, B3.25, B3.26), Q2 at
and beyond the spacing (gauge selectivity, B3.16), and the harmonic-analysis face of Q3 (prime
polynomials at zero ordinates, B3.24).

| Programme | What SSHA takes | What SSHA adds |
|---|---|---|
| [ArithmeticElectrostatics](../ArithmeticElectrostatics/README.md) | atomic tests, the atomic Weil prime form, `primeSum = (∫g²) P_N` below the spacing, the coupled form `Re W = M + 2C² − 2S²`, the stability law at width `N^{−O(1)}`, twins at atomic resolution | stability at a fixed fraction of the spacing; gauge blindness of the whole law |
| [RenormalizedArithmeticPotentialTheory](../RenormalizedArithmeticPotentialTheory/README.md) | the covariant counterterm `log N + O(1)` and its exact Schur rows | the finite part of the matched renormalization; tilted rows paying the archimedean cross kernel |
| [ArithmeticIntersectionTheory](../ArithmeticIntersectionTheory/README.md) | tower coordinates, gauge blindness of the finite intersection | the archimedean side at width `cδ_N`; where non-ratio lags enter |
| [RenormalizedBiarithmeticGeometry](../RenormalizedBiarithmeticGeometry/README.md) | regulators, counterterms, survival cones | a counterterm that is paid by the other place rather than survived |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md) | sign twins, square-class blindness | the diamagnetic inequality; the non-ratio lag law |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md), [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | the spline orbit and its negative-index law, Weil Grams of translates, the rational Hecke orbit | the same law on the atomic families: unbounded overlap is RH |
| `RHTower` (Weil–Markov) | `archForm = 2θ′(0)‖f‖² + levyEnergy`, `markovEnergy = archForm − primeSum`, the Markov property, Mertens' first theorem | the Lévy density bound `ω(y) ≥ 1/(2y)` with constant one |
| `HTGeometry`, `RHTower/Sieve` | harmonic row sums, Hilbert inequalities, mean values of Dirichlet polynomials | the atomic family as band-limited Dirichlet polynomials |
| [SquareRootThreshold](../SquareRootThreshold/README.md), [SelectivePositivityAndThresholdLaws](../SelectivePositivityAndThresholdLaws/README.md) | aperture positivity, the zero width as an unbounded-aperture property, Liouville failure at `23/40` | the reading of bounded overlap as a finite-aperture problem |
| [ArithmeticCriticalityTheory](../ArithmeticCriticalityTheory/README.md) | supersolutions of arithmetic jump operators | a supersolution at the spacing: the tilt `1 + n/N` |

---

## 2. Why

**Weil over `𝔽_q`.** The global Hodge index is local Hodge index at each place plus a degree
contribution, and the diagonal has finite self-intersection `2 − 2g`. Nothing is regularized.

**Over `ℤ` two divergences.** On the atomic family

* the **prime place** charges the atomic Weil prime form
  `P_N(x) = Σ_{m ∣ n} x_m x_n Λ(n/m)(n/m)^{−1/2}`, whose norm is the covariant counterterm
  `log N + O(1)` (RAPT), attained on the pole vector `n^{−1/2}`;
* the **archimedean place** charges the Lévy energy `∫_0^∞ ω(y)‖f − f(· + y)‖² dy`,
  `ω(y) = e^{−y/2}/(1 − e^{−2y}) ∼ 1/(2y)`: an atom of width `w` costs `log(1/w)` per unit mass,
  with constant one.

At `w ≍ 1/N ≍ δ_N` the leading terms coincide. Arakelov theory regularizes the diagonal by an
archimedean Green function at each point; over `ℤ` the regularization is resolved at the
log-spacing of the integers, uniformly in `n`.

**Three regimes.**

1. *Below the spacing*, `ϱ ≤ N^{−O(1)}`: the self-energy dominates every cross term (AES).
2. *At the spacing*, `ϱ = c` fixed: the atoms are disjoint, so the prime sum is exactly
   `(∫g²) P_N(x)`; but the archimedean **cross kernel** between atoms `m < n` is of size
   `w·ω(log(n/m)) ≈ w n/(n − m)`, a Hilbert-type kernel whose row at the atom `m` is
   `≈ c (m/N) log N`. The margin `log(1/(wN)) = log(1/c)` left by the matched divergences is
   bounded; the cross kernel is not. No diagonal argument closes; a joint estimate does.
3. *Beyond the spacing*, `ϱ > 1`: atoms overlap; the prime sum reads non-ratio lags
   `log k ≈ log(n/m)`; near the top scale the family contains smooth tests of aperture `≈ log ϱ`.

**Harmonic-analysis reading.** The transform of `f_x` is `h_g(z) D_x(z)` with the Dirichlet
polynomial `D_x(z) = Σ x_n e^{iz log n}`; at a zero, `D_x(γ_ρ) = Σ x_n n^{ρ−1/2}`. The test is
band-limited at `|z| ≲ 1/w`, and the explicit formula samples `|h_g D_x|²` at the zero ordinates.
Zeros at height `T` have density `log(T/2π)/2π`; a Dirichlet polynomial of length `N` has spectrum
in `[0, log N]`, Nyquist density `log N/2π`. The two match at `T ≍ N`, that is at `w ≍ δ_N`: **the
spacing scale is the Nyquist scale of the atomic family.** Below it the zeros oversample the family
and positivity is cheap; at it the joint estimate is sharp; beyond it the family is undersampled by
the zeros it can see and positivity becomes a statement about zeros.

---

## 3. Objects and language

### 3.1 The atomic family

| Object | Definition | Lean |
|---|---|---|
| atoms, spacing | `log n`, `1 ≤ n ≤ N`; `δ_N = log(1 + 1/N)`, the least gap | `atomSpacing` (AES) |
| bump, width | real `C²` `g` supported in `[0, w]` | — |
| atomic test | `f_x(u) = Σ_{n ≤ N} x_n g(u − log n)` | `atomicTest` (AES) |
| overlap ratio | `ϱ = w/δ_N`; separated `ϱ < 1`, overlapping `ϱ > 1` | — |
| relative width at `m` | `w·m`, the width in units of the local spacing `1/m` | — |
| bump autocorrelation | `G(t) = ∫ g(v) g(v + t) dv`, supported in `[−w, w]` | `bumpCorr` |
| log-gap | `s_{mn} = log n − log m` | `logGap` |
| Dirichlet polynomial | `D_x(z) = Σ x_n e^{iz log n}`; `h_{f_x} = h_g D_x` | `dirichletPoly`, `paperFT_atomicTest` |
| atom positions | `{log n : n ≥ 1}` | `logShifts` |

### 3.2 The forms and kernels

| Object | Definition | Lean |
|---|---|---|
| Markov form | `M(f) = archForm f − primeSum f` | `markovEnergy` (RHTower) |
| Lévy–Markov form | `2θ′(0)‖h‖² + levyEnergy h − primeSum h`, defined for every real `h` | `levyMarkovForm` |
| Lévy density | `ω(y) = e^{−y/2}/(1 − e^{−2y})`; `1/(2y) ≤ ω(y) ≤ e^{y/2}/(2y)` on `(0, 1]` | `archLevyDensity` |
| windowed autocorrelation | `∫ f_x(u) f_x(u + y) du = Σ x_m x_n G(y − s_{mn})` | `integral_atomicTest_mul_shift` |
| pair window | `[s − w, s + w]`, the shifts on which atoms at log-distance `s` interact | `pairWindow` |
| cross bound | `2e^{1/2} w/|s|` for `|s| ≤ 2`, else `0` | `crossBound` |
| atomic prime form | `P_N(x)`, kernel `P(m, n) = Λ(n/m)(n/m)^{−1/2}` on `m ∣ n` | `atomicWeilForm` (AES) |
| tilt | `r(n) = 1 + n/N` | `tilt` |
| tilted row | `Σ_n P(m, n) √(m/n) r(n)/r(m)` | `tiltedRow_le` |
| lag form | `Σ_{m,n} x_m x_n (G(−log k − s_{mn}) + G(log k − s_{mn}))` | `lagForm` |
| gauge factor | `ω(k) − ω(m) ω(n)` | `gaugeFactor_eq_zero_of_ratio` |
| pole moments | `C(f) = ∫ f cosh(u/2)`, `S(f) = ∫ f sinh(u/2)`; `Re W = M + 2C² − 2S²` | `re_W_atomicTest_eq` (AES) |
| constants | `c₁ = 1/(32 e^{5/2})`, `C = 2(log 4 + 4) + 1`, `c₀ = c₁ e^{−(C + 2|θ′(0)|)}` | `spacingRatio`, `spacingConstant`, `spacingWidthRatio` |

### 3.3 Words

*Below / at / beyond the spacing*: `ϱ → 0` polynomially, `ϱ` a fixed constant `< 1`, `ϱ > 1`.
*Unbounded overlap*: `ϱ → ∞` with `N`, in particular a fixed width. *Diagonal* and *cross* parts of a
form on the atomic family. *Ratio lag*: a prime-sum lag `log k` with `n = km`; *non-ratio lag*:
`|log k − s_{mn}| ≤ w` with `n ≠ km`. *Concentrated* vector: carried by one dyadic block;
*spread* vector: comparable mass on many blocks. *Nyquist margin*: `log(1/(wN))`, the finite part
left by the matched divergences. *Matched*: two divergences with the same leading constant. *Tilted
Schur test*: a Schur test whose weights vary across scales. *Paid* counterterm: one supplied by the
other place. *Gauge blind*: true for every sign twin with the same constants. *Ground state of the
gauge orbit*: the twist with the lowest bottom of the Markov form. *Form margin* versus *coefficient
margin*, *uniform* versus *non-uniform* bound, as in the report.

Every theorem states its width regime, its correction rank, its constants, and whether it is gauge
blind.

---

## 4. Mechanisms

### A. Constant one on both sides

1. **Lévy density.** `ω(y) ≥ 1/(2y)` on `(0, 1]` ⇔ `sinh y ≤ y e^{y/2}`, from the cubic Taylor
   bounds of `e^{±y}`; and `ω(y) ≤ e^{y/2}/(2y)` ⇔ `y ≤ sinh y`. A bump supported in `[0, w]` is
   moved off itself by every shift `y > w`, so `levyEnergy g ≥ log(1/w)‖g‖²`. The corpus constant
   `e^{−1/2}` falls short of `log N` at every `w ≥ N^{−e^{1/2}}`.
2. **Prime norm.** The Schur rows of `P_N` with weights `n^{−1/2}` are `A(⌊N/m⌋) + log m`, at most
   `log N + O(1)` (RAPT), and the pole vector shows the constant one is attained.

### B. The cross kernel

3. **Windowed autocorrelation.** For `y > w` the diagonal of `∫ f_x(u) f_x(u + y) du` vanishes;
   distinct atoms meet only on their pair window `|y − s_{mn}| ≤ w`, where `|G| ≤ ‖g‖²`.
4. **Cross-kernel law.** On the pair window `y ≥ |s|/2`, so `ω(y) ≤ e^{1/2}/|s|`; the window has
   length `2w`; it meets `(w, 1]` only if `|s| ≤ 2`; and `1/|log(n/m)| ≤ e² m/|n − m|`. The harmonic
   row then gives: **the cross-kernel row at the atom `m` is at most `4e^{5/2} w m (1 + log(N+1))`**
   — the relative width at that scale times `log N`. Hence
   `levyEnergy f_x ≥ ‖g‖² Σ_m x_m² (log(1/w) − 8e^{5/2} w m (1 + log(N + 1)))`.

### C. The joint estimate

5. **The tilt.** With `r(n) = 1 + n/N` the down tower of the row at `m` loses the fraction
   `(m/2N)/(1 + m/N) ≥ m/4N` of `log m` — every proper divisor lies at most half way down — while the
   up tower gains at most `(m/N) ψ(N/m) ≤ log 4 + 4` (Chebyshev). So
   `P_N(x) ≤ Σ_m x_m² (log N + 2(log 4 + 4) − (m/4N) log m)`.
6. **Payment scale by scale.** At `w ≤ c₁/N` the cross-kernel row `8e^{5/2} w m (1 + log(N+1))` is
   at most `(m/4N) log m + 3/4`: the down-tower saving pays the archimedean cross kernel atom by atom.
   Power weights `n^α` cannot do this — at an `m` with many small prime factors every divisor `m/k`
   is close to `m` on a logarithmic scale — but a weight separating `m` from `m/2` can.
7. **Spacing-scale stability.** Adding the rows:
   `M(f_x) ≥ (2θ′(0) + log(1/w) − log N − C)‖f_x‖²` for `w ≤ c₁δ_N`; hence `M ≥ 0` and
   `Re W + 2S² ≥ 0` at `w ≤ c₀δ_N`, every `N`. The correction has rank one: the pole.

### D. The gauge

8. **Diamagnetic inequality.** The Lévy energy is a Dirichlet form (`L(|f|) ≤ L(f)`) and the prime
   place enters with a positive kernel, so for every twist `|ω| ≤ 1` and every real test
   `archForm f − twistedPrimeSum ω f ≥ levyMarkovForm |f|`. Below the spacing with a nonnegative
   bump, `|f_x| = f_{|x|}`: `ζ` is the ground state of its gauge orbit on the atomic family, and every
   lower bound for `ζ` holds for every twin.
9. **Blindness of the stability law.** The proof uses only `|ω(n)Λ(n)| ≤ Λ(n)` through the gauged
   weights `ωx`, whose squares are those of `x`: every completely multiplicative sign twin satisfies
   the spacing-scale law with the same constants.
10. **Non-ratio lags.** At every width, `primeSum f_x = Σ_k Λ_k · lagForm_k(x)` and the twin's sum
    carries `ω(k)`. The difference between a twin at `x` and `ζ` at `ωx` is the lag form weighted by
    `ω(k) − ω(m)ω(n)`, which vanishes on every ratio lag (`n = km` or `m = kn`). Below the spacing
    there are no non-ratio lags; within `4δ_N` of the spacing there are.

### E. Overlap

11. **Unbounded overlap is RH.** Weil Grams of translates are invariant under a common shift, and
    every finite set of rational Hecke shifts `log(p/q)` moves into `{log n}` after the shift by the
    logarithm of a common denominator. So the spline-orbit law of AOG holds on the atomic families
    of one fixed bump: RH iff every Gram of translates `B(· − log n)` of the cubic spline is
    positive semidefinite, and the largest negative index of these Grams counts the right zeros.
12. **Overlap is aperture.** At ratio `ϱ` the atoms near the top scale form, after translation,
    approximations of `w`-smooth tests of aperture `≈ log ϱ`. Bounded overlap is therefore a
    finite-aperture problem, and finite-aperture positivity holds for configurations with off-line
    zeros (SRT); unbounded overlap reaches every test.

### F. The dictionary

13. **Atomic tests are Dirichlet polynomials.** `h_{f_x}(z) = h_g(z) D_x(z)`. The zero-side term of
    `ρ` in `W(f_x, f_x)` is `m_ρ h_g(γ_ρ) conj h_g(γ̄_ρ) · D_x(γ_ρ) conj D_x(γ̄_ρ)`, and for a zero on
    the line it is `m_ρ |h_g(γ_ρ)|² |D_x(γ_ρ)|² ≥ 0`.

---

## 5. Pillar theorems

| Pillar | Statement | Module |
|---|---|---|
| **SH1 Constant one** | `1/(2y) ≤ ω(y) ≤ e^{y/2}/(2y)`; `levyEnergy g ≥ log(1/w)‖g‖²` (`archLevyDensity_ge_inv_two_mul`, `levyEnergy_atom_ge`) | `TheSelfEnergyOfAnAtomHasConstantOne` |
| **SH2 Cross-kernel law** | windowed autocorrelation; row `≤ 4e^{5/2} w m (1 + log(N+1))`; Lévy energy of atomic tests (`levyEnergy_atomicTest_ge`) | `TheArchimedeanCrossKernel` |
| **SH3 Tilted rows** | `P_N(x) ≤ Σ x_m² (log N + 2(log 4 + 4) − (m/4N) log m)` (`atomicWeilForm_le_tilted`) | `TheTiltedPrimeRows` |
| **SH4 Stability at the spacing** | `M ≥ (2θ′(0) + log(1/(wN)) − C)‖f‖²` at `w ≤ c₁δ_N`; `M ≥ 0`, `Re W + 2S² ≥ 0` at `w ≤ c₀δ_N`; the same for every twin (`re_W_add_sinh_sq_nonneg_spacing`, `twinMarkov_atomicTest_nonneg_spacing`) | `TheStabilityLawAtTheSpacingScale` |
| **SH5 Diamagnetic inequality** | `archForm f − twistedPrimeSum ω f ≥ levyMarkovForm |f|`; `ζ` is the ground state (`diamagnetic_inequality`, `twinMarkov_ge_of_markov_ge`) | `TheDiamagneticInequality` |
| **SH6 Unbounded overlap** | RH iff all spline Grams on `{log n}` are PSD; negative index = right zeros (`riemannHypothesis_iff_splineAtomic_negIndex_eq_zero`, `zeta_splineAtomic_negIndex_law`) | `UnboundedOverlapIsTheRiemannHypothesis` |
| **SH7 Non-ratio lags** | the overlap calculus; the gauge defect lives on non-ratio lags; none below the spacing, some within `4δ_N` (`twistedPrimeSum_sub_primeSum_gauge_eq`, `nonRatio_lag_vanishes_below_spacing`, `exists_nonRatio_pair`) | `TheGaugeEntersThroughNonRatioLags` |
| **SH8 Dictionary** | `h_{f_x} = h_g D_x`; zero terms factor; on-line zeros are squares (`paperFT_atomicTest`, `Wsummand_atomicTest_onLine`) | `TheAtomicFamilyIsADirichletPolynomial` |

---

## 6. Questions and their answers

The questions of the report (§4.4), as SSHA answers them.

1. **How far does the archimedean place pay the prime place?** *To a fixed fraction of the
   spacing.* `Re W + 2S² ≥ 0` on every atomic test of width `≤ c₀δ_N`, for every `N`, with a
   rank-one correction (SH4) — B3.25 holds with `c = c₀`. On the atomic families of one fixed bump,
   where the overlap ratio is unbounded, positivity is RH (SH6). Between them lies bounded overlap,
   a finite-aperture problem (§4.E). The critical width is therefore the spacing: the endpoint
   exponent `θ = 1` is unconditional, the endpoint `θ = 0` is RH; the intermediate exponents are
   open topic 2.
2. **What is the base over `ℤ`?** At the spacing, a Schur weight: the tilt `1 + n/N` is a positive
   structure across all prime ladders on which the tower forms and the archimedean cross kernel sum
   with bounded loss (SH3, SH4). It is not Hecke covariant and need not be: it enters as a similarity
   of the Schur test, while the counterterm it serves — `log(1/w)` — is scalar and covariant. A base
   beyond the spacing is open.
3. **When does a form see the gauge?** The Markov form never favours `ζ` on a family closed under
   `|·|` (SH5), and the spacing-scale law is gauge blind (SH4). The prime form sees the gauge only
   through non-ratio lags (SH7), absent below the spacing and present at overlap ratio of order
   one. A form margin in `ζ`'s favour must therefore come from the pole — the one anti-Markovian
   term — on signed tests, or from non-ratio lags in the overlap regime. Whether the coefficient
   margin `2 log² p` becomes such a form margin is open topic 4.
4. **Does an off-line zero force alignment inside the strip?** The dictionary (SH8) writes every
   atomic test as a band-limited Dirichlet polynomial whose zero-side terms factor and are squares
   on the line. The interior implication itself is open topic 5.
5. **Which covariant regulator has a nontrivial null cone?** None is needed at the spacing: the
   divergence is paid by the archimedean place with a scalar, covariant counterterm and leaves the
   positive finite part `log(1/(wN)) − O(1)`.
6. **What is the Frobenius at infinity?** On the atomic family conjugation acts by
   `D_x(γ_ρ) ↦ D_x(γ̄_ρ)`, pairing a zero with its reflection; beyond that open.
7. **What is the arithmetic point and its period?** The atom `n = 1`, whose tilted row has no down
   tower; beyond that open.
8. **What bounds the field at right zeros off a sparse set?** Outside SSHA.
9. **How does a quantized statistic reach every window?** Outside SSHA.
10. **Is the coupled class bounded at the centre? What selects the fibre?** Outside SSHA.

---

## 7. Traps

| Trap | Truth |
|---|---|
| The self-energy constant does not matter | With `e^{−1/2}` positivity stops at `N^{−O(1)}`; constant one reaches the spacing |
| The disjoint-shift gain `log(δ_N/w)` is the self-energy | It is the part below the spacing; the shifts in `(δ_N, 1]` carry `log(1/δ_N)` through the cross kernel |
| At the spacing the cross kernel is lower order | Its row at the atom `m` is `≍ c (m/N) log N`, as large as the margin is small |
| A uniform Schur weight proves stability at the spacing | The down tower is `log m` at every row, the top rows included; only a tilt across scales pays |
| Power weights `n^{−1/2+α}` tilt enough | At `m` with many small prime factors the down tower stays `≈ log m` |
| Stability at the spacing sees zeros, so it is RH | It is a theorem; it sees zeros up to height `≍ N` with a positive Nyquist margin |
| A fixed-width family is still "near the spacing" | Its overlap ratio is unbounded, and positivity on it is RH |
| Gauge selectivity can come from the Markov form | `ζ` is its ground state; only the pole is anti-Markovian |
| Twins differ from `ζ` on every lag | The gauge factor vanishes on ratio lags; only non-ratio lags carry it |

---

## 8. Tools

**Imported.** Atomic tests, `primeSum_atomicTest`, the coupled form, twins (AES); Schur rows,
Mertens' first theorem (RAPT, RHTower); the Lévy form of `archForm`, the Markov property and the
contraction lemma (RHTower); Weil Grams, translates, the rational Hecke orbit (ACS); the spline
orbit law (AOG); harmonic row sums (RHTower/Sieve); Chebyshev's bound (Mathlib).

**Built here.** Constant-one Lévy density bounds; the self-energy of an atom; bump autocorrelations,
windowed autocorrelations and pair windows; the cross-kernel row; the tilted Schur test and tilted
rows; the spacing-scale constants and law; the Lévy–Markov form and the diamagnetic inequality;
closure of atomic tests under `|·|`; translation invariance of Weil Grams and the transfer of the
rational Hecke orbit to the atom positions; lag forms, the gauge factor and the non-ratio lag law;
the Dirichlet-polynomial factorization of atomic tests.

**To build.** The upper half of the self-energy, `levyEnergy g ≤ (log(1/w) + C_φ)‖g‖²`, and the
Robin constant `C_φ` of a bump profile; the critical constant; a quantitative aperture embedding of
bounded overlap; Riemann sums on the log-lattice with continuity of `W`; the weight of a single zero
at the spacing.

---

## 9. Open research topics

1. **The critical constant.** The largest `c*` with `Re W + (rank-one) ≥ 0` on all atomic tests of
   width `cδ_N` for every `N`. On the pole vector the finite part of `M` is
   `log(1/c) + κ_0(g) + γ + o(1)` with `κ_0(g) = 2θ′(0) + C_φ`, so `M` alone is expected to fail
   inside the separated regime; the pole decides whether `Re W + 2S²` does.
2. **Intermediate exponents.** For `w = N^{−θ}`, `0 < θ < 1`, the log-lattice Riemann sums of a
   narrow bump approximate any fixed smooth test near scales `n ≫ N^θ`, and `W` is continuous in
   the log-Sobolev norm; this indicates that positivity for all large `N` is RH for every `θ < 1`.
   A formal proof needs the continuity of `W` under these sums.
3. **Bounded overlap.** Positivity at fixed ratio `ϱ > 1`: the exact aperture `a(ϱ)` carried by the
   ratio, and positivity for `log ϱ` below the certified apertures.
4. **Gauge margin in the overlap regime.** A signed test at bounded overlap separating `ζ` from every
   twin flipping a prime `≤ p_N`, with margin bounded below, built from non-ratio lags; the
   Liouville twin at overlap ratio `e^{23/40}`.
5. **Interior anti-alignment.** Read the outward reserve of an off-line zero as a large value of the
   band-limited Dirichlet polynomial `D_x` at its ordinate, through the factorized zero terms.
6. **A covariant base beyond the spacing.** A Hecke-covariant tilt surviving overlap.
7. **Weight of one zero.** A bound for a single zero-side term on the atomic family at the spacing in
   terms of `wN`, uniform in the zero.

---

## 10. Success criteria and contribution standards

SSHA succeeds when the regimes below, at and beyond the spacing are separated by proved laws —
unconditional positivity with matched constants at the spacing, RH-strength at unbounded overlap,
an exact account of bounded overlap — and when the place where the gauge enters Weil's form is
located exactly. The first two and the location of the gauge are proved; bounded overlap and the
form margin are the open core.

A contribution is an unconditional Lean theorem about the atomic family or its overlap. It states
its **width regime** (`ϱ`), its **correction rank**, its **constants** (matched or not), and whether
it is **gauge blind**; it separates identities from signs; it says what it gives for sign twins;
and every no-go records its positive survivor.

Principles: match the constants first; the spacing is the Nyquist scale; separate concentrated and
spread vectors; tilt weights across scales, not within them; overlap is aperture; the pole is the
only anti-Markovian term; the gauge lives on non-ratio lags; a reformulation is not a reduction.
