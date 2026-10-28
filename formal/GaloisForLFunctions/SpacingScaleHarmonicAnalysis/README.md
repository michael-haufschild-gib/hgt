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
> of width `c₀δ_N`, for every `N`; without the pole it fails at every width `cδ_N`, `c > e/(2π)`.
> As soon as the overlap ratio grows like a power of `log N` — at every width `N^{−θ}`, `θ < 1`,
> at overlap `(log N)^{1/4+ε}` for every `C²` profile and at overlap `(log N)^ε` for every smooth
> one — narrow atoms synthesize every fixed test and positivity is the Riemann hypothesis: the
> critical exponent is one, the decisive scale is bounded overlap, and RH is the statement that the
> pole remains the only negative square. The arithmetic gauge is invisible to the Markov form
> on every family closed under `|·|`, reaches the prime form only through non-ratio lags, and once
> the overlap ratio grows like a power of `log N` it is seen by exactly the twists that fail
> somewhere.*

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
polynomials at zero ordinates, B3.24). Of the report's work items it owns the Lévy synthesis (W22:
SH9–SH11, SH18–SH21), the universal threshold (W26: SH4′, SH16) and the overlap bookkeeping (W12: SH7, SH17,
with the Markov Gram at every width and its overlap law from ALG, `levyMarkovForm_atomicTest_eq`,
`markovPair_shift_ge`),
and it supplies Arithmetic Lorentzian Geometry with the separated law, the threshold and the overlap
calculus on which its Metzler and trickle-down questions are posed.

| Programme | What SSHA takes | What SSHA adds |
|---|---|---|
| [ArithmeticElectrostatics](../ArithmeticElectrostatics/README.md) | atomic tests, the atomic Weil prime form, `primeSum = (∫g²) P_N` below the spacing, the coupled form `Re W = M + 2C² − 2S²`, the stability law at width `N^{−O(1)}`, twins at atomic resolution | stability at a fixed fraction of the spacing; gauge blindness of the whole law |
| [RenormalizedArithmeticPotentialTheory](../RenormalizedArithmeticPotentialTheory/README.md) | the covariant counterterm `log N + O(1)` and its exact Schur rows; the finite part `2θ′(0) + log(1/(wN)) + κ_L + γ` of the Markov form at `wN ≤ 1/(64e²)`, the pole defect as a Dirichlet energy | tilted rows paying the archimedean cross kernel at a fixed fraction of the spacing; the exact Robin constant `2c_∞ = 2 log 2 + π/2` and the failure of the finite part beyond `e^{β/‖φ‖²}/(2π)` |
| [ArithmeticIntersectionTheory](../ArithmeticIntersectionTheory/README.md) | tower coordinates, gauge blindness of the finite intersection | the archimedean side at width `cδ_N`; where non-ratio lags enter |
| [RenormalizedBiarithmeticGeometry](../RenormalizedBiarithmeticGeometry/README.md) | regulators, counterterms, survival cones | a counterterm that is paid by the other place rather than survived |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md) | sign twins, square-class blindness | the diamagnetic inequality; the non-ratio lag law |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md), [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | the spline orbit and its negative-index law, Weil Grams of translates, the rational Hecke orbit | the same law on the atomic families: unbounded overlap is RH |
| `RHTower` (Weil–Markov) | `archForm = 2θ′(0)‖f‖² + levyEnergy`, `markovEnergy = archForm − primeSum`, the Markov property, Mertens' first theorem | the Lévy density bound `ω(y) ≥ 1/(2y)` with constant one |
| `HTGeometry`, `RHTower/Sieve` | harmonic row sums, Hilbert inequalities, mean values of Dirichlet polynomials | the atomic family as band-limited Dirichlet polynomials |
| [SquareRootThreshold](../SquareRootThreshold/README.md), [SelectivePositivityAndThresholdLaws](../SelectivePositivityAndThresholdLaws/README.md) | aperture positivity, the zero width as an unbounded-aperture property, Liouville failure at `23/40` | the reading of bounded overlap as a finite-aperture problem |
| [ArithmeticLorentzianGeometry](../ArithmeticLorentzianGeometry/README.md) | the Metzler sign of the atomic form below the spacing, its threshold at overlap ratio one, frustration beyond it; trickle-down as the remaining content of positivity | the analytic inputs it builds on: Lévy form and Markov pairing, the stability law as its base case, the universal threshold and the correction rank beyond it |
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
| dilated profile | `φ_k(s) = k φ(ks)` of a `C²` profile `φ` supported in `[−1, 1]`, `∫ φ = 1` | `dilate`, `VanishesOff` |
| overlap growth | widths `1/κ_N`, `κ_N → ∞`, `(κ_N/N)² log κ_N → 0` | `OverlapGrowth` |
| pole vector | `x_n = n^{−1/2}`, the top of the prime form | `atomicWeilForm_poleVector` |
| plateau profile | smooth, `1` on `[η, 1 − η]`, `0` off `[0, 1]` | `plateau` |

### 3.2 The forms and kernels

| Object | Definition | Lean |
|---|---|---|
| Markov form | `M(f) = archForm f − primeSum f` | `markovEnergy` (RHTower) |
| Lévy–Markov form | `2θ′(0)‖h‖² + levyEnergy h − primeSum h`, defined for every real `h` | `levyMarkovForm` |
| Lévy density | `ω(y) = e^{−y/2}/(1 − e^{−2y})`; `1/(2y) ≤ ω(y) ≤ e^{y/2}/(2y)` on `(0, 1]` | `archLevyDensity` |
| windowed autocorrelation | `∫ f_x(u) f_x(u + y) du = Σ x_m x_n G(y − s_{mn})` | `integral_atomicTest_mul_shift` |
| pair window | `[s − w, s + w]`, the shifts on which atoms at log-distance `s` interact | `pairWindow` |
| cross bound | `2e^{1/2} w/\|s\|` for `\|s\| ≤ 2`, else `0` | `crossBound` |
| atomic prime form | `P_N(x)`, kernel `P(m, n) = Λ(n/m)(n/m)^{−1/2}` on `m ∣ n` | `atomicWeilForm` (AES) |
| tilt | `r(n) = 1 + n/N` | `tilt` |
| tilted row | `Σ_n P(m, n) √(m/n) r(n)/r(m)` | `tiltedRow_le` |
| lag form | `Σ_{m,n} x_m x_n (G(−log k − s_{mn}) + G(log k − s_{mn}))` | `lagForm` |
| gauge factor | `ω(k) − ω(m) ω(n)` | `gaugeFactor_eq_zero_of_ratio` |
| pole moments | `C(f) = ∫ f cosh(u/2)`, `S(f) = ∫ f sinh(u/2)`; `Re W = M + 2C² − 2S²` | `re_W_atomicTest_eq` (AES) |
| constants | `c₁ = 1/(32 e^{5/2})`, `C = 2(log 4 + 4) + 1`, `c₀ = c₁ e^{−(C + 2\|θ′(0)\|)}` | `spacingRatio`, `spacingConstant`, `spacingWidthRatio` |
| Weil's form on real tests | `Q(f) = Re W(f, f)`; for a twist `\|λ\| ≤ Λ`, `Q_λ` | `weilQuad`, `weilQuadTw` |
| Markov form on real tests | `M(g) = Q(g) − 2 m₋(g) m₊(g)`, `m_∓(g) = ∫ g e^{∓u/2}` | `markovQuad`, `poleMomentNeg`, `poleMomentPos` |
| Robin constants | `2c_∞ = 2∫_0^1(ω − 1/(2y)) + 2∫_1^∞ ω = 2 log 2 + π/2`; shape term `β(φ) = ∫_0^1 ‖φ − φ(·+y)‖²/(2y)`; `κ_L(φ) = 2c_∞ + β(φ)/‖φ‖²` | `archRobinConstant`, `bumpRobin`, `profileRobin` |
| synthesis errors | supremum `M(k/n₀)‖φ′‖₁ + L‖φ‖₁/k`, Lipschitz and Lévy bounds | `synthErr`, `synthLip`, `synthLevy`, `weilErr` |

### 3.3 Words

*Below / at / beyond the spacing*: `ϱ → 0` polynomially, `ϱ` a fixed constant `< 1`, `ϱ > 1`.
*Unbounded overlap*: `ϱ → ∞` with `N`, in particular a fixed width. *Overlap growth of order `q`*:
widths `1/κ_N → 0` with `(κ_N/N)^q log κ_N → 0`, the overlap ratio beating `(log N)^{1/q}`
(`OverlapGrowthPow`; order `2` is `OverlapGrowth`, order `4` is `OverlapGrowthTwo`); *overlap
growth* without order means order `2`.
*Alias ripple*: the part of a synthesis at the frequencies `≍ N` of the atom lattice. *Diagonal* and *cross* parts of a
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
   moved off itself by every shift `y > w`, so `levyEnergy g ≥ log(1/w)‖g‖²`; splitting the Lévy
   integral at `w` and `1` gives the matching upper bound `(log(1/w) + O(1))‖g‖²` for dilated
   profiles. The corpus constant `e^{−1/2}` falls short of `log N` at every `w ≥ N^{−e^{1/2}}`.
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
9. **Blindness and universality of the stability law.** Below the spacing every prime pairing of an
   atomic test is an exact Hecke pairing, so a twisted prime sum with `|ω(k)| ≤ 1` is at most
   `‖g‖² P_N(|x|)`, and the tilted rows bound `P_N(|x|)` with the squares of `x`: every real twist —
   completely multiplicative or not — satisfies the spacing-scale law with the same constants. The
   separated regime of the Markov form carries no arithmetic beyond `|a(k)| ≤ Λ(k)`.
10. **Non-ratio lags.** At every width, `primeSum f_x = Σ_k Λ_k · lagForm_k(x)` and the twin's sum
    carries `ω(k)`; only the lags `log k ≤ log N + w` meet the atoms, so the sums are finite. The
    ratio lags read the bump only through `‖g‖²`: at every width
    `primeSum f_x = ‖g‖² P_N(x) + NR_w(x)`, and the non-ratio form `NR_w` is the only overlap term.
    Its rows, by a Schur test with weights `n^{−1/2}`, are `O(K)` up the tower (a window of width `w`
    around `km` holds `≤ 2km(e^w − 1)` atoms, Chebyshev) and `O(K (m/N) log m)` down it (pairs
    `kn = ℓ ≠ m` near `m` are divisors of `ℓ`, and `Σ_{d∣ℓ} Λ(d) = log ℓ`). So at bounded overlap
    the coefficient-size method weighs three rows of the same shape `(m/N) log N` — the tilt saving
    `1/4`, the archimedean cross kernel and the non-ratio lags, both `≍ K` — and closes only while
    the first dominates. The difference between a twin at `x` and `ζ` at `ωx` is the lag form weighted by
    `ω(k) − ω(m)ω(n)`, which vanishes on every ratio lag (`n = km` or `m = kn`). Below the spacing
    there are no non-ratio lags; within `4δ_N` of the spacing there are.

### E. Overlap

11. **Unbounded overlap is RH.** Weil Grams of translates are invariant under a common shift, and
    every finite set of rational Hecke shifts `log(p/q)` moves into `{log n}` after the shift by the
    logarithm of a common denominator. So the spline-orbit law of AOG holds on the atomic families
    of one fixed bump: RH iff every Gram of translates `B(· − log n)` of the cubic spline is
    positive semidefinite, and the largest negative index of these Grams counts the right zeros.
    The same holds for the spline `U_w^{⋆4}` of every fixed width `w > 0`.
12. **Narrow atoms synthesize wide tests.** Put the cell weights `x_n = ∫_{cell} F` of a fixed test
    `F` on the atoms `log n`, `n ≍ n₀`, which have gaps `≤ 1/n₀`. Against a dilated profile `φ_k` of
    width `1/k` the synthesis `S` satisfies `‖S − F‖_∞ ≤ M (k/n₀)‖φ′‖₁ + L‖φ‖₁/k` — each cell carries
    the `L¹` norm of `φ_k′`, not its supremum — and `Lip(S) = O(k)`. So the Lévy energy of `S − F` is
    `O((k/n₀ + 1/k)² log k)`.
13. **Weil's form is continuous in the Lévy norm.** In Lévy form each piece of `Q(f) = Re W(f, f)` is
    controlled by a norm of `f`: `L²`, the Lévy energy (Cauchy–Schwarz by the discriminant), the
    finitely many prime lags meeting a window, `L¹` for the pole moments. Together with 12: as soon as
    `k → ∞` and `(k/n₀)² log k → 0` the atoms reproduce `Q(F)` up to `o(1)` — under overlap growth.
    A twisted explicit formula `|λ| ≤ Λ` differs from `ζ`'s by finitely many lags on a window, so the
    same holds for every twin.
14. **The alias ripple pays `log N`.** The synthesis error `S − F` of 12 is a ripple at the
    frequencies `≍ N` of the atom lattice, and the Lévy bound charges it `log N` per unit mass. Its
    relative size is the order of the quadrature: `O(1/ϱ)` for the cell weights `∫_{cell} F`;
    `O(1/ϱ²)` for the trapezoid weights `F(a_j)(a_{j+1} − a_{j−1})/2`, for every `C²` profile —
    the Taylor expansions at the two ends of a cell cancel to first order; `O(ϱ^{−p})` for every `p`
    when the profile is smooth, with the weights `F(log n − c)/n`: in the variable `s = e^t` the
    atoms are the integers, the synthesis is the sum over the integers of `s ↦ s⁻¹ H(log s)`,
    `H(t) = F(t − c) φ_k(r + c − t)`, and Euler–Maclaurin summation to order `p` charges
    `n₀^{−p}` times `p` derivatives of `H`, each worth a factor `k`. A `C²` test is first made smooth
    by convolution with a dilated profile, at a cost `O((log m)/m²)` in the Lévy energy. So the
    synthesis converges in Weil's form once `ϱ^{2p} ≫ log N`: `ϱ ≫ √(log N)`, `(log N)^{1/4}`,
    `(log N)^ε`. At bounded ratio the atoms covering an interval of length `2a` near the top have
    relative overlap between `ϱe^{−2a}` and `ϱ`, so they reach aperture `≈ (1/2) log ϱ`, but only
    with a ripple of fixed relative size whose Lévy bound grows like `log N`: synthesis does not
    reduce bounded overlap to a finite-aperture problem.
15. **The pole is the correction.** `M(g) = Q(g) − 2 m₋(g) m₊(g)` with `m_∓ = ∫ g e^{∓u/2}`; the
    product `m₋m₊` is translation invariant, and the pole hyperplane `m₋ = 0` is a translation
    invariant hyperplane on which `M = Q`. So the synthesis carries both `M` and the hyperplane to
    the atomic families: a pole-free negative test is synthesized and moved back into the
    hyperplane by a vanishing multiple of a synthesized bump. Under overlap growth the Markov form
    inherits its unconditional negative square, and a second one exactly when RH fails.

### F. The dictionary

16. **Atomic tests are Dirichlet polynomials.** `h_{f_x}(z) = h_g(z) D_x(z)`. The zero-side term of
    `ρ` in `W(f_x, f_x)` is `m_ρ h_g(γ_ρ) conj h_g(γ̄_ρ) · D_x(γ_ρ) conj D_x(γ̄_ρ)`, and for a zero on
    the line it is `m_ρ |h_g(γ_ρ)|² |D_x(γ_ρ)|² ≥ 0`.
17. **One zero weighs at most the overlap ratio.** The two Dirichlet factors of a zero read the
    weights against `n^{σ}` and `n^{−σ}`, `σ = Re ρ − ½`; by Cauchy–Schwarz their product is at most
    `‖x‖² ((Σ n^{2|σ|})(Σ n^{−2|σ|}))^{1/2}`, and comparing the power sums with `∫ t^{±2|σ|}` gives
    `(N + 1)/√(1 − 4σ²)`. The bump factors cost `e^{2|σ| r}‖g‖₁²`. Relative to the diagonal energy of
    a dilated profile the weight is the overlap ratio times `1/(2√(β(1 − β)))`.

### G. The finite part

18. **The pole vector reads the finite part.** On `x_n = n^{−1/2}` the prime form is
    `2Σ_{n≤N} log n/n = log² N + O(1)`, since `Σ_{d∣n} Λ(d) = log n`; the diagonal is
    `H_N (2θ′(0) + log(1/w) + κ_L(φ) + O(w))` with `H_N = log N + γ + o(1)`, and for nonnegative
    weights and bump the cross correlations only lower the Lévy energy. At `w = cδ_N` the `log² N`
    cancel and the Rayleigh quotient is `(log(1/c) + κ_L(φ) + 2θ′(0) + γ) log N`, where
    `2θ′(0) + γ = −(3 log 2 + π/2 + log π)` and Euler's constant cancels. The closed
    antiderivative of `ω` gives `2c_∞ = 2 log 2 + π/2`, so the finite part is
    `log(1/c) + β(φ)/‖φ‖² − log(2π)`: the threshold is `c = e^{β(φ)/‖φ‖²}/(2π)`, and a plateau
    profile has `β(φ)/‖φ‖² → 1`.

---

## 5. Pillar theorems

| Pillar | Statement | Module |
|---|---|---|
| **SH1 Constant one** | `1/(2y) ≤ ω(y) ≤ e^{y/2}/(2y)`; `levyEnergy g ≥ log(1/w)‖g‖²` (`archLevyDensity_ge_inv_two_mul`, `levyEnergy_atom_ge`) | `TheSelfEnergyOfAnAtomHasConstantOne` |
| **SH1′ Exactly logarithmic** | `levyEnergy g ≤ (log(1/w) + C₀)‖g‖² + e^{1/2} K w ‖g‖₁` for a `K`-Lipschitz bump; for dilates `φ(·/w)` the self-energy is `(log(1/w) + O_φ(1))‖g‖²` (`levyEnergy_atom_le`, `archForm_atom_le`) | `TheSelfEnergyOfAnAtomIsExactlyLogarithmic` |
| **SH2 Cross-kernel law** | windowed autocorrelation; row `≤ 4e^{5/2} w m (1 + log(N+1))`; Lévy energy of atomic tests (`levyEnergy_atomicTest_ge`) | `TheArchimedeanCrossKernel` |
| **SH3 Tilted rows** | `P_N(x) ≤ Σ x_m² (log N + 2(log 4 + 4) − (m/4N) log m)` (`atomicWeilForm_le_tilted`) | `TheTiltedPrimeRows` |
| **SH4 Stability at the spacing** | `M ≥ (2θ′(0) + log(1/(wN)) − C)‖f‖²` at `w ≤ c₁δ_N`; `M ≥ 0`, `Re W + 2S² ≥ 0` at `w ≤ c₀δ_N`; the same for every twin (`re_W_add_sinh_sq_nonneg_spacing`, `twinMarkov_atomicTest_nonneg_spacing`) | `TheStabilityLawAtTheSpacingScale` |
| **SH4′ Universality** | the law holds for every real twist `\|ω\| ≤ 1`, multiplicative or not, and every real bump (`twistedPrimeSum_atomicTest_le`, `twistedMarkov_atomicTest_nonneg_spacing_of_abs_le`) | `TheSpacingScaleLawIsUniversal` |
| **SH5 Diamagnetic inequality** | `archForm f − twistedPrimeSum ω f ≥ levyMarkovForm \|f\|`; `ζ` is the ground state (`diamagnetic_inequality`, `twinMarkov_ge_of_markov_ge`) | `TheDiamagneticInequality` |
| **SH6 Unbounded overlap** | RH iff all spline Grams on `{log n}` are PSD, at every fixed width; negative index = right zeros (`riemannHypothesis_iff_splineAtomic_negIndex_eq_zero_of_width`, `zeta_splineAtomic_negIndex_law_of_width`) | `UnboundedOverlapIsTheRiemannHypothesis` |
| **SH7 Non-ratio lags** | the overlap calculus; the gauge defect lives on non-ratio lags; none below the spacing, some within `4δ_N` (`twistedPrimeSum_sub_primeSum_gauge_eq`, `nonRatio_lag_vanishes_below_spacing`, `exists_nonRatio_pair`) | `TheGaugeEntersThroughNonRatioLags` |
| **SH8 Dictionary** | `h_{f_x} = h_g D_x`; zero terms factor; on-line zeros are squares (`paperFT_atomicTest`, `Wsummand_atomicTest_onLine`) | `TheAtomicFamilyIsADirichletPolynomial` |
| **SH9 Lévy continuity** | `Q(f + d) ≤ Q(f) + O(‖d‖₂ + √levy d + ‖d‖₁)` on a window; `levy d ≤ e^{1/2}Kδ‖d‖₁ + (2 log(1/δ) + C₁)‖d‖₂²` (`weilQuad_add_le`, `levyEnergy_le_lipschitz`) | `WeilsFormIsContinuousInTheLevyNorm` |
| **SH10 Log-lattice synthesis** | the cell lemma `\|S − ∫F φ(· − t)\| ≤ ‖F‖_∞ h ‖φ′‖₁`; the explicit bound `Q(atomic synthesis) ≤ Q(F) + Err(n₀, k)` (`abs_cellSum_sub_le`, `exists_atomicTest_weilQuad_le`) | `TheLogLatticeSynthesizesWideTests`, `TheCriticalExponent` |
| **SH11 Overlap law** | for every `C²` profile and every width `1/κ_N` of overlap growth: RH iff for all large `N` Weil's form is nonnegative on the atomic families of width `1/κ_N`; in particular at widths `N^{−θ}`, `0 < θ < 1`, and at overlap ratio `(log N)^α`, `α > 1/2` (`riemannHypothesis_iff_atomicFamilies_nonneg_of_growth`, `riemannHypothesis_iff_atomicFamilies_nonneg`, `riemannHypothesis_iff_atomicFamilies_nonneg_log`) | `TheCriticalExponent` |
| **SH12 Gauge visibility** | for every twist `\|λ\| ≤ Λ` the same law with `Q_λ`; a twist is negative on the atomic families of every width of overlap growth for infinitely many `N` iff it is not Weil positive — unconditionally so for Liouville, every `cΛ` with `−1 ≤ c < 1`, every quadratic mixture `Λ(1 − t + tχ)`; under RH `ζ` separates from all of them there (`weilPositive_iff_atomicFamilies_nonneg`, `atomicFamilies_negative_iff`, `liouville_atomicFamilies_negative`, `scaled_atomicFamilies_negative`, `quadraticMix_atomicFamilies_negative`, `riemannHypothesis_imp_liouville_separation`) | `TheGaugeBecomesVisibleAtTheCriticalExponent` |
| **SH13 One negative square** | `M = Q − 2m₋m₊`, `M(u + iv) = M(u) + M(v)`; under overlap growth `M < 0` on some atomic test for infinitely many `N`, unconditionally (`ζ` itself): the threshold of the Markov law lies between `c₀` and overlap growth; and RH iff for all large `N`, `M ≥ 0` on the atomic tests in the pole hyperplane `m₋ = 0` (`markovQuad_eq`, `markovEnergy_eq_re_add_im`, `markov_atomicFamilies_negative`, `markovThreshold_bracket`, `riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg`) | `ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold` |
| **SH14 Weight of one zero** | `(Σ_{n≤N} n^a)(Σ_{n≤N} n^{−a}) ≤ (N+1)²/(1 − a²)`; for a bump in `[−r, r]` the term of a zero `ρ`, `σ = Re ρ − ½`, is at most `m_ρ (e^{\|σ\|r}‖g‖₁)² ‖x‖² (N+1)/√(1 − 4σ²)`; for a dilated profile, relative to the diagonal energy, at most `m_ρ e^{2\|σ\|/k}(‖φ‖₁²/‖φ‖₂²)((N+1)/k)/(2√(β(1−β)))` (`sum_rpow_mul_sum_rpow_neg_le`, `norm_Wsummand_atomicTest_le`, `norm_Wsummand_atomicTest_dilate_le`) | `TheWeightOfOneZero` |
| **SH15 The Markov form fails inside the separated regime** | `P_N(n^{−1/2}) = 2Σ_{n≤N} log n/n`; for `x, g ≥ 0` below the spacing `levyEnergy f_x ≤ ‖x‖² levyEnergy g`; `2c_∞ = 2 log 2 + π/2`; `2θ′(0) + γ = −(3 log 2 + π/2 + log π)`; on the pole vector `M < 0` for all large `N` once `c > e^{β(φ)/‖φ‖²}/(2π)`, and plateau profiles give every `c ∈ (e/(2π), 1)` (`atomicWeilForm_poleVector`, `levyEnergy_atomicTest_le`, `archRobinConstant_eq`, `markovQuad_poleVector_neg_of_threshold`, `markov_poleVector_negative_inside_separated`) | `TheMarkovFormFailsInsideTheSeparatedRegime` |
| **SH16 The universal threshold is finite** | `Re W_ω = archForm − twistedPrimeSum ω + 2C² − 2S²`; for an `L`-Lipschitz test on `[0, D]`, `levyEnergy ≤ 36DL² + 4A(D)‖f‖²`; on the level-2 dipole `g − t g(· − log 2)` of a wide bump, with `C = 0` and the sign twist aligned with the lag correlations, `Re W_ω + 2S² < 0`; with SH4′: `c₀ ≤ K_univ < ∞` (`weilQuadTw_eq_markov`, `levyEnergy_le_of_wide`, `universalThreshold_finite`, `universalThreshold_bracket`) | `TheUniversalThresholdIsFinite` |
| **SH17 The rows at bounded overlap** | at every width `primeSum f_x = ‖g‖² P_N(x) + NR_w(x)`; `\|NR_w(x)\| ≤ ‖g‖² Σ_m x_m² ρ_w(m)` with `ρ_w(m) = 2(log 4 + 4)e^{3w/2}(e^w − 1)N + 2e^{w/2}m(e^w − 1)(log m + w)`, at ratio `K` at most `2(log 4 + 4)e^{5/2}K + 2e^{3/2}K(m/N)(log m + 1)`; the prime form at ratio `K` as tilted row sums plus non-ratio rows; the summability premises of the gauge-defect identity discharged (`primeSum_atomicTest_eq_ratio_add`, `abs_nonRatioForm_le`, `nonRatioRow_le_of_ratio`, `primeSum_atomicTest_le_rows`, `twistedPrimeSum_sub_primeSum_gauge_eq_of_supp`) | `TheRowsAtBoundedOverlap`, `TheGaugeEntersThroughNonRatioLags` |
| **SH18 Second-order synthesis** | on a cell `|∫_p^q G − (q − p)(G(p) + G(q))/2| ≤ (5/4)(q − p)² ∫_p^q |G″|`; the trapezoid synthesis on the log-lattice is within `(5/4)(1/n₀)²(M₂‖φ‖₁ + 2Lk‖φ′‖₁ + Mk²‖φ″‖₁) + L‖φ‖₁/k` of `F` with Lipschitz constant `O(k)`; for every `C²` profile RH iff the atomic families are eventually nonnegative under overlap growth of order `4`, in particular at overlap ratio `(log N)^α`, `α > 1/4` (`abs_integral_sub_trap_le_two`, `abs_trapSum_sub_integral_le`, `exists_atomicTest_weilQuad_le_two`, `riemannHypothesis_iff_atomicFamilies_nonneg_of_growthTwo`, `riemannHypothesis_iff_atomicFamilies_nonneg_log_quarter`) |
| **SH19 The overlap law at every root** | `(d/ds)^j[s⁻¹H(log s)] = s^{−(j+1)}T_j(log s)`, `T_{j+1} = T_j′ − (j+1)T_j`, `‖T_p‖₁ ≤ (p+1)! Σ_{i≤p} ‖H^{(i)}‖₁`; Euler–Maclaurin on the log-lattice: `|Σ_n F(log n − c)/n · φ_k(r + c − log n) − (F ∗ φ_k)(r)| ≤ C_p(F, φ)(k/n₀)^p` for every even `p`; a negative `C²` test has a negative smooth mollification; for every smooth profile and every `q`, RH iff the atomic families are eventually nonnegative under overlap growth of order `q` — at overlap ratio `(log N)^α` for every `α > 0` (`hasDerivAt_logTowerS`, `abs_sum_logTowerS_sub_integral_le`, `abs_emSynth_dilate_sub_le`, `exists_atomicTest_weilQuad_le_em`, `exists_smooth_weilQuad_neg`, `riemannHypothesis_iff_atomicFamilies_nonneg_of_growthPow`, `riemannHypothesis_iff_atomicFamilies_nonneg_log_pos`) |
| **SH20 The gauge at every root** | a *stable form* — translation invariant, moved by `Err(e, V) → 0` under a `C²` perturbation of supremum `e` and Lévy bound `V` — is nonnegative on all tests iff it is eventually nonnegative on the atomic families of overlap growth of any order, for every smooth profile; Weil's form, every twist `\|λ\| ≤ Λ` and the Markov form are stable; so a twist is seen at overlap `(log N)^ε` iff it is not Weil positive (Liouville, `cΛ`, quadratic mixtures; under RH `ζ` separates from them there), and `M < 0` on some atomic test for infinitely many `N`, unconditionally (`StableForm`, `nonneg_iff_atomicFamilies_nonneg_of_stable`, `atomicFamilies_negative_iff_of_growthPow`, `riemannHypothesis_imp_liouville_separation_of_growthPow`, `markov_atomicFamilies_negative_of_growthPow`) |
| **SH21 The pole at every root** | for `m₋(F) = 0`, `m₋(h) > 0` and small `D₁, D₂`, `F + D₁ − t(h + D₂)` lies in the pole hyperplane with `\|t\| ≤ 2e^{R′/2}‖D₁‖₁/m₋(h)`; synthesizing a pole-free negative test and a bump with the same weights and correcting: for every smooth profile and every overlap growth of finite order, RH iff for all large `N` the Markov form is nonnegative on the atomic tests in the pole hyperplane (`exists_pole_correction`, `comb_perturbation`, `exists_smooth_poleFree_markov_neg`, `frequently_poleHyperplane_markov_neg`, `riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg_of_growthPow`) |

---

## 6. Questions and their answers

The questions of the report (§4.4), as SSHA answers them.

1. **How far does the archimedean place pay the prime place?** *To a fixed fraction of the
   spacing.* `Re W + 2S² ≥ 0` on every atomic test of width `≤ c₀δ_N`, for every `N`, with a
   rank-one correction (SH4) — B3.25 holds with `c = c₀`. The correction is needed inside the
   separated regime: the Markov form alone is negative on the pole vector at width `cδ_N` for every
   `c > e/(2π) ≈ 0.43` (SH15). *The critical exponent is `θ* = 1`*
   (B3.26): for every `θ < 1`, positivity of Weil's form on the atomic families of width `N^{−θ}` for
   all large `N` is the Riemann hypothesis (SH11), as it is at every fixed width (SH6) — and so it
   is at overlap ratio `(log N)^{1/2+ε}` (SH11), `(log N)^{1/4+ε}` for every `C²` profile (SH18) and
   `(log N)^ε` for every smooth profile (SH19). So there is no positivity statement weaker than RH
   once the overlap ratio grows like any power of `log N`: *the decisive scale is bounded overlap*.
   What remains is the window between `c₀` and the sub-power growth rates, where the alias ripple
   of every synthesis costs `log N` (§4.E) and the gauge question is open. *The universal
   threshold is bracketed and the correction rank is exactly located* (SH13, SH20): the Markov law
   `M ≥ 0` holds for every twist up to `c₀δ_N` and fails — for `ζ` itself, unconditionally — once the
   overlap ratio grows like a power of `log N`; there the Markov form has a negative square, and RH
   is the statement that it has only one, the pole (SH13 under overlap growth, SH21 at every root). The universal threshold `K_univ` — the largest ratio
   at which `Re W_ω + 2S² ≥ 0` for every twist `|ω| ≤ 1`, uniformly in `N` — satisfies
   `c₀ ≤ K_univ < ∞` (SH4′, SH16): a wide dipole on the atoms `1, 2` with vanishing cosh moment, read
   against the sign twist aligned with its lag correlations, has negative archimedean form and a
   nonnegative twisted prime sum. Beyond `K_univ` positivity must read arithmetic. At ratio `K` the
   prime form is the tilted ratio rows plus the non-ratio rows `O(K) + O(K (m/N) log m)` (SH17):
   the overlap enters the coefficient-size method as a row of the same shape as the tilt saving,
   which is why universal methods stop at a fixed ratio.
2. **What is the base over `ℤ`?** At the spacing, a Schur weight: the tilt `1 + n/N` is a positive
   structure across all prime ladders on which the tower forms and the archimedean cross kernel sum
   with bounded loss (SH3, SH4). It is not Hecke covariant and need not be: it enters as a similarity
   of the Schur test, while the counterterm it serves — `log(1/w)` — is scalar and covariant. A base
   beyond the spacing is open.
3. **When does a form see the gauge?** *Once the overlap ratio grows like a power of `log N`.* The Markov form never favours
   `ζ` on a family closed under `|·|` (SH5), and at the spacing every twist — multiplicative or
   not — satisfies the stability law with `ζ`'s constants (SH4, SH4′). The prime form sees the gauge
   only through non-ratio lags (SH7), absent below the spacing. Under overlap growth the twisted
   form is positive on the atomic families iff it is positive on all tests
   (SH12): every twist that is not Weil positive is seen there — the Liouville twin, every scaling
   `cΛ` with `c < 1`, every quadratic mixture `Λ(1 − t + tχ)` — while `ζ` holds there iff RH. So
   the source's coefficient margin becomes a form margin exactly where positivity becomes
   RH-strength, and on `ζ`'s side that margin is the Riemann hypothesis. What remains is bounded
   overlap ratio — open topic 3.
4. **Does an off-line zero force alignment inside the strip?** The dictionary (SH8) writes every
   atomic test as a band-limited Dirichlet polynomial whose zero-side terms factor and are squares
   on the line, and each zero weighs at most the overlap ratio times the diagonal energy, an
   off-line zero at most `1/(2√(β(1 − β)))` times more, uniformly in its height and in `N` (SH14).
   At the spacing no single zero can carry more than a fixed fraction of an atomic test. The
   interior implication itself is open topic 4.
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
| Widths shrinking like `N^{−θ}` stay cheap | For every `θ < 1` the atoms synthesize every fixed test; positivity is RH |
| RH-strength needs polynomial overlap | Overlap ratio `(log N)^ε` already synthesizes every fixed test, for every smooth profile |
| The log-lattice is not uniform, so quadrature on it stops at low order | In `s = e^t` the atoms are the integers: the weights `F(log n − c)/n` make the synthesis Euler–Maclaurin summation, accurate to every order |
| At bounded ratio the atoms reproduce smooth tests of aperture `≈ log ϱ` | Only up to an alias ripple of fixed relative size, whose Lévy bound grows like `log N` |
| The synthesis error is the Lipschitz constant of the bump | It is the `L¹` norm of its derivative, cell by cell: `O(k/n₀)`, not `O(k²/n₀)` |
| Gauge selectivity can come from the Markov form | `ζ` is its ground state; only the pole is anti-Markovian |
| Twins differ from `ζ` on every lag | The gauge factor vanishes on ratio lags; only non-ratio lags carry it |
| The rank-one pole correction of the stability law is an artifact of the method | The Markov form alone fails on the pole vector at width `cδ_N` for every `c > e/(2π)` |
| Universal methods might reach every bounded overlap | Some sign twist fails `Re W_ω + 2S² ≥ 0` at a finite ratio: `K_univ < ∞` |
| The Markov law fails beyond the spacing because of arithmetic | It fails for `ζ` itself once the overlap grows like a power of `log N`; RH says the failure has rank one |
| A twin positive at the spacing is positive beyond it | Liouville is stable at width `c₀δ_N` and fails at every width of overlap growth |

---

## 8. Tools

**Imported.** Atomic tests, `primeSum_atomicTest`, the coupled form, twins (AES); Schur rows,
Mertens' first theorem (RAPT, RHTower); Euler–Maclaurin summation to every order with the Bernoulli
remainder bound (RHTower, `dqpt_euler_maclaurin`); convolution calculus (Mathlib); the Lévy form of `archForm`, the Markov property and the
contraction lemma (RHTower); Weil Grams, translates, the rational Hecke orbit (ACS); the spline
orbit law (AOG); harmonic row sums (RHTower/Sieve); Chebyshev's bound (Mathlib).

**Built here.** Constant-one Lévy density bounds; the two-sided self-energy of an atom; the
domination of twisted prime sums below the spacing; bump autocorrelations,
windowed autocorrelations and pair windows; the cross-kernel row; the tilted Schur test and tilted
rows; the spacing-scale constants and law; the Lévy–Markov form and the diamagnetic inequality;
closure of atomic tests under `|·|`; translation invariance of Weil Grams and the transfer of the
rational Hecke orbit to the atom positions; lag forms, the gauge factor and the non-ratio lag law;
the Dirichlet-polynomial factorization of atomic tests; Weil's quadratic form on real tests and its
continuity in the Lévy norm; Cauchy–Schwarz for the Lévy energy; the Lévy bound for Lipschitz
perturbations; the cell lemma, log-lattice nodes, dilated profiles and the synthesis of a fixed test
with explicit error; the asymptotics of the synthesis errors; twisted quadratic forms, their
reduction to `ζ`'s on a window and their continuity; overlap growth and its two scales; the Markov
form on real tests, its real/imaginary splitting, translation invariance and continuity; the
corrected synthesis into the pole hyperplane; power sums against `∫ t^{±a}`, the Dirichlet factor by
Cauchy–Schwarz and the bump factor at complex frequencies; the exact self-energy of an atom
`levyEnergy(φ(·/w)) = (log(1/w) + κ_L(φ))‖φ(·/w)‖² + O(w)` and the archimedean pairing
`ω(s)(∫g)² + O(w)` of two separated atoms (`TheRobinConstantOfAnAtom`,
`TheArchimedeanPairingOfTwoAtoms`); the archimedean Robin constant `2c_∞ = 2 log 2 + π/2`; the
prime form of the pole vector; plateau profiles with shape term `β(φ)/‖φ‖² → 1`; the finiteness of
the lag sums; Weil's form of a twist in Markov form; the Lévy energy of wide tests; the dipole and the
twist aligned with its lag correlations; the trapezoid rule on a cell and on a lattice to first and
second order, and the trapezoid synthesis; the logarithmic tower `T_j` of `s ↦ s⁻¹ H(log s)`, the
change of variables `s = e^t`, Euler–Maclaurin summation on the log-lattice, the `L¹` bound of the
tower and the Leibniz bound; the Euler–Maclaurin synthesis with its supremum and Lipschitz bounds;
the generic motion of Weil's form under a Lipschitz perturbation; mollification to smooth tests;
overlap growth of every order; stable forms and the transfer of their signs to the atomic
families; the correction of a synthesis into the pole hyperplane by a synthesized bump.

**To build.** The cross-term density of the pole vector (the critical constant); the archimedean
cross kernel of overlapping atoms with constants, to close the joint estimate at a fixed `K`; the
alias fraction carried by a bounded overlap ratio; a large sieve over the zeros.

---

## 9. Open research topics

1. **The critical constant.** The Markov form alone has its critical constant inside the separated
   regime: `c₀ ≤ c*_M ≤ e/(2π)` (SH4, SH15). On the pole vector the finite part is
   `log(1/c) + β(φ)/‖φ‖² − log(2π)` up to the archimedean cross terms, which only help; RAPT proves
   the matching two-sided law `M ≈ (log(1/(2πwN)) + β(φ)/‖φ‖² ± ε + O(wN))‖f‖²`, the lower bound for
   all `x` at `wN ≤ 1/(64e²)` (`TheArchimedeanFinitePartIsMinusLogTwoPi`). Open: `c*_M` itself — the cross-term density on the pole vector and the
   profile minimizing `β(φ)/‖φ‖²` — and the critical constant of `Re W + 2S²`, where the pole
   decides.
2. **The window below every power of `log N`.** For smooth profiles RH-strength begins below
   `(log N)^ε` for every `ε` (SH19). The sharp threshold: the alias fraction `A(ϱ)` of the best
   synthesis (for smooth profiles `Σ_{j≠0} |φ̂(2πjϱ)|²`; for a Gevrey profile of class `s > 1`,
   `e^{−cϱ^{1/s}}`, which would carry RH-strength down to `ϱ ≫ (log log N)^s`) and whether
   RH-strength begins at `A(ϱ) log N ≍ 1`. At fixed `ϱ`: does the alias self-energy make
   Weil's form of every twist positive on the atomic tests of bounded aperture for large `N` — a
   Nyquist penalty — and what survives across all scales.
3. **Gauge margin at bounded overlap.** Under overlap growth a twin is seen iff it fails somewhere
   (SH12). At bounded overlap ratio: a signed test separating `ζ` from every twin flipping a prime
   `≤ p_N`, with margin bounded below, built from non-ratio lags — first the Liouville twin at
   overlap ratio `≈ e^{23/40}`.
4. **Interior anti-alignment.** Read the outward reserve of an off-line zero as a large value of the
   band-limited Dirichlet polynomial `D_x` at its ordinate, through the factorized zero terms.
5. **A covariant base beyond the spacing.** A Hecke-covariant tilt surviving overlap.
6. **Many zeros at once.** A large-sieve bound for the zero-side terms of the zeros in a window of
   height `T`: the zeros as a frame for the Dirichlet polynomials of length `N`, with frame constants
   as functions of `wN` and `T/N`.

---

## 10. Success criteria and contribution standards

SSHA succeeds when the regimes below, at and beyond the spacing are separated by proved laws —
unconditional positivity with matched constants at the spacing, RH-strength at every polynomial
overlap, an exact account of bounded overlap — and when the place where the gauge enters Weil's
form is located exactly. The first two (with RH-strength from overlap `(log N)^ε` on), the
location of the gauge (non-ratio lags, visible under overlap growth to exactly the twists that are
not Weil positive) and the correction rank (needed already at `cδ_N`, `c > e/(2π)`; beyond the
threshold one negative square unconditionally, only one iff RH) are proved; the window between
`c₀` and the sub-power growth rates of `ϱ`, and the form margin there, are the open core.

A contribution is an unconditional Lean theorem about the atomic family or its overlap. It states
its **width regime** (`ϱ`), its **correction rank**, its **constants** (matched or not), and whether
it is **gauge blind**; it separates identities from signs; it says what it gives for sign twins;
and every no-go records its positive survivor.

Principles: match the constants first; the spacing is the Nyquist scale; separate concentrated and
spread vectors; tilt weights across scales, not within them; overlap is aperture plus alias; the
pole is the only anti-Markovian term; the gauge lives on non-ratio lags; a reformulation is not a reduction.
