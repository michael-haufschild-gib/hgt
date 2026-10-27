# Arithmetic Harmonic Analysis at the Spacing Scale (SSHA)

**One question.** The prime place and the archimedean place of `ℚ` regularize the same diagonal.
On a test made of narrow atoms at the points `log n`, `n ≤ N`, the archimedean place pays a
self-energy `log(1/w)` per unit mass and the prime place charges at most `log N`. Below the spacing
`δ_N = log(1 + 1/N)` of the atoms nothing arithmetic is seen; at the spacing the two divergences
match; beyond it the atoms overlap and the tests see the zeros. **Exactly how far does the
archimedean place pay the prime place, what does the matching leave as a finite part, where does
positivity stop being unconditional, and where does a form first see the arithmetic gauge?**

SSHA is the harmonic analysis of Weil's form on the **atomic family**: the `N`-dimensional space of
tests `f_x = Σ_{n ≤ N} x_n g(· − log n)` built from one bump `g` of width `w`, read through its
three scales — the width `w`, the spacing `δ_N ≍ 1/N`, and the logarithmic length `log N`. Its
organizing sentence:

> *At the spacing scale every divergence is matched with constant one, and what is left is a
> joint estimate between two kernels living on different vectors: the archimedean cross kernel,
> which is large only on vectors concentrated at the top scale, and the prime kernel, which is
> large only on vectors spread across multiplicative scales. A tilted Schur weight separates them.
> Beyond the spacing the overlap ratio `w/δ_N` is the exponential of an aperture: bounded overlap
> is a finite-aperture problem, unbounded overlap is the Riemann hypothesis.*

Namespace `GaloisForLFunctions.SpacingScaleHarmonicAnalysis`; umbrella
`SpacingScaleHarmonicAnalysis.lean`. Everything is unconditional; RH and its partial forms appear
only inside equivalences.

---

## 1. Place in the research

The frontier ([obstacles summary](../../../docs/reports/review-2710/obstacles-summary.md), §4) lists
what of Weil's argument over `𝔽_q` exists over `ℤ`. The global index "local + archimedean" exists
below the spacing (the archimedean self-energy pays the prime form on atomic tests of width
`N^{−O(1)}`) and is open at and beyond it. The same scale is where the arithmetic gauge first
becomes visible to Weil forms and where tests begin to see zeros up to height `≍ N`. Every positive
mechanism of the corpus stops at a threshold, and the thresholds line up there. SSHA owns that
scale. Its questions are Q1 (how far the archimedean place pays the prime place) and Q2 (gauge
selectivity at and beyond the spacing) of the report, and the harmonic-analysis face of Q3
(alignment of prime polynomials at zero ordinates).

| Programme | What SSHA takes | What SSHA adds |
|---|---|---|
| [ArithmeticElectrostatics](../ArithmeticElectrostatics/README.md) | atomic tests, the atomic Weil prime form, `primeSum = (∫g²) P_N` below the spacing, the stability law at width `N^{−O(1)}`, the coupled form `Re W = M + 2C² − 2S²`, gauge invisibility at atomic resolution | stability at the spacing itself; the cross-kernel law; gauge blindness of the whole separated regime |
| [RenormalizedArithmeticPotentialTheory](../RenormalizedArithmeticPotentialTheory/README.md) | the covariant counterterm `log N + O(1)`, exact Schur rows (Mertens up the tower, `log m` down) | the finite part of the matched renormalization; the tilted rows that pay the archimedean cross kernel |
| [ArithmeticIntersectionTheory](../ArithmeticIntersectionTheory/README.md) | tower coordinates, the finite intersection, its gauge blindness, the spacing regulator | the archimedean side of tower coordinates at width `cδ_N` |
| [RenormalizedBiarithmeticGeometry](../RenormalizedBiarithmeticGeometry/README.md) | regulators, counterterms, survival cones, cell defects | a counterterm that is paid rather than survived |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md) | the gauge torus, sign twins, square-class blindness | the diamagnetic inequality: `ζ` is the ground state of its gauge orbit for the Markov form |
| `RHTower` (Weil–Markov) | `archForm = 2θ′(0)‖f‖² + levyEnergy`, `markovEnergy = archForm − primeSum`, the Markov property `M(|g|) ≤ M(g)`, Mertens' first theorem | sharp Lévy density bounds with constant one |
| `HTGeometry`, `RHTower/Sieve` | Montgomery–Vaughan Hilbert inequality, mean values and large values of Dirichlet polynomials | the dictionary atoms ↔ Dirichlet polynomials at `T ≍ 1/w` |
| [SquareRootThreshold](../SquareRootThreshold/README.md), [SelectivePositivityAndThresholdLaws](../SelectivePositivityAndThresholdLaws/README.md) | aperture positivity (`181/500`), the zero width as an unbounded-aperture property, Liouville failure at `23/40` | overlap ratio = exponential of an aperture; the critical width law |
| [ArithmeticCriticalityTheory](../ArithmeticCriticalityTheory/README.md) | ground states and supersolutions of arithmetic jump operators | supersolutions at the spacing: the tilted Schur weight |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | the scaling surface, orbit Hodge index, `𝔽_q` calibration | a Hodge index on the `N`-dimensional atomic family, uniform in `N` |

SSHA imports what these programmes own and proves the laws of the spacing scale.

---

## 2. Why

**Weil over `𝔽_q`.** The global Hodge index is local Hodge index at each place plus an archimedean
(here: degree) contribution, and the diagonal has finite self-intersection `2 − 2g`. Nothing has to
be regularized.

**Over `ℤ` two divergences.** On the atomic family:

* the **prime place** charges the atomic Weil prime form
  `P_N(x) = Σ_{m ∣ n} x_m x_n Λ(n/m)(n/m)^{−1/2}`, whose norm is the covariant counterterm
  `log N + O(1)` (RAPT), attained on the pole vector `n^{−1/2}`;
* the **archimedean place** charges the Lévy energy `∫_0^∞ ω(y)‖f − f(· + y)‖² dy` with
  `ω(y) = e^{−y/2}/(1 − e^{−2y}) ∼ 1/(2y)`: an atom of width `w` has self-energy `log(1/w) + O(1)`
  per unit mass, with constant one.

At `w ≍ 1/N ≍ δ_N` the two leading terms coincide. Arakelov theory regularizes the diagonal by an
archimedean Green function at each point; over `ℤ` the regularization must be resolved at the
log-spacing of the integers, uniformly in `n`.

**Three scales, three regimes.**

1. *Below the spacing* (`w ≤ N^{−O(1)}`): the self-energy dominates every cross term; positivity is
   proved (AES) and blind — every sign twin satisfies it.
2. *At the spacing* (`w = cδ_N`, `c` fixed): the atoms are still disjoint, so the prime sum is
   exactly the atomic prime form, but the archimedean **cross kernel** between atoms `m < n` is
   `≈ w·ω(log(n/m))`, a Hilbert-type kernel of size `c (n/N) log N` on the row of `n`. Diagonal
   alone no longer pays: the margin `log(1/(wN)) = log(1/c)` is bounded while the cross kernel is
   not. A joint estimate is needed.
3. *Beyond the spacing* (`w = ϱ δ_N`, `ϱ > 1`): atoms overlap; the prime sum reads non-ratio lags
   `log k ≈ log(n/m)`; the family contains smooth tests of aperture `log ϱ` near the top scale.

**Harmonic-analysis reading.** The Fourier transform of `f_x` is `ĝ(r) D_x(r)` with the Dirichlet
polynomial `D_x(r) = Σ x_n n^{−ir}`. The test is band-limited to `|r| ≲ 1/w` and the explicit
formula samples `|ĝ D_x|²` at the zero ordinates. Zeros at height `T` have density
`log(T/2π)/2π`; a Dirichlet polynomial of length `N` has spectrum in `[0, log N]`, Nyquist density
`log N/2π`. The two densities match at `T ≍ N`, that is at `w ≍ δ_N`: **the spacing scale is the
Nyquist scale of the atomic family**. Below it the zeros oversample the family and the mean-value
diagonal dominates (Montgomery–Vaughan at `T ≫ N`); at it the large-sieve and Hilbert inequalities
are sharp; beyond it the family is undersampled by the zeros it can see in a window and positivity
becomes a statement about zeros.

---

## 3. Objects and language

### 3.1 The atomic family

| Object | Definition | Lean |
|---|---|---|
| atom, spacing | `log n`, `1 ≤ n ≤ N`; `δ_N = log(1 + 1/N)`, the least gap | `atomSpacing` (AES) |
| bump, width | real `C²` `g` supported in `[0, w]` | — |
| atomic test | `f_x(u) = Σ_{n ≤ N} x_n g(u − log n)` | `atomicTest` (AES) |
| overlap ratio | `ϱ = w/δ_N`; separated `ϱ < 1`, overlapping `ϱ > 1` | — |
| relative width at `n` | `w·n`: the width measured in the local spacing `1/n` | — |
| Dirichlet polynomial | `D_x(r) = Σ x_n n^{−ir}`; `f̂_x = ĝ D_x` | — |

### 3.2 The forms

| Object | Definition | Lean |
|---|---|---|
| Markov form | `M(f) = archForm f − primeSum f` | `markovEnergy` (RHTower) |
| archimedean form | `2θ′(0)‖f‖² + L(f)`, Lévy energy `L(f) = ∫_0^∞ ω(y)‖f − f(·+y)‖² dy` | `archForm`, `levyEnergy` (RHTower) |
| Lévy density | `ω(y) = e^{−y/2}/(1 − e^{−2y})` | `archLevyDensity` |
| self-energy | `E(g) = archForm g`; `E(g) = ‖g‖²(log(1/w) + O(1))` | — |
| windowed autocorrelation | `⟨f, f(· + y)⟩ = Σ_{m,n} x_m x_n G(y − log(n/m))`, `G = g ⋆ g̃` | — |
| cross kernel | `K(m, n) = ∫_w^1 ω(y) G(y − log(n/m)) dy`, `m < n` | — |
| atomic prime form | `P_N(x)`, kernel `P(m, n) = Λ(n/m)(n/m)^{−1/2}` on `m ∣ n` | `atomicWeilForm` (AES) |
| Schur rows | up `Σ_{k ≤ N/m} Λ(k)/k`, down `Σ_{k ∣ m} Λ(k) = log m` | `row_eq` (RAPT) |
| tilted weight | `r(n) = 1 + n/N`; tilted rows `Σ (Λ(k)/k) r(mk)/r(m) + Σ_{k∣m} Λ(k) r(m/k)/r(m)` | — |
| pole moments | `C(f) = ∫ f cosh(u/2)`, `S(f) = ∫ f sinh(u/2)`; `Re W = M + 2C² − 2S²` | `re_W_atomicTest_eq` (AES) |
| sign twin | completely multiplicative `ω = ±1`; twisted prime sum with `ω(n)Λ(n)` | `twistedPrimeSum` (AES) |

### 3.3 Words

*Below / at / beyond the spacing*: `ϱ → 0` polynomially, `ϱ` bounded below `1`, `ϱ > 1`.
*Diagonal* and *cross* parts of a form on the atomic family. *Ratio lag*: a prime-sum lag `log k`
with `n = km` exactly; *non-ratio lag*: `|log k − log(n/m)| < w` with `n ≠ km`. *Concentrated*
vector: supported on one dyadic block `(N/2^{j+1}, N/2^j]`; *spread* vector: comparable mass on many
blocks. *Nyquist margin*: `log(1/(wN))`, the finite part left by the matched divergences.
*Matched*: two divergences with the same leading constant. *Tilted Schur test*: a Schur test whose
weights vary across scales. *Paid* counterterm: one supplied by another place, as opposed to one
whose null cone survives. *Gauge blind*: true for every sign twin with the same constants. *Form
margin* versus *coefficient margin*, *uniform* versus *non-uniform* bound, as in the report.

Every theorem states its width regime (`ϱ`), its correction rank, and whether it is gauge blind.

---

## 4. Mechanisms

### A. Matched constants

1. **Self-energy with constant one.** `ω(y) ≥ 1/(2y)` on `(0, 1]` (equivalently
   `y e^{y/2} ≥ sinh y`), so the shifts `y ∈ (w, 1]`, which move an atom off itself, contribute at
   least `log(1/w)` per unit mass. The corpus constant `e^{−1/2}` cannot reach the spacing:
   `e^{−1/2} log(1/w) < log N` for every `w ≥ N^{−e^{1/2}}`.
2. **Prime norm with constant one.** The Schur rows of `P_N` with weights `n^{−1/2}` are
   `A(⌊N/m⌋) + log m ≤ log N + O(1)` (RAPT).

### B. The cross kernel

3. **Windowed autocorrelation.** On `(w, 1]` the diagonal autocorrelation vanishes; only pairs
   `m < n ≤ e^{1+w} m` interact, through `G(y − log(n/m))`.
4. **Cross-kernel law.** `|K(m, n)| ≤ e^{1/2} w ‖g‖² / log(n/m)` once `w ≤ δ_N/2`, and
   `log(n/m) ≥ (n − m)/n`. Its row at `n` is at most `C w n (1 + log N) ‖g‖²`: **the cross kernel
   at a scale is the relative width at that scale times `log N`**. At `w = cδ_N` it is
   `c (n/N) log N`, maximal on the top dyadic block, where the prime form vanishes (no `m ∣ n` with
   `n/m < 2`).

### C. The joint estimate

5. **Tilted Schur test.** With `r(n) = 1 + n/N` the down-tower row loses a fraction
   `(n/2N)/(1 + n/N)` of `log n` — every proper divisor lies at most half way down — while the
   up-tower row gains at most `(n/N) ψ(N/n) ≤ C` by Chebyshev. The loss is proportional to
   `(n/N) log n`, exactly the shape of the cross-kernel row: the prime form pays the archimedean
   cross kernel scale by scale.
6. **Spacing-scale stability.** Adding the two: `M(f_x) ≥ (log(1/(wN)) − C₀)‖f_x‖²` for
   `w ≤ c₁ δ_N`, hence `M ≥ 0` and `Re W + 2S² ≥ 0` on every atomic test of width `≤ c₀ δ_N`,
   uniformly in `N`. The correction has rank one; it is the pole.

### D. Gauge

7. **Diamagnetic inequality.** The Lévy energy is a Dirichlet form, so `L(|f|) ≤ L(f)`; a twisted
   prime sum with `|a(n)| ≤ Λ(n)` is dominated by `ζ`'s prime sum of `|f|`. Hence
   `M_a(f) ≥ M(|f|)` for every real test: `ζ`'s Markov form has the lowest bottom in its gauge
   orbit on every family closed under `|·|`. Selectivity in `ζ`'s favour can come only from the
   pole, the one anti-Markovian term.
8. **Blindness of the separated regime.** The stability proof uses only `|ω(n)Λ(n)| ≤ Λ(n)`: every
   sign twin satisfies the spacing-scale stability law with the same constants.

### E. Overlap

9. **Overlap is aperture.** At overlap ratio `ϱ` the span of the atoms at scales `n ≥ ϱ/w` contains
   approximations of all `w`-smooth tests of aperture `≈ log ϱ`. Weil's form is translation
   invariant, so overlap at ratio `ϱ` carries aperture-`log ϱ` positivity.
10. **Critical width law.** Bounded `ϱ`: a finite-aperture problem, weaker than RH (finite-aperture
    positivity holds for configurations with off-line zeros). `ϱ(N) → ∞`, in particular
    `w = N^{−θ}` with `θ < 1`: positivity on the families for all large `N` gives positivity on
    every test, the Weil criterion. The critical exponent is `θ* = 1`, and at it the free parameter
    is the overlap ratio.

---

## 5. Pillar theorems

| Pillar | Statement | Module |
|---|---|---|
| **SH1 Constant-one self-energy** | `ω(y) ≥ 1/(2y)` on `(0,1]`; `L(g) ≥ log(1/w)‖g‖²` for a bump of width `w` | `TheSelfEnergyOfAnAtomHasConstantOne` |
| **SH2 Cross-kernel law** | the windowed autocorrelation of an atomic test; the cross-kernel row is `≤ C w n (1 + log N)` | `TheArchimedeanCrossKernel` |
| **SH3 Tilted prime rows** | `P_N(x) ≤ Σ x_n² (log N + C − (n/4N) log n)` | `TheTiltedPrimeRows` |
| **SH4 Spacing-scale stability** | `M(f_x) ≥ (log(1/(wN)) − C₀)‖f_x‖²` for `w ≤ c₁δ_N`; `M ≥ 0`, `Re W + 2S² ≥ 0` at `w ≤ c₀δ_N` | `TheStabilityLawAtTheSpacingScale` |
| **SH5 Diamagnetic inequality** | `M_a(f) ≥ M(|f|)` for `|a| ≤ Λ`; twins satisfy SH4 | `TheDiamagneticInequality` |
| **SH6 Critical width law** | overlap = aperture; `θ* = 1` | `TheCriticalWidthLaw` |

---

## 6. Questions the programme must answer

The questions of the report (§4.4), in SSHA terms.

1. **How far does the archimedean place pay the prime place?** To the spacing itself, with a
   fixed constant `c₀` and a rank-one correction (SH4). In the overlap regime the question becomes
   aperture positivity (SH6): bounded overlap ratio is finite aperture, unbounded overlap is RH.
   The critical exponent is `θ* = 1`.
2. **What is the base over `ℤ`?** The tilted weight `1 + n/N` is a positive structure across the
   transverse ladders on which the tower forms and the archimedean cross kernel sum with bounded
   loss — at the spacing. Whether a Hecke-covariant version exists beyond the spacing is open.
3. **When does a form see the gauge?** Not on the Markov form at any width (SH5), not anywhere in
   the separated regime (SH4 is gauge blind). The pole and the overlap regime are the only
   carriers; the aperture translation (SH6) moves the known separation of Liouville at `23/40`
   into the overlap regime.
4. **Does an off-line zero force alignment inside the strip?** SSHA supplies the dictionary: an
   atomic test is a Dirichlet polynomial band-limited at `1/w`; at the spacing a single off-line
   zero changes the form by `O(c)` per unit mass. The interior implication is open.
5. **Which covariant regulator has a nontrivial null cone?** At the spacing none is needed: the
   counterterm `log(1/w)` is scalar, covariant, supplied by the archimedean place, and leaves a
   positive finite part `log(1/c)`.
6. **What is the Frobenius at infinity?** Open; on the atomic family conjugation acts by `x ↦ x̄`
   on `D_x`.
7. **What is the arithmetic point and its period?** The atom `n = 1`, the only atom with no down
   tower; open beyond that.
8. **What bounds the field at right zeros below `√log γ` off a sparse set?** Open.
9. **How does a quantized statistic reach every window?** Open.
10. **Is the coupled class bounded at the centre? What selects the fibre?** Open.

---

## 7. Traps

| Trap | Truth |
|---|---|
| The self-energy constant does not matter | With `e^{−1/2}` positivity stops at `N^{−O(1)}`; constant one reaches the spacing |
| The disjoint-shift gain `log(δ_N/w)` is the self-energy | It is the part below the spacing; the shifts `(δ_N, 1]` carry the remaining `log(1/δ_N)` through cross terms |
| At the spacing the cross kernel is lower order | Its row is `c (n/N) log N`, as large as the margin is small |
| A uniform Schur weight proves stability at the spacing | The down tower is `log n` at every smooth `n`; only a weight tilted across scales pays |
| Power weights `n^{−1/2+α}` tilt enough | Smooth numbers keep the down tower at `log n`; the tilt must separate `n` from `n/2` |
| Stability at the spacing sees zeros, so it is RH | It is weaker: one off-line zero moves the form by `O(c)` per unit mass |
| Overlap at a fixed exponent `θ < 1` is weaker than RH | It is RH; only bounded overlap ratio is a finite-aperture problem |
| Gauge selectivity can come from the Markov form | `ζ` is the ground state of its gauge orbit for `M`; only the pole is anti-Markovian |

---

## 8. Tools

**Imported.** Atomic tests, `primeSum_atomicTest`, the coupled form (AES); exact Schur rows,
Mertens' first theorem (RAPT, RHTower); the Lévy form of `archForm`, the Markov property
(RHTower); Montgomery–Vaughan, mean values, large sieve (HTGeometry, RHTower/Sieve); aperture
positivity (SPTL, SRT).

**Built here.** Constant-one Lévy bounds; windowed autocorrelations of atomic tests; the cross-kernel
row bound; tilted Schur rows; the joint estimate; the diamagnetic inequality.

**To build.** Sharp `O(1)` terms (the Robin constant of a bump profile); certified critical
constant `c*` (the largest `c` with stability); the overlap decomposition into ratio and non-ratio
lags; the aperture embedding with explicit error.

---

## 9. Open research topics

1. **The critical constant.** The largest `c*` such that `M ≥ 0` on all atomic tests of width
   `cδ_N` for every `N`; whether `c*` reaches `1` (the end of the separated regime).
2. **Bounded overlap.** Positivity at overlap ratio `ϱ ∈ (1, e^{a})` for the certified apertures
   `a`; the exact aperture `a(ϱ)` carried by ratio `ϱ`.
3. **Gauge margin in the overlap regime.** A signed overlap test separating `ζ` from every twin
   flipping a prime `≤ p_N`, with margin bounded below; Liouville at bounded overlap.
4. **Interior anti-alignment.** Read the outward reserve of an off-line zero as a large value of a
   band-limited Dirichlet polynomial at its ordinate.
5. **A covariant base beyond the spacing.** A Hecke-covariant tilted weight that survives overlap.

---

## 10. Success criteria and contribution standards

SSHA succeeds when each question of §6 has an answer of the form theorem, sharp equivalence, or
sharp no-go with its positive survivor, and when the regimes below, at and beyond the spacing are
separated by proved laws: unconditional positivity with matched constants at the spacing, a
critical width law beyond it, and an exact account of where the gauge enters.

A contribution is an unconditional Lean theorem about the atomic family or its overlap. It states
its **width regime** (`ϱ`), its **correction rank**, its **constants** (matched or not), and whether
it is **gauge blind**; it separates computed identities from signs; it says what it gives for sign
twins and for curves over `𝔽_q`; and every no-go records its positive survivor.

Principles: match the constants first; the spacing is the Nyquist scale; separate concentrated and
spread vectors; tilt weights across scales, not within them; overlap is aperture; the pole is the
only anti-Markovian term; a reformulation is not a reduction.
