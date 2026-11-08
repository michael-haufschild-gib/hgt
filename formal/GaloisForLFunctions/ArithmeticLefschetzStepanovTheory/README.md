# Arithmetic Lefschetz–Stepanov Theory (ALST)

Namespace `GaloisForLFunctions.ArithmeticLefschetzStepanovTheory`; umbrella
`ArithmeticLefschetzStepanovTheory.lean`. Specification: §2.9 of
[the review-0811 obstacles summary](../../../docs/reports/review-0811/obstacles-summary.md).

## 1. Motivation

Weil's theorem for a curve `C/𝔽_q` has a proof with two halves that never mention a positivity of
forms:

1. **Lefschetz.** The number of fixed points of `Fⁿ` is a trace:
   `#C(𝔽_{qⁿ}) = Γ_{Fⁿ}·Δ = qⁿ + 1 − Σ αᵢⁿ`.
2. **Stepanov.** An auxiliary function `h` vanishes to order `J` at every fixed point and has pole
   order `D` at one point; the product formula `#C(𝔽_{qⁿ})·J ≤ D` gives
   `#C(𝔽_{qⁿ}) ≤ qⁿ + O(q^{n/2})` (Bombieri's form, even `n`).

Self-improvement turns the crude count into `|αᵢ| = √q`. Over `Spec ℤ` the corpus has the Lefschetz
half and the self-improvement: the smoothed Frobenius graphs `Γ_n` meet with
`c_B(log n) = Γ_1·Γ_n`, a bound `|c_B(log n)| ≤ K` at every integer degree is RH, a lower bound at the
square degrees already suffices (`SurfaceOfSpecZ`), and crude bounds on thick sets self-improve
(`InfiniteRankWeilTheory`). The missing half is Stepanov's. ALST is the theory of that half over `ℤ`:
which Frobenius, which auxiliaries, which orders of vanishing, which degrees, and which identity plays
the role of `x^q = x`.

Stepanov's count rests on three exact facts over `𝔽_q`:

| | Fact over `𝔽_q` | Role |
|---|---|---|
| (S1) | the Frobenius is a ring endomorphism fixing every rational point (`x^q = x`) | an auxiliary built from `g∘F` restricts on the points to a low-degree function |
| (S2) | the Frobenius is inseparable: `d(g^q) = 0`, and `(Σfᵢgᵢ^{p})` is a `p`-th power | vanishing at a point costs one condition but has order `p^μ` |
| (S3) | the product formula: zeros counted with order and degree equal the pole order | the count `#points·J ≤ deg h` |

ALST locates each fact over `ℤ`, proves what each gives there, and isolates what is missing. Its
working thesis: (S3) holds exactly (Bézout of `𝔾_m(ℚ)`, Jensen, the product formula); (S1) holds
exactly on the **torsion of the prime torus**, where the Galois action of `ℚ(μ_m)` is the power map;
(S2) holds exactly at every finite place `ℓ` (`ψ_ℓ(x) ≡ x^ℓ mod ℓ`) and never at the archimedean place,
where the zeros live. The archimedean Frobenius exists only approximately (returns of the prime
orbit), and approximate vanishing at returns is capped by precision (`InfiniteRankWeilTheory`).

## 2. Objects

| Object | Meaning | Corpus |
|---|---|---|
| Frobenius graph of degree `n` | `Γ_n`, the graph of `x ↦ nx` on the scaling line (Hecke correspondence `T_n`), smoothed by a test `B` | `SurfaceOfSpecZ`, `ArithmeticCastelnuovoSeveri` |
| Lefschetz number | `c_B(log n) = Γ_1·Γ_n`; atomic: `N(n) = Λ(n) + 1 + 1/(n² − 1)` | `pointCount_eq`, `orbitCorr_eq_re_lagStructure` |
| Fixed points of degree `n` | closed orbits of length `log n` (primes `p` with `pᵏ = n`, index `log p`), the archimedean fixed point (jets), the cusp (pole) | `smoothedPrime_add_smoothedArchPole_eq_orbitCorr` |
| Prime torus | `T_P = (S¹)^P` for a finite set `P` of primes; the Bohr lift `A(s) = F(p^{−s})` of a `P`-smooth Dirichlet polynomial to a Laurent polynomial `F ∈ ℤ[u_p^{±1}]` | — |
| Prime orbit | `γ(t) = (p^{−it})_{p∈P}`, a one-parameter subgroup, dense in `T_P` | `PrimeTorusTheory` |
| Torsion point | `ω ∈ μ_m^P`; its closed point `[ω]` = Galois orbit `{ω^a : a ∈ (ℤ/m)^×}`; character torsion point `ω_χ = (χ(p))_p` | — |
| Galois–Adams Frobenius | `ψ_a : u ↦ u^a` on `T_P`; on torsion of order `m` it is `σ_a ∈ Gal(ℚ(μ_m)/ℚ)` | — |
| Return | `δ`-return to `ω`: `\|p^{−it} − ω_p\| ≤ δ` for `p ∈ P`; returns to `1` freeze `P`-smooth polynomials | `IsReturn`, `norm_dpoly_near_return_le` |
| Frobenius orbit of a return | the dilates `a·t`, `a ∈ (ℤ/m)^×`: returns to the conjugates `ω^a` at precision `aδ` | — |
| Integer auxiliary | `A(s) = Σ_{n∈S} a_n n^{−s}`, `a_n ∈ ℤ`, `S` `P`-smooth: an element of `ℤ[Γ_P]` | `IntegerCoeffs`, `dpoly` |
| Degree, height | `deg A = log max S` (length `N`), height `‖a‖₁` | `EffectiveArithmeticHodgeTheory` |
| Order of vanishing | along a Frobenius progression `2πiℤ/log p` (divisibility by `1 − p^{−s}`), at a closed torsion point (Hasse derivatives of `F`), along the prime orbit at `s₀` (derivatives in `s`) | `VanishesAlong` |
| Factorial auxiliary | `Π_d ⌊x/d⌋!^{c_d}`, the `ℓ`-adic Frobenius auxiliaries (Legendre, Kummer) | — |

## 3. Language

- **Point count of degree `n`**: `Fix_B(n) = Σ_m Λ(m) m^{−½} K_B(log n − log m)` plus the archimedean
  index; **main term** `M_B(n)`: the pole (the `qⁿ` of a curve). **Arithmetic Stepanov bound**:
  `Fix_B(n²) ≤ M_B(n²) + K`.
- **Exact Frobenius**: an operator fixing a point set exactly, acting on auxiliaries as a ring
  endomorphism. **Approximate Frobenius**: the flow at a return time.
- **Inseparable at `ℓ`**: `ψ_ℓ(F) ≡ F^ℓ (mod ℓ)`.
- **Integrality amplifier**: a mechanism turning smallness of an integer auxiliary into exact
  vanishing (an integer of modulus `< 1` is `0`; a nonzero algebraic integer has norm `≥ 1`).
- **Precision cap**: a Rouché copy of a zero of order `J` at a `δ`-return within radius `r` forces
  `J ≤ e² r log N + log(1/δ)`.
- **Blind**: a count whose error term does not depend on the zeros of `ζ`.
- **Uniform order** at a torus point: vanishing of all partial derivatives of `F`; **orbit order**:
  vanishing of the `s`-derivatives of `A` along the prime orbit only.

## 4. Mechanisms

**Built on (corpus).**
1. Integer-degree Hasse–Weil: any constant `K` at every integer degree is RH; the lower bound at the
   squares suffices; the Stepanov side is blind exactly to real zeros (`SurfaceOfSpecZ`).
2. Infinite-rank elimination: thick-set crude bounds self-improve in well-founded towers
   (`InfiniteRankWeilTheory`).
3. Bézout and Riemann–Roch of `𝔾_m(ℚ)`: vanishing to order `m_p` along `p`'s progression forces
   `Π p^{m_p} ≤ N`, `h⁰(N, m) = ⌊N/Π p^{m_p}⌋`; small integer auxiliaries on a progression are
   divisible (`EffectiveArithmeticHodgeTheory`).
4. Freezing at returns, forced near-vanishing, the precision cap (`InfiniteRankWeilTheory`).
5. Stepanov over `𝔽_q` for hyperelliptic curves and character sums (`RHTower.Stepanov`,
   `ArithmeticKreinLangerTheory`); Baker's and Gelfond–Schneider's theorems (`RHTower`).

**Developed here.**
6. **Galois = Adams on torsion.** For `F ∈ ℤ[u^{±1}]` and `ω ∈ μ_m^P`, `σ_a(F(ω)) = F(ω^a)`. The fixed
   points of `ψ_q` are the `(q−1)`-torsion, on which `ψ_q F = F`: the identity `x^q = x` holds exactly,
   in characteristic zero, on the torsion of every prime torus.
7. **The prime orbit meets the torsion only at `t = 0`** (two primes), and returns to every torsion
   point; the dilates `a·t` of a return to `ω` are returns to `ω^a`.
8. **Norm amplifier.** `Π_a F(ω^a) = N_{ℚ(μ_m)/ℚ}(F(ω)) ∈ ℤ`; smallness of `A` along the Frobenius
   orbit of a torsion return forces exact vanishing of `F` on the closed point `[ω]`. The required
   precision is polynomial in the height and does not grow with the order: the amplifier beats the
   precision cap, off the prime orbit.
9. **`ℓ`-adic inseparability is blind.** Factorial auxiliaries satisfy Legendre's identity
   `log Π⌊x/d⌋!^{c_d} = Σ_m Λ(m) Σ_d c_d⌊x/(dm)⌋` and Stirling's formula: their prime counts equal a
   main term up to `O(log x)` whatever the zeros of `ζ` are.
10. **Integrality on the orbit stops at order two.** At the common fixed point `s = 0`, smallness of
    an integer auxiliary forces exact vanishing of `A` and `A'` (an integer; the logarithm of a
    rational); exactness of `A''` is a question about quadratic relations among `log p`.

## 5. Questions

| # | Question (§2.9) | Approach |
|---|---|---|
| Q1 | What is the degree-`n` Frobenius of `Spec ℤ` as a correspondence, and what are its fixed points? | `Γ_n` with fixed points the closed orbits of length `log n`; its exact form is the Galois–Adams Frobenius on torsion; the prime orbit carries only the dilation `s ↦ as` with the single fixed point `0` |
| Q2 | What is the Lefschetz identity for `Γ_1·Γ_n` with its main term? | fixed-point form `c_B(log n) = M_B(n) − Fix_B(n)`; the arithmetic Stepanov bound in point-count form at square degrees |
| Q3 | Which auxiliary integer Dirichlet polynomials vanish at all fixed points, to what order, of what degree? | cyclotomic Riemann–Roch: vanishing at all closed torsion points of the prime circles is divisibility by `Π Φ_m(p^{−s})^{J}`; degree `Σ φ(m) J log p`; uniform order at a torus point `≤ deg/log 2` |
| Q4 | When does integrality force a `δ`-small auxiliary to vanish exactly at a return of the prime orbit? | at torsion returns on the torus (norm amplifier); on the orbit itself: at progression points of one prime, and at `s = 0` through order two; never at a generic return |

## 6. Tools

| # | Tool (§2.9) | Form |
|---|---|---|
| T1 | Siegel lemmas for Dirichlet polynomials on smooth numbers | integer auxiliaries on `P`-smooth `n ≤ N` vanishing to prescribed uniform order at prescribed closed torsion points, with explicit height |
| T2 | zero estimates in many logarithms, uniform in their number | zero counts of integer Dirichlet polynomials in discs with constants independent of `\|P\|`; integrality supplies the centre value |
| T3 | integrality amplifier | the norm amplifier at torsion returns; divisibility on progressions |
| T4 | Lefschetz fixed-point form of Frobenius-graph intersections | `Γ_1·Γ_n` as a sum of local indices at fixed points with main term |
| T5 | Stepanov counting `#fixed·J ≤ deg A` | cyclotomic Bézout: `Σ_{p,m} φ(m) J_{p,m} log p ≤ deg A` |

## 7. Criteria (§2.9)

1. Reproduce Stepanov–Bombieri over `𝔽_q` as the finite-rank case.
2. Give the crude bound with a constant at every integer degree, or on the squares.
3. Use the Euler product and the functional equation (fail on one-offs, `cosh` models, the heat
   family).
4. Beat the precision cap by exact vanishing, not by approximation.

Criterion 2 is RH. A mechanism of ALST meets criterion 3 only if it distinguishes `ζ` from the
integer-norm one-off; every mechanism of §4 is tested against that model.

## 8. Traps

| Trap | Truth |
|---|---|
| Returns are fixed points of a Frobenius | at a return the flow is close to the identity on the whole torus: there is no point set, only freezing |
| Integrality turns forced near-vanishing at returns into zeros | exact vanishing of an integer auxiliary at a generic point of the orbit is impossible; integrality acts at torsion points of the torus and on progressions of single primes |
| High order at a point is cheap with integer coefficients | the uniform order of a length-`N` auxiliary at a torus point is at most `log N/log 2`; orbit order beyond two needs relations among `log p` |
| `ℓ`-adic Frobenius congruences give a Stepanov count | they give factorial auxiliaries, whose counts are blind to the zeros |
| Vanishing at all fixed points can be cheap over `ℤ[Γ]` | Riemann–Roch of `𝔾_m(ℚ)` is exact; cheapness needs an identity that `ℤ[Γ]` does not supply |

## 9. Context

| Programme | Interface |
|---|---|
| SurfaceOfSpecZ | integer-degree Hasse–Weil, point count, Stepanov side at squares, smoothed kernels |
| InfiniteRankWeilTheory | self-improvement on thick sets, returns, forced vanishing, precision cap |
| EffectiveArithmeticHodgeTheory | Bézout and Riemann–Roch of `𝔾_m(ℚ)`, divisibility of small integer auxiliaries |
| ArithmeticCastelnuovoSeveri | scaling surface, Hecke and Adams operations, curve data, fake curves |
| PrimeTorusTheory, TailArithmeticOfThePrimeOrbit | non-alignment, torsion avoidance, returns, precision law |
| RHTower | Stepanov over `𝔽_q`, Baker, Gelfond–Schneider, zero estimates |
| CountingHolography | count laws on curves; the count door over `ℤ` |

## 10. Success criteria and contributions

ALST succeeds when Q1–Q4 have theorem-level answers, T1–T5 exist in their strongest unconditional
form, each criterion of §7 is met or shown impossible for a named mechanism with its strongest
positive survivor, and RH is reduced to one precise Stepanov statement whose strength is fixed by a
theorem.

A **contribution** must be unconditional; say which of (S1), (S2), (S3) it realizes over `ℤ` and at
which place; state whether it holds for the integer-norm one-off; and say whether its vanishing is
exact or approximate and at which points (orbit, torus, progression).
