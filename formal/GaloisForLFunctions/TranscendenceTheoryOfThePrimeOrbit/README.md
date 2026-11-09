# Transcendence Theory of the Prime Orbit (TTPO)

Namespace `GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit`; umbrella
`TranscendenceTheoryOfThePrimeOrbit.lean`. Specification: §2.11 of
[the review-0811 obstacles summary](../../../docs/reports/review-0811/obstacles-summary.md).

Throughout, `ω_t = (p^{−it})_p` is the point of the prime orbit at height `t`, `P` a finite set of
primes, `ν ∈ ℤ^P` an integer vector, `Λ_ν = Σ_p ν_p log p` its linear form in logarithms,
`|ν|₁ = Σ|ν_p|` its height, and `‖x‖` the distance of a real number to `ℤ`.

## 1. Motivation

The sign-free part of the curve proof over `ℤ` is in the corpus: elimination at the exceptional rank on
thick sets (Vandermonde), free self-improvement at the integer degrees, and the finite-rank Euler–FE
purity theorem. What it lacks is a **producer** for the crude step. The three sign-free producers that
exist are capped: integrality reaches Chebyshev, phase-freezing Rouché copies reach the trivial
separation bound, exponential sums reach Vinogradov–Korobov. The crude step fails exactly where the
prime orbit returns: at an early heavy return a long prime polynomial is large and a zero can hide
under it (proportional saving ⇔ no early heavy return). Over `𝔽_q` there is one Frobenius and no
return to fear.

A return is a simultaneous approximation: `t` is a `δ`-return of `P` when `‖t log p/2π‖ ≤ δ` for every
`p ∈ P`. Lower bounds for return times are Diophantine statements about the numbers `log p`, and
transcendence theory is the sign-free discipline that proves such statements: auxiliary functions with
integer coefficients, extrapolation, zero estimates, linear forms in logarithms. Integrality
(`|n| ≥ 1` for a nonzero integer, `|N(α)| ≥ 1` for a nonzero algebraic integer) is the one sign-free
mechanism that turns approximate vanishing into exact vanishing, which the precision cap says Rouché
cannot do.

TTPO is the theory of the prime orbit as a Diophantine object. Its target is the **quantitative
Kronecker theorem for the primes** (B97): at fixed precision `δ ∈ (0,1)` the first `δ`-return of the
primes up to `y`, and of every heavy subset, comes after `exp(y^c)`. Unconditionally the first return
lies between `exp(c(log y)^{3/2}/log log y)` (Vinogradov–Korobov on the `1`-line, at precision
`≍ 1/log log y`) and `exp(π(y) log(1/δ))` (Dirichlet); under RH it is at least `exp(c√(y/log y))`.

A return has two parameters, and they belong to different mathematics:

- its **depth** `δ`, at a fixed set of primes;
- its **breadth** `|P|`, at a fixed depth.

Linear forms in logarithms control depth: a return of two primes at depth `δ` makes one binary form
`|n_p log q − n_q log p|` of size `≤ δ log pq` with coefficients `≍ t`, and Baker bounds that form from
below by a power of `t`. The main conjecture is a breadth statement at constant depth. TTPO makes this
distinction exact, prices each transcendence tool on both axes, and asks which mechanism converts
breadth into depth or depth into breadth.

## 2. Objects

| Object | Meaning |
|---|---|
| Prime orbit | `t ↦ ω_t = (p^{−it})_p` on the infinite torus; a one-parameter subgroup, dense by the independence of the `log p` |
| Return, first return | `δ`-return of `P` at `t`: `‖t log p/2π‖ ≤ δ` for `p ∈ P`; `R(P, δ)` the least `t ≥ 1` of one (TAPO's `IsReturn`, `firstReturn` in the cosine normalization) |
| Heavy subset | `H ⊆ P` carrying all but `κ` of the weight `Σ p^{−½}`; a heavy return is a return of a heavy subset |
| Linear form, height | `Λ_ν = Σ ν_p log p = log(a/b)` for coprime `P`-smooth `a, b`; `|ν|₁`, `|ν|_∞` |
| Window of a form | the heights `t` at which `‖tΛ_ν/2π‖` exceeds `|ν|₁δ`; no `δ`-return lies in a window |
| Rounded system | steps `ℓ_p = 2π·round(T log p/2π)/T`: an exact return at `T` |
| Integer auxiliary | `A(s) = F((p^{−s})_{p∈P})`, `F ∈ ℤ[u_p]`: a Dirichlet polynomial with integer coefficients on `P`-smooth numbers |
| Jet at a return | `A^{(j)}(it)` against `A^{(j)}(0) = (−1)^j Σ c_n (log n)^j`, an integer form of degree `j` in the `log p` |
| Power sums, level sums | `Σ_j b_j z_j^ν`; for zeros, `z_ρ = b^{ρ−½}` on the levels `ν` of a base `b` |
| Finite-rank remainder | `ψ(x) − x` minus a finite exponential sum `Σ c_j x^{ρ_j}`; `Θ∞` is its infimum exponent |
| Reciprocity | the FE as a reflection of lengths and heights: approximate functional equation, Estermann and theta reflection |

## 3. Language

- **Depth** of a return: its precision `δ`. **Breadth**: the number of primes returning together.
- **Diophantine certificate of height `K`**: an argument excluding returns that uses only lower bounds for
  `|Λ_ν|`, `|ν|₁ ≤ K`.
- **Window method**: excluding returns by forms whose windows cover a range of heights.
- **Survival**: an approximate vanishing condition at a return that integrality forces to hold exactly.
- **Turán loss**: the factor `(c/N)^N` by which Turán's second main theorem bounds an `N`-term power sum
  below at some level of a window of length `N`.
- **Well-founded radius**: the radius above which a tower of modes is finite above every larger radius.
- **Reciprocity**: an identity exchanging a sum of length `N` at height `t` with one of length `t/2πN`.

## 4. Mechanisms

**Built on (corpus).**
1. Proportional saving ⇔ no early heavy return; the first return is an extreme value of
   `ζ(1 + 1/log N + it)`; the precision law (TailArithmeticOfThePrimeOrbit).
2. Vinogradov–Korobov on the `1`-line caps the spike: `R ≥ exp(c(log N)^{3/2}/log log N)` at bounded
   harmonic defect (TailArithmeticOfThePrimeOrbit).
3. Effective Baker for any finite family of primes, Fel'dman's method
   (`RHTower.Matveev.effectiveBakerBound_holds`); two primes: `log 2`, `log 3` polynomially separated
   (`SumProductArithmeticOfTheLogarithm`); Baker and Gelfond–Schneider qualitatively; six exponentials:
   `p^ρ, q^ρ, r^ρ` are not all algebraic for nonreal `ρ` (`RHTower.SixExponentials`).
4. Integrality on the torus: the norm amplifier at closed torsion points, Galois = Adams, Stepanov's
   construction on the torsion, exact vanishing on the orbit only at countably many heights
   (ArithmeticLefschetzStepanovTheory).
5. Freezing at returns and the precision cap `J ≤ e²r log N + log(1/δ)`; well-founded elimination on thick
   sets; Wolff towers (InfiniteRankWeilTheory).
6. Turán's second main theorem without separation, weighted (HTGeometry).
7. `Θ∞` is the finite-rank Chebyshev exponent (ZeroConfigurationGeometry); RH ⇔ ZAL ∧ AAL.

**To establish.**
8. **Return–form duality.** At a `δ`-return, `‖tΛ_ν/2π‖ ≤ |ν|₁δ`; a form excludes returns on its window.
9. **Depth law.** Baker turns every return of two primes into a binary form with coefficients `≍ t`, so
   `R(P, δ) ≥ c δ^{−a}` with explicit `c, a` depending on `|P|` and `Σ_{p∈P} log p` only.
10. **Breadth cap.** At precision `δ` only forms of height `< 1/2δ` act; Liouville is sharp for them up to
    polylogarithmic factors, and the rounded system matches all of them while returning exactly at any
    `T ≥ 2πK y^K`. No lower bound for linear forms certifies a constant-precision return past `y^{O(1/δ)}`.
11. **Survival at a deep return.** The jets of an integer auxiliary at a return equal its jets at `0` up
    to `δ` times a logarithmic mass; order one survives below an explicit Baker threshold.
12. **Reciprocity of lengths.** The approximate functional equation reflects a return of the integers past
    the self-dual length into a value of `ζ` on the critical line.

## 5. Questions

| # | Question (§2.11) | What an answer must contain |
|---|---|---|
| Q1 | How early can the primes `≤ y` return to `δ`-precision, and how early can a heavy subset? | lower and upper brackets for `R(y, δ)` and for heavy subsets, on both axes (fixed `P`, `δ → 0`; fixed `δ`, `y → ∞`), with the method that reaches each bracket and the theorem that caps it |
| Q2 | How does the lower bound for linear forms in `k` logarithms depend on `k`, and can it be taken uniform for `k ≍ π(y)`? | an explicit exponent `C(k, W)`, a necessary lower bound for any exponent, and the consequence of uniformity at `k ≍ π(y)` for returns |
| Q3 | Which auxiliary integer polynomials on smooth numbers survive the passage from approximate to exact vanishing? | the orders, points and precisions at which smallness forces exact vanishing, and the obstruction beyond them |
| Q4 | How does Turán's power-sum method give ZAL on the finite-rank remainder of `ψ`? | what Turán decides on the remainder, what it cannot decide, and the exact input it would need |

## 6. Tools

| # | Tool (§2.11) | Target form |
|---|---|---|
| T1 | Linear forms in many logarithms with explicit dependence on their number | `|Λ_ν| ≥ exp(−C(k, W)(log |ν|_∞ + 2))` with `C` explicit in `k` and `W ≥ Σ log p`; its necessary growth in `k` |
| T2 | Schneider–Lang extrapolation along the prime orbit | transport of smallness of integer auxiliaries from one return to its multiples and sums; algebraic points of the orbit |
| T3 | Turán's second main theorem on thick sets of levels | power-sum lower bounds on every window of a thick set, the loss, and its role for the finite-rank part of `ψ` |
| T4 | Poisson, theta, Farey and Dedekind reciprocity as sign-free forms of the FE acting on heights | exact reflection identities for sums along the orbit, and what they transport |

## 7. Criteria and milestones

| Item (§2.11) | Content |
|---|---|
| C1 | never use a sign, a spectral decomposition or a positivity |
| C2 | reproduce Stepanov over `𝔽_q` (no returns to fear) as the degenerate case |
| C3 | pass the two-prime case (continued fractions) and the fixed-`k` case (Baker–Wüstholz) |
| C4 | supply a producer for the crude step beyond the precision cap, Chebyshev (integrality) and VK (exponential sums) |
| M1 | two primes |
| M2 | linear forms in `k ≍ (log y)^A` logarithms with explicit `k`-dependence |
| M3 | `log R(y, δ) ≥ (log y)²` (past VK) |
| M4 | `log R(y, δ) ≥ y^c` |
| M5 | sign-free ZAL |

## 8. Foundational theorems

1. Return–form duality and the window method.
2. Explicit linear forms in `k` logarithms; the pigeonhole lower bound `C(k) ≥ k − 1`.
3. The depth law of returns of a fixed set of primes, uniform over the subsets of the primes `≤ y`.
4. The breadth cap: no Diophantine certificate of bounded height reaches past `y^{O(1/δ)}`.
5. Survival of order one at deep returns; the obstruction at order two.
6. The Turán window theorem for the finite-rank part of `ψ` and the obstruction on the remainder.
7. Reciprocity of lengths along the integer orbit.

## 9. Traps

| Trap | Truth |
|---|---|
| Baker's theorem bounds return times | it bounds the depth of returns of a fixed set; at constant precision only forms of bounded height act, and for them Liouville is already sharp |
| A uniform Baker bound for `k ≍ π(y)` would give B97 | at constant precision the relevant forms have bounded height; the rounded system satisfies every bounded-height bound and returns early |
| Returns are rare because the `log p` are independent | independence gives density zero of exact returns, not a rate; the rate is a counting statement |
| Integrality makes small values at returns vanish | exact vanishing on the orbit happens at countably many heights; integrality is a repulsion there |
| Turán's method proves upper bounds | it proves lower bounds at some level of every window; ZAL is an upper bound on the remainder |
| A return bound is a statement about `ζ` | it is a statement about the prime labels; every Euler product over the rational primes shares it |
| The FE moves zeros to new heights | each reflection preserves the height; transport is the open problem of Euler–FE transport theory |

## 10. Open research topics

1. A breadth mechanism: an argument excluding returns that uses the number of small forms, not their size.
2. Depth-to-breadth conversion: from deep returns of few primes to moderate returns of many.
3. Survival at order two: lower bounds for integer quadratic forms in `log p`, `p ∈ P`.
4. Return bounds for heavy subsets that avoid the small primes, where the spike of `ζ(1 + it)` is blind.
5. Reciprocity for prime sums: a reflection of the prime orbit not passing through the zeros.
6. ZAL from power sums with an arithmetic input that excludes Wolff conspiracies.

## 11. Context

| Programme | Interface |
|---|---|
| TailArithmeticOfThePrimeOrbit | first return, precision law, proportional saving ⇔ heavy first return, VK bracket |
| PrimeTorusTheory | orbit at finite time, rounded orbit, savings against size, Kronecker scale |
| ArithmeticLefschetzStepanovTheory | integrality amplifier on the torsion, Stepanov's construction, exact order costs the degree |
| InfiniteRankWeilTheory | freezing, precision cap, well-founded elimination, Wolff towers, thick sets |
| EulerFETransportTheory | the FE as height reflection; transport (B112) |
| RHTower (Matveev, BakerProof, SixExponentials) | effective and qualitative transcendence of the `log p` |
| HTGeometry | Turán power sums, Kronecker density, simultaneous Dirichlet |
| SumProductArithmeticOfTheLogarithm | two-prime separation, logarithmic collisions |

## 12. Success criteria and contributions

TTPO succeeds when Q1–Q4 have theorem-level answers, T1–T4 exist in their strongest unconditional form,
each criterion C1–C4 is met or shown unattainable for a named mechanism with its strongest positive
survivor, and the main conjecture is reduced to statements whose strength is fixed by theorems.

A **contribution** must be unconditional; state its depth and breadth; say whether it uses lower bounds
for linear forms (and of which height), integrality (at which points), or counting; say whether it holds
for every Euler product over the rational primes or uses the coefficients and the FE of `ζ`; and be
false on the rounded system if it claims a return bound past the Kronecker scale.

## 13. Big picture

A return of the prime orbit is a simultaneous approximation to `2πℤ`. Transcendence theory measures
how good one approximation can be; the main conjecture asks how many mediocre approximations can occur
together. TTPO separates these two axes, proves what each tool gives on each, and isolates the
statement that a proof of B97 must supply: a counting law for the forms of bounded height, which is a
statement about exponential sums over the primes, not about the size of a single linear form.
