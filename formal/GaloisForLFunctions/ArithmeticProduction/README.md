# Arithmetic Production at Square-Root Precision (APR)

Namespace `GaloisForLFunctions.ArithmeticProduction`; umbrella `ArithmeticProduction.lean`.

## 1. Motivation

Every route to RH reduces to one inequality, the count `ψ(x) − x = O(√x log²x)`, read in some coordinate. A receiver
states what must be delivered; a producer delivers an inequality. The corpus has many receivers and no producer: PNT,
Guth–Maynard and every error law weaker than square root hold for weights that fail the count, finite windows are
blind to every width, and exact identities determine `Λ` without giving an inequality. APR is the theory of production:
which unconditional statements about `Λ` and `ζ` inside the strip can carry parity and square-root precision, what each
classical tool can and provably cannot produce, and where the precision is lost between `ζ` and `Λ`.

## 2. Objects

| Object | Meaning |
|---|---|
| Weight, count | `a : ℕ → ℝ`; `A(x) − x = O(√x log²x)` (ASRP) |
| Square-root class `𝒬`, stabilizer | perturbations with partial sums `O(√x log²x)`; perturbations a statement survives |
| Liouville twin, power perturbation, impure Euler factor | `λa`; `a + εn^{−η}`; `ζ(s)(1 − c p^{−s})`, `c > √p` |
| Bilinear form | `B_a(α, β) = Σ α_m β_n a(mn)` on a box; its norm |
| Type I datum | `Σ_{n ≤ x, d | n} a(n)` for `d ≤ D` |
| Mollifier of length `y` | `M(s) = Σ_{n ≤ y} b_n n^{−s}`, `b₁ = 1`, `|b_n| ≤ 1`; linear Möbius `b_n = μ(n)(1 − log n/log y)` |
| Length exponent | `θ = log y / log T` |
| Mollifier defect | `(2π)⁻¹∫|1 − ζM(½+it)|² dt/(¼+t²)` and its windowed forms |
| Sawtooth form | `∫₀^∞|1_{x≥1} + Σ_d b_d {x/d}|² dx/x²` |
| Cramér integral | `∫₁^X (ψ(x) − x)² dx/x²` |
| Selberg integral | mean square of primes in short intervals `(x, x e^{1/T}]` |
| Spectral measure of a second moment | `∫|F(½+x+it)|² dt = 2π∫ e^{−2xu}|Y(u)|² du` |
| Critical-scale clustering, `D_win`, `D_zero`, Planck shadows, giant clusters | CDG |
| Strip width `Θ`, shifted products | `sup Re ρ`; `ζ(s+ε/2)ζ(s−ε/2)` |

## 3. Language

- **Producer**: an unconditional statement that is not an identity, with a named consequence for the zeros.
- **Parity-blind**: unchanged by the Liouville twist. **Phase-blind**: depends on `|a_n|` only.
- **Precision-blind at `η`**: shared by `a` and `a + εn^{−η}`.
- **Locally pure**: distinguishes `Λ` from an impure factor at every single prime.
- **Band-limited**: spectral measure essentially supported in `[0, log(Ty)]`.
- **Length–precision**: the exponents `η` a statement at length `θ` resolves.
- **Floor**: a lower bound on a mollified moment, valid for every mollifier in a class.

## 4. Mechanisms

**A. Exclusion.** Bilinear norms are conjugated, not changed, by a completely multiplicative unimodular twist, so they are
parity-blind at infinite precision. On prime-supported weights the form is block-diagonal over prime towers, so it does
not see where the primes are. Type I data of the twin are `λ(d)L(x/d)`, so level-`D` divisor sums stay at `L¹`-distance
`≈ x` from `Λ` until `D ≈ x`. Mean values of length below the window depend on `|a_n|` only. Upper bounds for `ζ` survive an
impure Euler factor, which breaks the count, D_win and the log-mean.

**B. Dictionary.** For the linear Möbius mollifier the coefficients of `ζM` are `1 + Λ(n)/log y` on `n ≤ y`, so the mollifier
defect is the Chebyshev error: on `1 ≤ x ≤ y` the sawtooth function equals `xM(1) − ψ(x)/log y`. The global mollified second
moment contains the Cramér integral over `log²y`. For the sharp Möbius mollifier the same function is `x m(y)`, so the defect contains
`(y − 1) m(y)²`. Beyond the window length the windowed prime polynomial is a Selberg integral.

**C. Floors.** A zero of `ζ` is a fixed zero of every mollified product, so each off-line zero pins a floor for every length.
The left-line floor `E log|ζM(½ − a + it)| ≥ a log T` comes from the zero count; second moments on vertical lines are Laplace transforms of a
spectral measure carried by `[0, log(Ty)]`. Together these force a value above `1` on the line itself.

**D. Self-improvement.** Shifted products have Euler products, functional equations and every width in `(½, 1)`.

## 5. Pillar theorems (to be established)

| Theorem | Statement |
|---|---|
| Necessary length | `T⁻¹∫_T^{2T}|ζM(½+it)|²dt ≥ 1 + c/(1+θ) − o(1)` for every real mollifier of length `T^θ` |
| Linear mollifier is the Chebyshev error | exact identity on `[1, y]`; Cramér integral inside the defect |
| Mollifier floor | `defect ≥ (2β−1)|1−ρ|²/|ρ|⁴` for every Dirichlet polynomial; Blaschke form |
| Bilinear parity barrier | `‖B_{ga}‖ = ‖B_a‖`; no statement through bilinear norms implies the count |
| Type I parity barrier | `Σ_{n≤x}|Λ − W| ≥ ψ(x) − 2ψ(√x) − Σ_d|c_d||L(x/d)|` |
| Length–precision law | a length-`θ` variance law resolves exactly `η < ½ − 1/(2θ)` |
| Impure factors | exact integer count, all upper bounds, failed count, D_win, positive log-mean |
| Shifted products | width formula; class-wide self-improvement `⇔ Θ = 1` |
| Long mollifier ⇒ clustering | named implication into the eight forms of B20 |

## 6. Tools

**In the corpus.** Dirichlet mean-value theorems, Montgomery–Vaughan, large sieve (`RHTower.Sieve`, `MontgomeryVaughan`); Vaughan
decompositions (`BezoutValuationIncidence`, `RHTower.Sieve`); Selberg near-line density and Littlewood for `ζΨ` (`RHTower`); Levinson
detector; clustering TFAE, Planck shadows, giant clusters (CDG); fractional-part Gram form and Báez-Duarte carrier (`RHTower`);
Cramér law and band rates (`BiScaleUncertainty`); precision classes, Nair integrals (ASRP).

**To develop here.** Sawtooth form with target; spectral calculus for second moments with contour-shift tail bounds; floors for
windowed mollified moments; bilinear and Type I barriers; Selberg-integral dictionary.

## 7. Questions

1. **`100%` critical-scale clustering (B20).** What does the mollifier route need exactly, and what can it not reach at bounded length?
2. **`D_win`, `D_zero` (B21).** Which inputs are excluded, and what must a proof see?
3. **Mollified second moment at length `T^θ`, `θ → ∞`.** Is the length necessary? What is the statement in terms of primes? How does it relate to RH?
4. **Self-improvement (B57).** On which class is it false, and which hypotheses must a proof use?
5. **A parity-breaking bilinear input at square-root precision.** What shape must it have?

## 8. Traps

| Trap | Fact |
|---|---|
| Uniform bilinear bounds can break parity | they are invariant under the twist |
| A longer sieve level breaks parity | not before `D ≈ x` |
| Mean values of long primes see the count | below the window length they depend on `|a_n|` only |
| Upper bounds for `ζ` constrain the zeros | they survive an impure Euler factor |
| Second moment `→ 1` at fixed length | excluded by the zero count and band limiting |
| A long Dirichlet polynomial on a finite window has a floor | only with bounded coefficients; a finite window admits arbitrary approximation otherwise |
| The eight forms of B20 are one statement | equivalent for `ζ`, separated on impure mimics |

## 9. Context

Consumes ASRP (entry test, classes), CDG (near-line ladder), RHTower (`Sieve`, Selberg, Levinson, Báez-Duarte), BiScaleUncertainty (Cramér). Produces the input
side of §2.7.2 for Programme A (`FrustratedArithmeticDirichletForms`, `SignedWindowCriticality`, `RHTower` cone theory), which treats weights as free; APR works on `Λ` itself.

## 10. Success criteria and contributions

Developed when each question of §7 has a Lean-backed answer: a theorem, a no-go with its positive survivor, or a precise reduction, and when each
classical tool has its production limit proved. A contribution must be an unconditional theorem that (a) excludes a class of inputs with a named mimic, or (b) gives an exact dictionary between a
`ζ` statement and a `Λ` statement, or (c) gives a floor or a threshold. Restatements of RH do not count.
