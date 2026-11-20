# Theory of Arithmetic Producers (TAP)

Namespace `GaloisForLFunctions.ArithmeticProducerTheory`; umbrella `ArithmeticProducerTheory.lean`.
Specification: §2.9 of the [review-2011 obstacles summary](../../../docs/reports/review-2011/obstacles-summary.md).
Every theorem of the programme is unconditional; RH and zero-free strips appear only inside
implications and equivalences.

> First draft. Sections 5–7 list the pillar theorems as targets; the status column records what is
> proved in Lean.

## 1. Motivation

The corpus has turned almost every route to RH into an exact statement about `Θ`, the supremum of
the real parts of the zeros of `ζ`. A quantity that reads `Θ` exactly is a **meter**. A meter has no
slack: a bound for it is as hard as the statement it reads. What a proof needs is a **producer**: a
construction built from integers and primes, without reference to zeros, together with a comparison of
two sizes of that construction which forces a one-sided bound for a signed remainder, at an exponent
that a proved one-sided ⇒ strip implication converts into a zero-free region.

Producers exist in two places only:

| Where | Producer | Comparison | Output |
|---|---|---|---|
| Classical analysis | zero-free regions, convexity, mean values | Hadamard, Jensen, Phragmén–Lindelöf | stops at a strip |
| Curves over `𝔽_q` | Stepanov–Bombieri | degree of an auxiliary ≥ multiplicity × number of fixed points | `N ≤ q + O(g√q)` |
| Curves over `𝔽_q` | Weil | Castelnuovo positivity of an intersection pairing | `|a_n| ≤ 2g q^{n/2}` |
| CM curves over `𝔽_q` | Jacobi | conjugation pairing = polarization pairing (an identity in `ℤ[ζ_m]`) | `|J| = √q` |

Over `ℤ` the integer analogues of the comparisons are known and all of them are exact or lossy:
Chebyshev's size-versus-divisibility comparison loses a constant factor, Nair's integrality floor
reads `ψ` from below with a constant, the Selberg quadratic identity reaches the prime number theorem
but no power saving, and Stepanov's auxiliary on the prime torus has degree `ψ(N)` exactly. TAP is the
theory of these comparisons over `ℤ`: which exist, what they cost, at which place the cost is paid,
and which twins they separate. Its aim is a producer that meets the four criteria of §11, or the proof
that a named class of constructions cannot contain one, together with the strongest positive survivor.

## 2. Objects

| Object | Meaning | Lean (corpus or TAP) |
|---|---|---|
| Signed remainder | `E(x) = θ(x) − x`, `ψ(x) − x`, the Mertens function `M(x)` | `Chebyshev.theta`, `Chebyshev.psi` |
| Halving increment | `E(H) − E(H/2)`: the terminal odd-quotient half | ECS `terminalOddHalf`, `terminal_odd_half_eq` |
| Prime midpoint price | `D(n) = 2θ(3n) − θ(2n) − θ(4n)` | ELT `primeMidpointPrice` |
| Stepanov degree | `log lcm(1,…,N) = ψ(N)`, the log length of the fixed-point auxiliary | ALST `log_length_fixedPointAux_eq_sum_lefschetz` |
| Construction | an integer, an integer polynomial, an integer Dirichlet polynomial on the prime torus, a section of a conductor bundle | — |
| Reading | the arithmetic size of a construction (valuations weighted by `log p`, vanishing orders weighted by degree); by unique factorization a linear functional of `Λ` | — |
| Price | a second size computed by a different mechanism (closed form, integral, dimension count) | — |
| Slack | price − reading | — |
| Stencil | a balanced integer combination `c` with the factorial ratio `∏ ⌊n/k⌋!^{c(k)}` | AAD `IsProducer` |
| Twin | an object sharing a named list of properties with `ζ` and violating the target bound | see §2.1 |
| Transfer kernel | a positive operator moving a one-sided bound from one remainder to another | ECS, ELT Green kernel |

### 2.1 The twin suite

| Twin | Shares with `ζ` | Violates | Lean |
|---|---|---|---|
| Integer-norm one-off | Euler product over integer norms, pole at `1`, continuation to `Re s > ½` | prime error `≍ x^{3/5}`; the Stepanov degree bound | APD `integer_norm_one_off_with_prime_oscillation`; ALST `one_off_violates_stepanov_bound` |
| Real one-off | same, with a real zero `3/5` | the lower side only | ALST `real_one_off_satisfies_stepanov_bound` |
| Liouville twin `λΛ` | contact sizes `|λΛ| = Λ`, every error law after the pole correction | comb positivity at macroscopic cost | SAC `eventually_exists_liouville_centeredMultiple_neg`; APR `count_poleCorrectedTwin_iff` |
| Prime-2 Schur twin | causality, Euler product, functional equation, passivity, unitarity | the quarter ringdown law | BHR `CausalIdentitiesCannotForceQuarterRingdown` |
| Euler-symmetric finite layers | Euler divisor, functional-equation symmetry | AAL at depth `b` | FFA `eulerDivisor_layerConfig` |
| Tempered configurations at fixed aperture | every fixed-aperture positivity | the zero width | SRT `TheZeroWidthIsAnUnboundedApertureProperty` |
| Golden datum | integral zeta function, functional equation, positive counts | purity | ACS `goldenDatum_beurling_not_pure` |

## 3. Language

- **Producer.** A construction `C(N)`, a reading `ρ(C)`, a price `π(C)` with `ρ ≤ π`, and the one-sided
  bound for a remainder that follows. **Output exponent** `b`: the bound is `≤ K N^b`.
- **Meter.** A remainder whose growth exponent is an exact function of `Θ`. A producer whose output is a
  meter at exponent `b` proves `Θ ≤ b` through its **landing** (a proved one-sided ⇒ strip theorem).
- **Zero-blind price.** A price computed in closed form (Stirling, binomial theorem, an integral) whose
  Dirichlet generating function has no pole at a zero of `ζ`.
- **Transfer.** A producer whose price is zero-blind turns an upper bound on a target into a lower bound
  on the complement; it moves the problem and produces nothing.
- **Free multiplicity.** Vanishing order obtained at a cost below the order times the cost of a simple
  zero. Over `𝔽_q` it comes from inseparability; over `ℤ` it is the open question Q1.
- **Selective.** An argument is selective for a twin if one of its steps is false for the twin.
- **Circular.** A price is circular if it is computed from `ψ` (or from `M`, or from the zeros).
- **Axiom level.** The list of properties of `ζ` an argument uses; its twin is the strongest twin at that
  level, and its output exponent is at most the twin's.
- **Inseparability ledger.** The record, place by place, of the size of the derivative of a Frobenius:
  over `ℚ` the degree-`n` Frobenius has derivative `n`, and `∏_v |n|_v = 1`.

## 4. Mechanisms

1. **Reading by unique factorization.** `log A = Σ_{d | A} Λ(d)` for every positive integer `A`; for a
   factorial ratio the reading is `Σ_n Λ(n) g(⌊N/n⌋)` with the stencil weight `g`. Every divisibility
   producer is linear in `Λ`.
2. **Zero-blindness of closed-form prices.** For a stencil `c` the price `Σ_k c(k) log⌊N/k⌋!` has
   generating function `−ζ′(s) D_c(s)`: the zeros of `ζ` cancel. The output on a target window equals the
   price minus the complementary reading, which carries the zeros with the opposite sign.
3. **Multiplicity is linear over `ℤ`.** Raising a divisibility producer to the `m`-th power multiplies
   price and reading by `m` (AGT `ghost_ledger`); exact order `J` at a point of the prime torus costs
   length `2^J` (ALST). Over `𝔽_q`, `d(g^q) = 0` makes the conditions for order `m` the conditions for
   order one on lower-degree data.
4. **Product-formula ledger.** A Frobenius over `ℤ` is contracting exactly at the primes dividing its
   degree and expanding at the real place by the same total amount. What `ℓ`-adic inseparability gains
   (ALST, the amplifier threshold `ℓ^{φ(m)}`) is paid at `∞`.
5. **Selection by axiom level.** A step valid for a twin cannot produce a bound the twin violates. The
   twin suite fixes, for each list of properties, the best exponent any argument at that level can
   output.
6. **Landing.** One-sided bounds at exponent `b` on the halving increment, on `E`, on `D`, or on the
   Stepanov degree give `Θ ≤ b` (ECS `terminal_odd_half_width_iff`, ELT
   `prime_error_from_integer_midpoint`, ALST `riemannHypothesis_iff_log_length_fixedPointAux_le`).
7. **Positive Neumann transfer.** A dilation stencil `T = c(I − K)` with `K` a positive combination of
   dilations of spectral radius `< 1` on `x^b` inverts by a positive Green kernel, so one-sided bounds on
   `T E` pass to `E` at the same exponent (halving: `K = V_{1/2}`; midpoint: the ternary gain).
8. **Two pairings.** On Kummer and Fermat curves purity is the identity
   `conj J(χ, φ) = J(χ⁻¹, φ⁻¹)` together with `J(χ, φ) J(χ⁻¹, φ⁻¹) = q` (TPP `norm_jacobiSum_sq`): the
   archimedean place of `ℚ(ζ_m)` enters through complex conjugation, and no positivity is used. For the
   zeros of `ζ` the same identity, `ρ̄ = 1 − ρ`, is RH.

## 5. Questions

The four questions of §2.9, and four that the programme adds.

| # | Question |
|---|---|
| Q1 | What replaces inseparability at the real place? |
| Q2 | What is the arithmetic analogue of a divisor of bounded degree on `Spec ℤ × Spec ℤ`, with a Riemann–Roch count whose constants include the `Γ` factor? |
| Q3 | Which comparisons of sizes survive the product formula, which charges vanishing order at every place? |
| Q4 | Is there a positivity-free proof of the curve case in which the archimedean place of a number field appears? |
| Q5 | **Exactness.** Is every producer with a zero-blind price a transfer? Which producer classes have sublinear slack at all? |
| Q6 | **Axiom ladder.** For each axiom level (integer norms; integer count to precision `x^θ`; functional equation; coefficients `1`), what is the best output exponent, and which twin attains it? |
| Q7 | **Nonlinear producers.** The Selberg identity is a quadratic reading with a zero-blind price and reaches the prime number theorem. What is the axiom level and the reach of quadratic producers? |
| Q8 | **Transfers.** Which one-sided transfers between the meters (halving increment, `E`, `D`, Stepanov degree, `M`) hold at the same exponent with explicit constants, and which directions are impossible? |

## 6. Tools

| Tool | Content | Status |
|---|---|---|
| T1 Auxiliary sections with explicit heights | Siegel's lemma on smooth numbers and on conductor sections; counts with exact archimedean constants | corpus: ALST `exists_siegel_auxiliary`; TAP: Γ-constants (Q2) |
| T2 `δ`-structure with an archimedean component | the ghost-ring `δ` at finite places (AGZ `frobenius_eq_pow_add_delta`) and the intertwining scalars of operators on auxiliaries at `∞` | TAP target (Q1) |
| T3 Sieve-ordered Schur elimination | elimination of the comb by prime rays, multiples of `2`, then `3`, …, keeping each correction explicit | TAP target |
| T4 Twin suite | §2.1 in one module, with each twin's value on each meter | TAP target |
| T5 One-sided transfer kernels | positive Neumann transfer for dilation stencils, unifying the halving identity and the midpoint Green kernel | TAP target (Q8) |

## 7. Pillar theorems (targets)

| # | Theorem | Answers | Status |
|---|---|---|---|
| 1 | **Abstract Stepanov producer.** A ring with a derivation `∂`, an endomorphism `F` with `∂ ∘ F = 0`, a fixed set and a zero count; the count theorem; the hyperelliptic instance recovers Hasse–Weil | criterion 1, Q1 | target |
| 2 | **Separability in characteristic zero.** No nonzero derivation of a `ℚ`-algebra kills an Adams operation; every integral intertwiner of the Adams operations has integer scalars, so no archimedean contraction exists on integer auxiliaries | Q1, T2 | target |
| 3 | **Zero-blind prices are transfers.** For every balanced stencil the output on a window and the reading of its complement have the same exponent | Q3, Q5 | target |
| 4 | **Axiom ladder.** Integer norms with a square-root integer count do not produce any fixed power saving | Q6, criterion 2 | target |
| 5 | **Twin suite** | criterion 2, T4 | target |
| 6 | **Positive Neumann transfer** | Q8, T5 | target |
| 7 | **Quadratic producers** | Q7 | target |
| 8 | **Riemann–Roch count with `Γ` constants** | Q2, T1 | target |

## 8. Traps

| Trap | Truth |
|---|---|
| A tight inequality is a producer | An identity read through `Λ` is a meter; slack is what a producer harvests |
| Raising the multiplicity sharpens a divisibility producer | Price and reading scale together (AGT `ghost_ledger`) |
| A closed-form price is information about the primes | Its generating function has no pole at a zero; it moves the problem to the complement |
| Integrality is selective | Every integrality mechanism on the prime torus holds for every Euler product over the rational primes (ALST); the one-off has integer norms |
| An integer count to square-root precision forces the primes | Beurling systems with good integer counts carry zeros near `Re s = 1` (Q6) |
| `ℓ`-adic inseparability is free multiplicity | Its gain at `ℓ` is paid at `∞` by the product formula |
| The Stepanov degree bound is a producer | Its price is `lcm(1,…,N) = e^{ψ(N)}`: it is circular |
| Purity of Jacobi sums is a positivity argument | It is an identity between two pairings; its `ζ` analogue is RH |
| Combining exact meters lowers `Θ` | Exact rows combine to exact rows |
| A producer valid for all Euler products separates `ζ` | The one-off and the Schur twin are Euler products |

## 9. Open research topics

1. A comparison over `ℤ` with sublinear slack whose price is not computed from `ψ` (Q5).
2. The reach of quadratic and higher-degree readings of `Λ` (Q7).
3. An operator on integer auxiliaries that intertwines the Adams operations and contracts at the real
   place up to an explicit integrality loss (Q1, T2).
4. A Riemann–Roch count on the arithmetic square with the `Γ` factor in its constants (Q2).
5. Sieve-ordered elimination of the comb that uses the sign of `Λ` along prime rays (T3).

## 10. Context

| Programme | Interface |
|---|---|
| ArithmeticLefschetzStepanovTheory | Stepanov's method on the prime torus; Lefschetz = Stepanov; the one-off calibration |
| ArithmeticProduction | mean-value producers: mollifiers, length laws, entry filters, mimic battery |
| ArithmeticAuxiliaryDynamics | stencil producers; the rate is the Mertens level |
| ArithmeticGaugeTheory | factorial ratios have Chebyshev precision |
| ArithmeticEffectivityTheory | Nair's integrality floor |
| ExclusionOfTheCriticalState, ExceptionalLayerTheory | the halving identity and the midpoint Green kernel (transfers) |
| AbsoluteGeometryOfSpecZ, SurfaceOfSpecZ | ghost ring, `δ`-structure, Frobenius graphs, point counts |
| TensorPowerProgramme | purity of Jacobi sums by the two pairings |
| ArithmeticPositiveDuality, BlackHoleRingdown, FloorFreeArithmetic, ArithmeticCastelnuovoSeveri | the twins |

TAP sits between the receiver programmes (which state what an input must deliver) and the meter
programmes (which read `Θ` exactly). It does not add a route: it asks of every route whether its central
inequality has slack, at which place the slack is paid, and which twin its axioms admit.

## 11. Success criteria and contributions

**Criteria a producer must meet** (§2.9).
1. **Calibration.** It reproves inside the theory the Riemann hypothesis for curves, starting with the
   hyperelliptic case, and Riemann–Roch with exact constants.
2. **Selection.** Its argument does not apply to any twin of §2.1.
3. **Non-circularity.** Its price is not computed from `ψ`.
4. **Output.** A one-sided bound for one meter at some exponent, landing in a proved implication.

**The programme succeeds** when Q1–Q8 have theorem-level answers, T1–T5 exist in their strongest
unconditional form, and each producer class in the corpus has its axiom level, its twin and its reach
fixed by theorems.

**A contribution must** be unconditional; name its construction, reading and price; state its output
exponent or prove that none below a named value exists; state its axiom level and the twin at that
level; say at which place the slack is paid; and improve a pillar, answer a question, or add a tool used
by another module. A restatement of a corpus equivalence is not a contribution.
