# Actual-prime first-trace exponential flat graph fracture

- **ID:** prime-first-trace-exponential-flat-graph-fracture
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `projective-quantum-recurrence-rate-distortion/main.tex`;
  `ArithmeticSchurFirstTraceNonclosability.lean`; positive survivor of the closed first-trace
  no-escape cluster
- **Statement:** The actual-prime first-trace graph witness has source size
  `a_p = Θ(1 / log p)` and response error `b_p = Θ(1 / p)` with explicit constants, hence
  `exp (-4 / a_p) ≤ b_p ≤ 8 exp (-1 / (2 a_p))`. Along consecutive primes,
  `log(p) X_p → e₁` and the intrinsic rate-distortion grade `a_p(-log b_p) → 1`.

## Goal

Retain quantitative arithmetic data discarded by binary graph closure.  Determine the regularity
class in which a source-native HGT reporter could still detect the singular first-trace anomaly
and eventually constrain the modulus `p^(Re ρ - 1/2)` at a Xi zero.

This theorem is not RH and does not supply the missing source-to-zero reporter.

## Gates

- [x] 0 → 1 in-progress: source-pure actual-prime witness and rate question
- [x] 1 → 2 fully-proven: complete coordinate proof below, no open dependency
- [x] 2 → 3 formalized: Lean theorem
  `RHTower.primeFirstTrace_farWitness_exponential_graph_sandwich`; targeted `lake build` green;
  only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] 3 → 4 publication-ready: standalone paper and broader external novelty audit

## Definitions

For a prime `p`, let `r = farPrime p`, so Bertrand gives

```text
p² < r ≤ 2p².
```

Write

```text
w_p = primeFirstTraceWitness p r,
X_p = primeHardyKernelMap w_p,
Y_p = primeFirstTraceClock w_p - e₁,
a_p = ‖X_p‖,
b_p = ‖Y_p‖.
```

The previous nonclosability theorem proved only

```text
a_p ≤ 4 / log p,
b_p ≤ 8 / p.
```

## Theorem

For every prime `p`,

```text
1 / (2 log p) ≤ a_p ≤ 4 / log p,
1 / p ≤ b_p ≤ 8 / p,
exp (-4 / a_p) ≤ b_p ≤ 8 exp (-1 / (2a_p)).
```

For `p_n` the `n`th prime and the corresponding `X_n,Y_n,a_n,b_n`,

```text
log(p_n) X_n → e₁,
log(p_n) a_n → 1,
log(b_n) / log(p_n) → -1,
a_n(-log b_n) → 1,
b_n/a_n^N → 0 for every fixed N.
```

### Proof `[PROVED HERE]`

The first Hardy coordinate of the source is exact:

```text
X_p(1)
  = (p / log p)(p⁻¹ - r⁻¹)
  = (1 - p/r) / log p.
```

Since `r ≥ p²` and `p ≥ 2`,

```text
p/r ≤ 1/p ≤ 1/2.
```

Coordinate evaluation is contractive on `ℓ²`, so

```text
a_p ≥ |X_p(1)| ≥ 1 / (2 log p).
```

The first coordinate of the response error is also exact:

```text
Y_p(1) = -p log r / (r log p).
```

From `r ≥ p²`,

```text
log r ≥ 2 log p.
```

From `r ≤ 2p²`,

```text
p log r / (r log p) ≥ p(2 log p) / (2p² log p) = 1/p.
```

Again coordinate evaluation is contractive, hence `b_p ≥ 1/p`.

For the exponential form, `a_p ≤ 4/log p` implies

```text
log p ≤ 4/a_p,
exp (-4/a_p) ≤ exp (-log p) = 1/p ≤ b_p.
```

Likewise `1/(2 log p) ≤ a_p` implies

```text
1/(2a_p) ≤ log p,
b_p ≤ 8/p = 8 exp (-log p) ≤ 8 exp (-1/(2a_p)).
```

For the exact normal direction, use

```text
p·primeHardyTail(p) = e₁ + hardyFirstTailRemainder(1/p).
```

The remainder norm is at most `2/p`, while

```text
‖p·primeHardyTail(r)‖ ≤ 2p/r ≤ 2/p.
```

The witness identity therefore gives

```text
‖log(p) X_p - e₁‖ ≤ 4/p.
```

Hence `log(p_n)X_n → e₁` and `log(p_n)a_n → ‖e₁‖=1`. The response bounds give

```text
-log(p_n) ≤ log b_n ≤ log 8 - log(p_n),
```

so `log b_n/log p_n → -1`. Multiplying the two normalized limits gives
`a_n(-log b_n) → 1`.

Finally,

```text
0 ≤ b_n/a_n^N
  ≤ (8/p_n)/(1/(2log p_n))^N
  = 8·2^N(log p_n)^N/p_n → 0.
```

Thus every finite algebraic order is blind while the exponential grade stays equal to one. This
closes the paper proof.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/PrimeFirstTraceExponentialFlatGraphFracture.lean`
- Exact coordinate theorems:
  - `primeHardyKernelMap_farWitness_apply_one`
  - `primeFirstTraceClock_farWitness_sub_basisOne_apply_one`
- Lower bounds:
  - `one_div_two_log_le_norm_primeHardyKernelMap_farWitness`
  - `one_div_prime_le_norm_primeFirstTraceClock_farWitness_sub_basisOne`
- Exponential sandwich:
  - `primeFirstTrace_farWitness_exponential_graph_sandwich`
- Canonical normal direction and exact rate grade:
  - `norm_log_smul_primeHardyKernelMap_farWitness_sub_basisOne_le`
  - `tendsto_log_smul_primeHardyKernelMap_nullSequence_basisOne`
  - `tendsto_log_mul_norm_primeHardyKernelMap_nullSequence_one`
  - `tendsto_log_norm_primeFirstTraceClock_error_div_log_prime_neg_one`
  - `tendsto_primeFirstTrace_exponentialRateDistortion_one`
  - `tendsto_primeFirstTrace_error_div_source_pow_zero`
- Verification:
  - `lake env lean GaloisForLFunctions/RHTower/PrimeFirstTraceExponentialFlatGraphFracture.lean`
  - `lake build GaloisForLFunctions.RHTower.PrimeFirstTraceExponentialFlatGraphFracture`
  - `#print axioms`: only standard Lean foundations

Global `scripts/formal_tools.py lint` no longer reports this module unreachable.  It still exits
nonzero because three unrelated, pre-existing RHTower modules are absent from the umbrella:
`KrylovGramPrefixTransfer`, `LocalHorizonQuantumReturnLaw`, and
`SpectralMeasureExactReturnClassification`.

## Novelty and collision audit

### What is not new

Exponential residuals and their logarithmic stability consequences occur in exponentially accurate
quasimodes and severely ill-posed inverse problems.  Therefore “exponential flatness defeats
finite-order control” is not itself a novel general principle.

Relevant parent literature:

- Holzegel--Smulevici, *Quasimodes and a Lower Bound on the Uniform Energy Decay Rate for Kerr-AdS
  Spacetimes*, arXiv:1303.5944.
- Agapiou--Stuart--Zhang, *Bayesian Posterior Contraction Rates for Linear Severely Ill-posed
  Inverse Problems*, arXiv:1210.1563.

### Provisional new content

Exact searches found no occurrence of this two-sided rate law for the actual-prime
Gamma-valuation/Hardy first-trace graph witness.  Provisional novelty is restricted to the
arithmetic-HGT realization:

```text
actual primes + first-trace nonclosability
  + exact reciprocal-log source scale
  + exact reciprocal-prime response scale
  + canonical normal ray e₁
  + exact dimensionless rate-distortion grade 1
  + Lean-certified exponential graph sandwich.
```

A broader literature audit remains necessary before publication.

## Consequence for RH mechanism search

The closed graph contains only the zero-vacuum relation, and all continuous single-valued riggings
in the corpus fail.  The new rate law sharpens that no-go:

```text
finite-order closure/jet category
  cannot retain the first-trace response;
an exponential associated-graded quotient is required.
```

The corpus rules out the tempting local-Stokes implementation.  Gamma and `E₁` Stokes data are
Tate-local, and the neutral one-phase Gamma boundary theorem makes common beyond-all-orders
factors projectively scalar.  A scalar analytic normal-cone blow-up also amplifies rather than
repairs the existing Möbius--Gamma/Xi source-gain defect.  The required quotient must therefore be
global Euler--Gamma connection/critical-Mellin data, not local Gamma Stokes data.

This makes the projective recurrence paper useful as a selector, not as a proof source. If a
source-canonical global rate-graded fibre supplied a nonzero on-shell vector `v_ρ` with

```text
D_p v_ρ = p^(ρ - 1/2) v_ρ
```

and a source-fixed recurrent/isometric normalization, projective recurrence would force
`|p^(ρ-1/2)| = 1`, hence `Re ρ = 1/2`.

The missing theorem is not the scalar inequality or recurrence conclusion; either is an RH
criterion when asserted only at zeros.  The missing theorem must construct, before restricting to
Xi zeros:

1. an exponential associated graded of the global Euler--Gamma first-trace graph;
2. a phase-bearing critical-Mellin curvature class, nonzero modulo gauge, with source-fixed norm;
3. prime-clock covariance with multiplier `p^(s-1/2)`;
4. an on-shell descent from the source equation to Xi zeros.

The formal clock-compass principal-symbol theorem is relevant only to item 2: a left-invertible
complete compass cannot erase a non-gauge Riemann-symbol polarization. It does not construct the
curvature class, prove positivity, or supply covariance. Moreover its classical principal symbol
is finite-order, whereas this card's anomaly is exponentially flat. The actual next bridge is an
**exponential Riemann principal symbol** on the global rate-graded Euler--Gamma cone, followed by
the existing clock-compass left inverse.

This is the surviving open core.

## Log

- 2026-07-28 — projective recurrence paper audited; binary recurrence retained only as purity
  selector.
- 2026-07-28 — exact first coordinates exposed the missing lower bounds.
- 2026-07-28 — paper proof closed; exponential rate class identified.
- 2026-07-28 — theorem formalized and targeted module build completed.
- 2026-07-28 — local Stokes implementation killed by the corpus Tate-local/projective-scalar
  theorems; open core corrected to global exponential associated-graded critical-Mellin curvature.
- 2026-07-28 — canonical normal direction and exact rate-distortion grade `1` proved in Lean.
