# CCM terminal frontier ledger

**Updated:** 2026-07-24  
**Purpose:** compact persistent state; facts to reuse, routes not to repeat, and one live attack.

## Terminal theorem

For `L ≥ π/2`, set `ξ = 2π/L` and

```text
CΓ(L) = ccmFirstClockContinuousHalfWaveBudget L ξ
P+(L) = ccmFirstClockPrimeAlignedMass L ξ
P-(L) = ccmFirstClockPrimeCounterMass L ξ.
```

Corpus Lean proves unconditionally

```text
π B₁(L) = CΓ(L) + P+(L) - P-(L),
CΓ(L) > 0,
RH ↔ ∀ L ≥ π/2, P-(L) ≤ CΓ(L) + P+(L).
```

Success remains exactly one of:

1. prove this inequality for every physical `L`;
2. exhibit a concrete violating `L`;
3. exclude every CCM-admissible infinite source transport.

No criterion equivalent to RH counts as completion.

## What is known

- Gamma orientation and midpoint reflection are closed.
- Source-to-RH Landau/Volterra transfer is closed.
- Abel-to-half-weight diagonal reweighting moves outer/inner odds in the wrong direction.
- Dirichlet convolution, including operator-valued infinite convolution series, is scalar on each
  irreducible prime face.
- Aligned block subdivision gives one genuine non-diagonal infinite source carrier. Its finite
  block intersections recover the LCM ridge.
- Unrenormalized cofinal block intersections collapse to zero in `ℓ²`.
- Radial four-grade graph closure is maximally multivalued.
- Natural square-scale block Gram is indefinite; canonical source debt repairs it only to rank one.
- Cubic local Gram positivity stays inside one prime-power tower and does not transport first-clock
  half-waves.
- Half-density localization and Selberg regrouping have no cancellation inside one semiprime
  product fibre. Cancellation, if it exists, must couple distinct products.

## Mechanisms tested in current attack

### Euler exterior-current sum

**Verdict:** rejected as terminal source lift.

The literal prime-power amplitude has squared mass
`Λ(n)n^(-1-u)`. Its unnormalized skew exterior current has energy of order `u⁻⁴` at the Euler
edge. Projective normalization restores finite Fisher energy but changes the observable to an
overlap logarithmic derivative; it no longer transports the continued Xi column. Direct
cellwise summation therefore cannot supply a fixed four- or eight-unit budget.

### Normal-cone/blown-up scalar graph

**Verdict:** rejected by existing exact source-gain theorem.

At the physical critical ray the graph gain remains `1/(2(σ-1))`. Analytic removal of a scalar
zero does not make the source map nonexpansive.

### Diagonal Euler chart

**Verdict:** rejected and Lean-formalized by parallel Fable work.

Every fixed off-line divisor point escapes in the diagonal pullback and contributes vanishing
anti-causal energy. Finite divisor packets become invisible. This chart cannot transfer a local
energy bound to the global divisor.

### Ward edge `L²` quantization

**Verdict:** useful alternative detector, not source producer.

Parallel Fable work has formalized the cross-kernel algebra for the proposed edge integral.
Completing its `8π` law would yield another RH-equivalent detector. It does not prove the
first-clock source inequality unless a source identity bounds that integral.

## Do not repeat

- finite-rank, diagonal, scalar, same-prime, one-product, or radial-Fock positivity;
- another RH-equivalent criterion without an unconditional source sign;
- estimates of already-closed Gamma, Volterra, first-clock transfer, or orientation interfaces;
- an ordinary bounded contraction of the saturated four-unit detail;
- “Gamma chart is asymptotically isometric” as a global Xi-weld argument;
- product-fibre Selberg averaging: one ordinary semiprime fibre has only one real cosine mode.

## Live conjecture: cross-product Type-II Stokes transport

Let

```text
S_L = Σ_(n≤e^L) Λ(n)n^(-1/2) sin(2π log n/L).
```

Use the exact half-density second jet `e''₀ = Λ*Λ`, but do **not** group by a single product
`R=mn`. Instead retain two independent products `R=mn` and `R'=m'n'` in the full aligned-block
incidence algebra before radialization.

The required new identity must produce a source-defined antisymmetric cross-product current
`J_L(R,R')` satisfying all three clauses:

```text
Σ_(R,R') J_L(R,R') = CΓ(L) + S_L,
J_L(R,R') = |K_L(R,R')|² or a positive Gram quadratic form,
K_L is defined from aligned block/LCM incidence and Gamma-polar sewing before first-clock
scalarization.
```

Falsifiers:

1. diagonal `R=R'` reduction reproduces the known one-fibre covariance;
2. summing one index first collapses to the flat inverse convolution;
3. Gamma completion enters only as a fitted scalar;
4. radialization occurs before the cross-product Schur complement;
5. the identity assumes the target first-clock sign.

## Immediate work

Derive the two-product incidence coefficient from the aligned block projections
`P_q=A_q* A_q`, using

```text
Ran(P_m) ∩ Ran(P_n) = Ran(P_lcm(m,n)),
```

and test whether its Möbius inclusion-exclusion is a genuine positive Laplacian on the divisibility
lattice or collapses to the already-failed one-product Selberg fibre. Formalize only the surviving
exact identity or decisive falsifier.
