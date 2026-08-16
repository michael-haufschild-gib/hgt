# Route P primitive Gamma--Julia physical Stokes Hellinger balanced-wall square law

- **ID:** `route-p-primitive-gamma-julia-physical-stokes-hellinger-balanced-wall-square`
- **Stage:** 3-formalized / needs audit
- **Type:** `[BRIDGE] [THEOREM] [P-G105P]`
- **Parent:** `route-p-primitive-gamma-julia-physical-stokes-hellinger-ordinary-determinant-cofinal-uniform.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaPhysicalStokesHellingerBalancedWallSquare.lean`

## Goal

Determine what the physical operator becomes at the forced aperture-wall ratio `r(d) -> 1`, and
whether the wall produces a genuine square-coordinate spectral object or only a formal
eigenfactor resemblance.

## Conjecturing loop

### Conjecture 1 — trace cancellation at `r = 1` collapses the physical channel

**Falsified exactly.** The balanced Hellinger channel has zero trace but satisfies

```text
A₁² = 64 I.
```

It is maximally nontrivial, with eigenvalues `+8` and `-8`. Completed-current cancellation removes
first trace, not operator mass.

### Conjecture 2 — balance gives only a product-level square resemblance

**Strengthened and proved.** For every finite Hermitian child matrix `H`, spectral factorization
first gives

```text
det(I + z(A₁ tensor H)) = product_i (1 - 64 lambda_i² z²).
```

Diagonalizing `H²` independently proves same product for the literal matrix
`I - 64 z² H²`. Therefore

```text
det(I + z(A₁ tensor H)) = det(I - 64 z² H²)
```

as an exact matrix identity at determinant level, with no fitted spectrum and no diagonal-model
premise.

### Conjecture 3 — every finite cofinal truncation preserves square symmetry

**Falsified.** An arbitrary finite subset of `Fin 2 × Nat.Primes` can retain one channel over a
prime and omit the other. Such a truncation destroys the `+8/-8` pairing and need not have an even
determinant.

### Conjecture 4 — symmetry-preserving truncations are too sparse to recover the full operator

**Falsified exactly.** For every finite prime set `t`, take both channels over every prime:

```text
S_t = univ(Fin 2) product t.
```

These channel-complete sets are cofinal among all finite channel-prime sets. Reindexing their
literal block matrices gives exactly `A₁ tensor H_t`, where `H_t` is the actual finite child block.
Thus every literal channel-complete ordinary determinant equals
`det(I - 64 z² H_t²)`.

### Conjecture 5 — evenness may be lost in the infinite determinant limit

**Falsified.** P-G105N supplies pointwise convergence for every cofinal finite-section net.
Restricting to channel-complete cofinal sections, each approximant is even. Uniqueness of limits
therefore proves the full balanced ordinary entire determinant is even. P-G105N's self-adjoint
zero theorem simultaneously keeps every zero real.

### Conjecture 6 — this identifies the existing reciprocal-gap squared Markov candidate

**Rejected as theatre.** P-G105P identifies the square of the literal cubic-coherence Stokes child
operator. Existing reciprocal-gap candidate is a different explicit carrier. Equality of their
moments, resolvents, or spectral measures is not proved and must not be inferred from shared
square-coordinate syntax.

## Paper proof

Use cubic Julia defect identity `delta² = 63/64` in balanced channel
`A₁ = [[1,8 delta],[8 delta,-1]]`; direct multiplication gives `A₁² = 64I`. Generalize finite
Hellinger spectral factorization from `Fin N` to arbitrary finite child type. At `r=1`, universal
signed factor loses its linear term and is `1-64 lambda²z²`.

For Hermitian `H`, conjugate `H` by eigenvector unitary `U`. Insert `UU* = I` between two copies of
`H` to diagonalize `H²`; determinant invariance under unitary conjugation yields
`det(I-64z²H²) = product_i(1-64lambda_i²z²)`. Compare products.

For finite prime set `t`, explicitly reindex block matrix on `univ × t` to channel times subtype
`t`; kernel definition makes it exactly `A₁ tensor H_t`. Existing finite ordinary determinant
equals literal block determinant, so square law applies. Any finite channel-prime set lies inside
`univ × image snd s`, proving cofinality. Compose P-G105N convergence with this cofinal map. Since
all approximants agree at `z` and `-z`, uniqueness of complex limits gives evenness of full entire
determinant. Existing real-zero theorem at `r=1` completes capstone. `QED`

## Novelty and anti-theatre audit

**Post-construction corpus classification:** this is bridge infrastructure, not counted as novel
RH-frontier progress. Corpus already contained multiple squared-coordinate RH carriers and much
later Suzuki reflected-wall/light completions. What remains specific here is the exact physical
Stokes-to-child-square determinant identity; it does not advance the current RH-bearing wall.

This is new operator knowledge, not restated parity:

- distinguishes zero completed trace from zero operator;
- identifies exact nonzero balanced channel square `64I`;
- proves universal physical-to-child-square determinant law for arbitrary finite Hermitian carrier;
- isolates false arbitrary-truncation claim and replaces it with an explicit cofinal
  symmetry-preserving subsystem;
- proves actual cofinal finite Stokes determinants are squared-child determinants;
- proves infinite balanced entire determinant is even and has real zeros;
- sharply separates literal child-square spectrum from unproved reciprocal-gap Markov spectrum.

Result is not RH. It does not prove aperture-parameter convergence as `d -> 0+`, identify wall
limit with completed Xi, or identify cubic-coherence child-square spectral measure with existing
reciprocal-gap carrier.

## Formal status

Lean proves unconditionally:

- `A₁² = 64I`;
- arbitrary-finite-type physical spectral factorization;
- exact balanced factor and even finite determinant;
- determinant equality with literal squared child matrix;
- actual channel-complete block reindexing and finite square law;
- cofinality of channel-complete truncations;
- evenness of full balanced ordinary entire determinant;
- real-zero inheritance and P-G105P capstone.

Direct Lean, single-target Olean emission, forbidden-declaration scan, whitespace check, and axiom
audit pass. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Module is
umbrella-wired; no umbrella build was run.

## Refined open core

Two independent wall gates remain:

1. prove compact-open convergence of physical ordinary determinants from forced `r(d)` to balanced
   child-square determinant as `d -> 0+`, despite entrywise child kernel diffusion;
2. identify resulting squared-child wall spectral measure/divisor with completed Xi source data.

The child kernel has fixed-prime entries tending to zero while its trace tends to four. Correct
wall topology therefore cannot be entrywise or trace norm without further rescaling. Scale
variable `x = 2d log p` suggests prime-weight limit `4 exp(-x) dx`; cubic coherence becomes

```text
C(x,y) = 64 x³ y³ / (x+y)⁶.
```

This predicts nonzero Hilbert--Schmidt mass

```text
integral integral 16 exp(-x-y) C(x,y) dx dy = 256/35.
```

This value is a conjectural analytic target, not yet a theorem. Proving it requires a two-prime
Abelian limit or a Laplace-factorized prime-log moment theorem. It directly falsifies any proposed
wall proof based on child operator norm collapse.

## Higher universal principle

Completed-current cancellation is grading symmetry: at wall, positive and negative channel traces
cancel while even spectral data survives as child square. Earlier trace obstruction was shadow of
using first-order current to see a second-order invariant. Universal route principle is:

```text
renormalized trace cancellation + nonzero Clifford channel square
  => square-coordinate determinant of child autocorrelation.
```

Wall problem is therefore spectral-measure convergence of `H_d²`, not entrywise convergence of
`H_d` and not direct convergence of signed first trace.

## Log

- 2026-08-16 — Balanced channel square, universal finite determinant square law, actual
  channel-complete cofinal bridge, infinite evenness, and real-zero capstone paper-proved and
  formalized.
