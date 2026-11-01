# Actual Mayer traces in primitive-orbit coordinates

- **Stage:** 3-formalized
- **Type:** Theorem
- **Parent:** [primitive modular orbit product](../1-in-progress/gauss-mayer-primitive-orbit-product.md).
- **Inputs:** [primitive pair-cycle multiplicities](gauss-mayer-primitive-pair-cycle-multiplicities.md), [actual word traces](gauss-mayer-countable-word-traces.md).

## Theorem

Let `M(u)` be the actual integral matrix of a nonempty pair word `u`, and
let `λ(u)>1` be the expanding root of
`X²−tr(M(u))X+1`. Then

```text
λ(rotation_k u)=λ(u),
λ(u^r)=λ(u)^r  (r≥1).
```

This is the same multiplier as the actual Gauss fixed-point multiplier.
For a primitive pair cycle `c`, write `ℓ(c)` for its pair length and `λ_c`
for its multiplier. Under the exact source bijection `a ↔ (c,r,i)`,
with `r≥1` and `0≤i<ℓ(c)`, the source half-length is `rℓ(c)`, its fixed-point
multiplier is `λ_c^r`, and its literal even-word trace-series term is

```text
z^(2rℓ(c))/(rℓ(c)) · (λ_c^r)^(−w)/(1−(λ_c^r)⁻²).
```

The statement holds for all complex `w,z`; it is an identity of individual
terms before any infinite summation. The indexing makes no additional
identification with inverse classes.

## Proof

Every nonempty pair word gives a strictly positive integral determinant-one
matrix. Its two diagonal entries are positive integers. If its trace were
at most two, both diagonal entries would be one, contradicting positive
off-diagonal entries and determinant one. Thus its trace exceeds two and
its expanding root exceeds one.

Two roots `x,y>1` of `X²−tX+1` must agree: subtraction gives
`(x−y)(x+y−t)=0`; the second factor vanishing would force `xy=1`.
Cyclic splitting changes a product `AB` into `BA`, preserving trace and
hence the expanding root.

The certified spectral decomposition is
`M^r=λ^r P+λ^(−r)(I−P)`. The defining formula for `P` and the quadratic
equation for `λ` give `tr(P)=1`. Taking traces gives
`tr(M^r)=λ^r+λ^(−r)`. Consequently `λ^r>1` satisfies the characteristic
quadratic of `M^r`; root uniqueness proves the repetition law.

The actual source fixed-point multiplier exceeds one and satisfies the
same characteristic quadratic. The exact even-word/pair-matrix identity
therefore identifies it with `λ(u)`. Compose the certified source-to-pair
bijection with the primitive-cycle indexing. Their length laws give
source half-length `rℓ(c)`, while rotation invariance and the power law give
fixed-point multiplier `λ_c^r`. Substituting these into the certified
literal fixed-point trace formula yields the displayed term, including
its denominator `rℓ(c)`.

## Lean certificate

Modules in `RenormalizedIntersectionTheory`:

- `GaussMayerPairMultiplier.lean`, namespace `MayerPairMultiplier`:
  `actualPairedMatrix_trace_gt_two`, `pairMultiplier_rotate`,
  `pairMultiplier_wordPower`, `wordMultiplier_eq_pairMultiplier`.
- `GaussMayerPrimitiveOrbitWords.lean`, namespace `MayerOrbitWords`:
  `multiplier_gt_one`, `sourceCycleEquiv`, `toPairs_sourceCycleEquiv_symm`,
  `source_index_length`, `source_multiplier`, `source_trace_term`.

The full namespace prefix is
`GaloisForLFunctions.RenormalizedIntersectionTheory`.

Both modules passed direct production checks without diagnostics. All ten
transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. Both modules are imported by the programme umbrella.

## Scope

This identifies the actual summands in primitive-orbit coordinates.
[Finite rotation sums and absolute regrouping](gauss-mayer-primitive-orbit-logarithm.md)
are certified. Geometric denominator expansion and the Euler product remain
unproved. No geodesic-length or scattering normalization is asserted.
