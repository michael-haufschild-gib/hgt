# Formal core of critical projective-horizon multiplicity

- **ID:** `projective-horizon-critical-multiplicity-core`
- **Stage:** 3-formalized
- **Type:** LEAN THEOREM PACKAGE
- **Scientific status:** `[FORMALIZED] [AXIOM-CLEAN] [NOVELTY PROVISIONAL]`
- **Paper theorem:** `projective-horizon-critical-binomial-multiplicity`
- **Module:**
  `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonCriticalMultiplicity.lean`

## Formal result

Lean defines the outer-product tensor of the two projective low-jet parameter vectors, proves that
every `2 x 2` minor vanishes, and proves that an arbitrary bilinear compatibility constraint equals
a linear matrix pairing restricted to this rank-one locus. This is the formal Segre linear-section
core.

Lean proves the boundary-exclusion lemma used in the biprojective compactification. If `p` is a
nonzero polynomial with `natDegree p<m` and `q` has a nonzero coefficient at order `n`, then

```text
exists k<m+n, coeff_k(p q) != 0.
```

The witness is the sum of the two natural trailing degrees. Multiplicativity of the trailing
coefficient proves nonvanishing; the two degree bounds place the witness below the critical
truncation. Lean also proves the complementary low-degree/low-degree version used at the corner
where both homogenizing coordinates vanish.

The exact critical intersection number is defined by

```text
criticalHorizonMultiplicity(m,n)=choose(m+n,m).
```

Lean identifies it with the coefficient of `X^m` in `(X+1)^(m+n)`, and proves positivity and
symmetry under exchanging the two horizon depths.

## Main declarations

```text
criticalHorizonSegreTensor_twoByTwoMinor_eq_zero
criticalHorizonBilinearConstraint_eq_matrixPairing_segreTensor
exists_low_mul_coeff_ne_zero
not_all_low_mul_coeff_zero
exists_low_mul_coeff_ne_zero_of_natDegree_lt
criticalHorizonMultiplicity
criticalHorizonMultiplicity_eq_chowCoefficient
criticalHorizonMultiplicity_pos
criticalHorizonMultiplicity_comm
```

## Verification

The targeted leaf build

```text
lake build GaloisForLFunctions.HTGeometry.ProjectiveHorizonCriticalMultiplicity
```

passes. A scratch `#print axioms` audit reports only `propext`, `Classical.choice`, and
`Quot.sound`. No full project build was run.

## Boundary

The module formalizes the exact valuation and intersection-coefficient cores. The standard
multiprojective Bezout and generic-etale theorems that promote these cores to a generic geometric
fiber cardinality remain in the paper proof. No entropy, probability, temporal evolution, or RH
conclusion is encoded.
