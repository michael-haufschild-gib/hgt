# Exact normalization of the odd-pair stabilizer

- **Stage:** 3-formalized
- **Parent:** [Argon routes](../1-in-progress/argon-quasi-rh-and-critical-proportion.md).

## Theorem

Write `W_Q(h)=2 Σ_{q≤Q, q odd} μ(q)² c_q(h)/φ(q)²`. If `Q≥1` and every
odd `q≤Q` divides `M>0`, then

`Σ_{i,j<M} W_Q(|(2i+1)−(2j+1)|)=2M²`.

A scalar β multiplying this weight therefore has mean β/2 in the full
`2M × 2M` integer rectangle. Unit mean forces β=2. The literal scalar 1/4 in
`stabilizerModelOddCoalSum` gives mean 1/8. Factorial periods discharge the
period condition for every cutoff. Removing coordinate one and the diagonal gives
exact mass `2M²−4M−(M−2)W_Q(0)`. The general row/column/diagonal deletion
identity is exported without a period assumption.

## Proof

Shifted Ramanujan orthogonality against conductor one gives zero complete-period
sum for every nonconstant mode. The period-square identity then gives pair mass
`M²·1_{q=1}`. Odd-conductor invariance under doubling transfers this to odd
coordinates. Erasing the first row, first column, and diagonal gives the boundary
formula.

## Scope and survivor

The corrected raw normalization is uniquely determined. The existing exact
model-plus-discrepancy identity remains valid with its present scalar; it provides
no centered estimate. These results concern arithmetic weights before applying the
signed coalescent kernel. They do not falsify the actual narrow-aperture prime-pair
conjecture: the kernel can cancel constant errors.

Incomplete periods, growing cutoffs, and comparison with actual prime weights are
[also formalized](../3-formalized/stabilizer-incomplete-periods-and-prime-comparison.md).

## Lean

`TransThresholdPairCorrelation/StabilizerPeriodNormalization.lean`: eight public
theorems, focused production check passed, umbrella import present. All transitive
axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
