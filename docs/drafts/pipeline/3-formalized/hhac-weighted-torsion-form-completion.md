# Weighted completion of the actual torsion forms

- **ID:** hhac-weighted-torsion-form-completion
- **Stage:** 3-formalized
- **Type:** WEIGHTED ARITHMETIC FORM COMPLETION
- **Status:** Formalized and directly audited

## Exact statement

For `δ>0`, let `Hδ` consist of real positive-conductor sequences with
`‖x‖δ²=Σ_n n^δ x_n²<∞`. Put `rε(m,n)=exp(−ε(1/m+1/n))` and

`Tε(m,n)=twistedEnergy(rε(m,n),m,n)`,
`Rε(m,n)=Tε(m,n)+[m=n]log(2ε)`,
`L(m,n)=−weilPrimeKernel(m,n)+[m=n]tameDifferent(n)`.

For every `ε>0`, the original pair series define continuous symmetric bilinear
forms on `Hδ`. All three series converge absolutely on every pair of probes.
The raw form is positive: `Tε(x,x)≥0`. The scalar normalization is exactly

`Rε(x,y)=Tε(x,y)+log(2ε)Σ_n x_n y_n`.

For every `0<α≤1` with `2α<δ`, there is a constant independent of `ε` such that

`‖Rε−L‖op≤Cδ,α ε^α`.

Thus the actual scalar-renormalized forms converge in operator norm as
`ε→0+`. Every positive conductor weight is admitted, for example with
`α=min(δ/8,1)`. The carrier is infinite-dimensional; finite conductor
truncations converge in its norm.

## Proof

On positive conductors the prime kernel satisfies

`0≤P(m,n)≤log(mn)gcd(m,n)/√(mn)`.

On a divisibility pair this is `Λ(n/m)≤log(mn)`; elsewhere the prime entry
vanishes. Absorb the logarithm into an arbitrarily small positive power and
apply the proved weighted gcd estimate. The diagonal uses
`0≤tameDifferent(n)≤log n`. Hence

`Σ_{m,n∈S}|x_m x_n L(m,n)|≤Aδ Σ_{n∈S}n^δx_n²`.

The [mixed-spacing estimate](hhac-weighted-mixed-spacing-convergence.md)
gives the corresponding absolute error bound `Dδ,α ε^α Σ n^δx_n²`.
Adding these bounds controls `Rε`. Subtracting the exact scalar diagonal
controls `Tε`, since `Σx_n²≤Σn^δx_n²`.

Square conductor windows exhaust all positive pairs. Uniform finite absolute
bounds therefore give summability and the same infinite quadratic bounds.
For mixed probes, compare with `z=|x|+|y|`; its weighted square mass is at most
twice the sum of the two masses. Normalizing both arguments yields the
bilinear bound `4C‖x‖δ‖y‖δ`.

Coordinates `u_k=(k+1)^(δ/2)x_(k+1)` identify the carrier exactly with real
`ℓ²`. The inverse respects addition and scalar multiplication, preserves the
norm and represents every finite-mass sequence. Coordinate atoms give infinite
rank, and their finite sums converge. Absolute convergence makes the original
kernel series bilinear and symmetric and permits the diagonal sum to collapse
to `Σx_ny_n`. Applying the bilinear bound to the error gives the operator rate.
Finally, square partial sums of the raw quadratic form are the existing
positive finite spacing forms, so their limit is positive.

## Lean realization

All modules belong to `HeightHomotopyArithmeticCounts` and its umbrella.

| Module | Main content |
|---|---|
| `WeightedTorsionLimit` | Prime-kernel envelope and full finite limiting bound |
| `InfiniteTorsionForms` | Absolute infinite series and exact quadratic comparison |
| `WeightedProbeSpace` | Exact Hilbert coordinates, truncation density and infinite rank |
| `KernelHilbertCompletion` | Continuous bilinear completion retaining the original series |
| `WeightedTorsionOperators` | Actual operators, scalar counterterm, positivity and operator-norm convergence |

Capstones are `spacingOperator_norm_error_rate`,
`tendsto_spacingRenormalizedOperator`, `spacingOperator_scalar_counterterm`
and `spacingRawOperator_nonneg`. All five modules pass direct
`lake --old env lean` checks. The twelve operator capstones have transitive
axioms exactly `[propext, Classical.choice, Quot.sound]`.

## Existing work and boundary

The finite prime-form and tame-diagonal bounds come from
`ArithmeticElectrostatics` and `RenormalizedArithmeticPotentialTheory`.
Finite spacing positivity comes from `ArithmeticIntersectionTheory`.
[Hilberdink–Pushnitski](https://arxiv.org/abs/2110.14323) establish spectral
results for LCM matrices; substituting `τ=1`, `σ=(1−δ)/2` identifies the
normalized weighted gcd majorant with their family. Hilbert completion and
this majorant belong to established operator theory. No literature-priority
claim is made for the actual torsion comparison.

The finite renormalized limit is already indefinite. This completion supplies
neither an arithmetic product formula nor self-energy payment. Its addition
is coefficient addition; the missing arithmetic height construction remains
open. The unweighted error prime row is unbounded, so zero conductor weight
cannot satisfy this operator comparison. Endpoint rates and optimality are
not asserted.
