# Narain mass factorization, chiral positivity and uniform gap

- **ID:** W11-NM
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [W11 programme](../1-in-progress/ads3-scalar-modular-bootstrap.md)
- **Statement:** At every pair of two-torus target moduli, actual Narain masses satisfy chiral positivity, exact scalar factorization and an explicit positive nonvacuum gap.

## Source and identities

Write `σ=x+iy`, `ρ=B+iV`, with `y,V>0`, and set
`Qσ(v)=(yv₁)²+(v₂−xv₁)²`, `Jw=(w₂,−w₁)`.
The mass in [the Narain partition function, equations (3.5), (3.24)](https://arxiv.org/html/2107.10744#S3.SS1.SSS2) is

`M²=[Qσ(n+BJw)+V²Qσ(Jw)]/(Vy)`.

[PROVED HERE] Put `A=(y(n₁+Bw₂),n₂−Bw₁−x(n₁+Bw₂))` and
`C=(yw₂,−w₁−xw₂)`. Expansion gives

`M²±2(n·w)=[(A₁∓VC₂)²+(A₂±VC₁)²]/(Vy)≥0`.

Thus the conformal dimension `M²/2` is at least `|n·w|`.
For scalar coordinates `n=d(a,b)`, `w=c(−b,a)`,

`M²=Qσ(a,b)[(d+Bc)²+(Vc)²]/(Vy)`.

At `ρ=σ=i`, this is the ordinary sum of the four squared charges.

## Uniform gap

Set `D=(2y²+1+2x²)/y²` and `K=VyD[2+(2B²+1)/V²]>0`.
The exact difference

`(2y²+1+2x²)Qσ(v)−y²|v|²
 =2y⁴v₁²+y²(2xv₁−v₂)²+(1+2x²)(v₂−xv₁)²`

proves `|v|²≤DQσ(v)`. Also
`|n|²≤2|n+BJw|²+2B²|Jw|²`.
Combining these inequalities gives `|n|²+|w|²≤KM²`.
Every nonzero integer charge has squared size at least one, hence `M²≥1/K>0`.

## Lean

Module: `ArithmeticScatteringHolography/ModularBootstrap/NarainMass.lean`.
Namespace: `GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap`.

- `narain_chiral_nonneg`, `two_mul_abs_spin_le_massSq`.
- `narainMassSq_scalarParameters`, `narainMassSq_square`.
- `chargeEuclideanSq_le_mass`, `narainMassSq_gap`, `narainMassSq_pos`.

Final direct `lake --old env lean` check passes without warnings.
Endpoint axiom audits contain only `propext`, `Classical.choice`, `Quot.sound`.

These are exact-source algebraic and coercive bounds. They supply Gaussian
domination and a mass gap, not modular invariance or the small-height RH remainder.

## Gates

- [x] 0 → 1: actual momentum-winding mass.
- [x] 1 → 2: sums of squares and integer gap.
- [x] 2 → 3: direct Lean check and transitive axiom audit.
