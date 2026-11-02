# Sharp global envelope of the central Cauchy multiplier

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 3.
- **Input:** [boundary law](../5-failed/gauss-mayer-complex-cauchy-contraction.md), [sharp high-frequency limit](../3-formalized/gauss-mayer-cauchy-high-frequency.md).

## Exact result

For the actual central multiplier, set

```text
q(w) = Γ((w+2)/4)^2 / [Γ((w+1)/4) Γ((w+3)/4)].
```

`|q(w)|<1` for `Re w>0`, hence the sharp global envelope

```text
|M K_w(w/2)| < 2^((1−Re w)/2).
```

The certified vertical limit makes this envelope optimal on every fixed
positive abscissa. It gives strict central contraction at and above abscissa one,
while preserving the certified high-frequency obstruction below one.

## Proof

Duplication identifies `m(w,w/2)=2^((1−w)/2) q(w)`. The exact imaginary
boundary law gives

```text
|q(iτ)|² = 1 − 1/[2 cosh(πτ/4)^2] < 1.
```

The Gamma arguments give holomorphy across the closed right half-plane.
For `z=(w+2)/4` and `x=Re z≥1/2`, the proved vertical Gamma-ratio
inequalities, Gamma recurrence, and real Gamma log-convexity give

```text
|q(w)| ≤ |z−1/4|/(x−1/4)
         · Γ(x)^2/[Γ(x−1/4) Γ(x+1/4)]
       ≤ |w+1|/(Re w+1) ≤ |w|+1.
```

Thus growth is polynomial. Gamma log-convexity also bounds the positive
real axis by one. The proved half-plane Phragmen–Lindelof theorem applies
to this growth, real-axis bound, and the exact imaginary-axis bound.
The strong maximum principle and the strict boundary value at zero then
give strict interior inequality. Every growth input follows from these actual Gamma quantities.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerCauchySchur.lean`, namespace
`MayerCauchySchur`: `normalized_boundary_norm_sq`,
`normalized_norm_le_linear_ratio`, `normalized_norm_le_linear`,
`normalized_norm_le_one`, and `normalized_norm_lt_one` certify the
boundary, growth, and strict Schur estimates. `norm_mellin_half_lt`,
`central_contractive`, and `central_norm_isLUB` identify the strict bound,
contraction, and exact supremum for the actual Mellin integral.
All fourteen public results passed the direct production check with only
`propext`, `Classical.choice`, and `Quot.sound` as transitive axioms.

## Boundary

This is an exact envelope for the actual Cauchy transform's scalar
multiplier. It does not supply a Mayer Hermitian form or remove scattering
boundary terms. Its threshold remains at abscissa one.
