# Scattering charge survives finite-energy subtraction

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 3.

## Target

For an actual zeta zero `w` with `0<Re w<1`, `Im w>0`, the
scattering-subtracted field satisfies

```text
lim_(a→∞) a F_w(a) = −Λ(w−1)/Γ_R(w) ≠ 0,
0 < ∫₀∞ a^(Re w−1) |F_w(a)|² da < ∞.
```

## Proof

The certified constant-term expansion gives `F_w=T_w−B(w)/a` when
`ζ(w)=0`. The Fourier-tail bound implies `|a T_w(a)|≤C a^(−Re w/2)→0`.
The functional equation sends `Λ(w−1)` to `Λ(2−w)`, whose zeta and
Gamma factors are nonzero in `Re(2−w)>1`. Thus the limit is nonzero.
Consequently `F_w` is nonzero at every sufficiently large height, so the
nonnegative, integrable weighted square is positive on a set of positive
measure. Its integral is strictly positive.

## Scope

This recovers the actual scattering charge from canonical finite-energy
data. It proves no spectral gap or positivity law on all eigenfunctions.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerScatteringCharge.lean`, namespace
`MayerScatteringCharge`: `scatteringCoefficient_ne_zero`,
`scaledTail_tendsto_zero`, `core_charge_limit`, `core_eventually_ne_zero`,
and `weighted_energy_pos`. The direct production check passes without
warnings; all five declarations use only `propext`, `Classical.choice`,
and `Quot.sound`.
