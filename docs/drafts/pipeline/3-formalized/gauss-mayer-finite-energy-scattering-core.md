# Finite-energy core after exact scattering subtraction

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [PM tasks](../1-in-progress/route-pm-mayer-scattering-and-escape.md), Mayer 3.
- **Input:** [actual Eisenstein lift](../3-formalized/gauss-mayer-actual-eisenstein-lift.md).

## Target

Write `B(w)=Λ(w−1)/Γ_R(w)` and, for positive heights,

```text
F_w(a) = epsteinField(w,a)
         − ζ(w)(1+a^(−w)) − B(w)(a^(−1)+a^(1−w)).
```

For `0<Re w<2`, `Im w>0`, prove the actual weighted energy is finite:

```text
∫₀∞ a^(Re w−1) |F_w(a)|² da < ∞.
```

Identify its absolutely convergent Cauchy transform with the actual Mayer
period minus the exact two axis and two scattering powers:

```text
C_w F_w(a) = period(w,a) − ζ(w)(1+a^(−w))
             − [2ζ(w−1)/(w−1)](a^(−1)+a^(1−w)).
```

At zeta zeros the axis term vanishes, but the scattering term remains.

## Proof mechanism

The actual Eisenstein constant term and exponentially decaying Fourier
tail give, at large heights,

```text
epsteinField(w,a) = ζ(w)+B(w)a^(1−w)+normalizedTail(w,a).
```

Thus `F_w(a)=normalizedTail−ζ(w)a^(−w)−B(w)a^(−1)` at infinity.
Height reciprocity gives `F_w(a)=a^(−w)F_w(1/a)`. The two power tails
are square-integrable with weight `a^(Re w−1)` exactly in the proposed
range `0<Re w<2`; the Fourier tail decays exponentially.

All four subtracted powers lie inside the certified Cauchy Mellin strip.
The axis multipliers are one. Reflection gives
`m(w,1)=m(w,w−1)`; Gamma recurrence gives
`B(w)m(w,1)=2ζ(w−1)/(w−1)`. These identities determine the exact boundary
correction without assuming an unspecified scattering form.

## Boundary

This constructs finite-energy canonical data and its actual transform.
A Hermitian form on all Mayer eigenfunctions, its scattering boundary
identity, and any off-line resonance exclusion remain separate tasks.

## Lean certificate

`RenormalizedIntersectionTheory/GaussMayerScatteringCore.lean`, namespace
`MayerScatteringCore`: `weighted_energy_integrable`,
`cauchyKernel_core_integrable`, `cauchyKernel_core_period`,
`fieldCore_reciprocity`, `fieldCore_eq_tail`, and
`scatteringCoefficient_mul_symbol_one` certify the statements above.
All 13 audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`; the direct production check passes without warnings.
