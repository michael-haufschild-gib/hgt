# Xi off-line quartet thermal orientation bound

- **ID:** `xi-offline-quartet-thermal-orientation-one-eighty-four`
- **Stage:** 3-formalized
- **Type:** VALUE RELATION / RH PROOF-BURDEN REDUCTION
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT AN RH PROOF]`
- **Lean file:**
  `formal/GaloisForLFunctions/RHTower/XiOffLineQuartetThermalOrientationBound.lean`
- **Target:** combine the four-copy endpoint height law with the thermal reciprocal-square
  decomposition and the fixed-window prime--polar abscissa criterion.

## Theorem

For every multiplicity-counted Xi zero, let

```text
u = (Re rho - 1/2)^2,
v = (Im rho)^2,
z = (-(rho - 1/2)^(-1))^2.
```

On the critical line, `Im z = 0`.  Off the critical line, the formalized quartet law gives
`v > 85`, while the open critical strip gives `u < 1/4`.  Hence `v > 340*u`, and therefore

```text
336*u*v <= (v-u)^2.
```

Using the exact coordinate formulas, this is

```text
(Im z)^2 <= (1/84) * (Re z)^2.
```

After summation it should give

```text
xiThermalOrientationEnergy <= (1/84) * xiThermalSecondMoment,
(83/84) * xiThermalSecondMoment <= normalizedPrimeArchMoment 1,
xiThermalSecondMoment <= (84/83) * normalizedPrimeArchMoment 1.
```

The exact fixed-window target has the common-value formulation

```text
sigma_abs(S^-_(L,N)) <= 1
iff xiThermalOrientationEnergy = 0
iff xiThermalSecondMoment <= normalizedPrimeArchMoment 1
iff xiThermalTruncation(N,1) tends to normalizedPrimeArchMoment 1
iff RH.
```

The preceding KMS coordinate already converges unconditionally:

```text
xiThermalPositiveMoment 0 = normalizedPrimeArchMoment 0,
xiThermalTruncation(N,0) tends to normalizedPrimeArchMoment 0.
```

Thus neither finite-system positivity nor convergence of the first source coordinate remains in
the RH obligation.  The whole thermodynamic residue is the next single value.

## Open core

The factor `1/84` is quantitative and does not force the nonnegative orientation energy to
vanish.  The remaining RH obligation is to improve this strict quantitative confinement to the
zero fibre, or to prove the prime--polar negative-mass abscissa bound directly.

## Gates

- [x] existing declarations and duplicate theorem names checked
- [x] atomwise inequality proved in Lean
- [x] global source/thermal bounds proved in Lean
- [x] prime--polar abscissa equivalence connected in Lean
- [x] unconditional zeroth-coordinate source convergence proved in Lean
- [x] second-coordinate thermodynamic convergence connected to the prime--polar target
- [x] axiom audit and narrow build
