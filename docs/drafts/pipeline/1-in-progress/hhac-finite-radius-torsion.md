# Finite-radius torsion self-energy

- **ID:** hhac-finite-radius-torsion
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** review-0711 §2.11, B88
- **Statement:** After removing diagonal self-energy and the universal radial
  term, a finite torsion cloud has a quadratic, explicitly bounded radial error.

## Exact target

For distinct unit complex numbers `z_i`, real charges `a_i`, and `0<r<1`,
put `d_ij=|z_i−z_j|²`, `u=(1−r)²/r`. The identity

`|1−r z_i conjugate(z_j)|² = r d_ij+(1−r)²`

implies that the off-diagonal kernel, after adding `log r/2`, differs from
`−log|z_i−z_j|` by `−log(1+u/d_ij)/2`. Its magnitude is at most
`u/(2d_ij)`. Summing against signed charges gives an explicit inverse-chord
cost; the universal radial term is determined by total charge and square mass.

## Mechanism and scope

Use the unit-circle norm identity and `0≤log(1+t)≤t` for `t≥0`.
The existing Abel-energy theorem proves positivity and a limiting
renormalization but supplies no finite-radius error modulus. This target
retains the exact divergent diagonal and quantifies the remaining error.

It does not prove payment of self-energy by the archimedean reserve, and
does not construct a global arithmetic height. Those remain open.

## Dependencies

`ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy`
defines the actual torsion energies and their limiting prime kernel.
Check for existing quantitative radial estimates before claiming a new tool.
