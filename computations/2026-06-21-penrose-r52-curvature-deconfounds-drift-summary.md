# R52 - curvature deconfounds affine drift

Status: dead end / reduce-to-known local curvature theorem.

Random source chain:
- seed RandomNode: inbreeding changes expected genotype-pair distributions
- broad topic RNG: 2, Wright-Fisher diffusion with assortative constraints
- NODE RNG: 19, selection and assortment can be statistically confounded in inferred drift terms
- target-file RNG: 2, `docs/consolidated/01-landscape-and-geometry.md`
- target-topic RNG: 12, RH/on-line curvature statement in `where the zeros live`
- scientific-method RNG: 9, test small cases
- perturbation-method RNG: 18, look for the right theorem

## Transfer

The NODE says first-order drift inference can confound selection and
assortment. The target suggests that the curvature hierarchy deconfounds local
zero-source displacement:

```text
first derivative / drift: affine background can confound
second derivative / curvature: affine background vanishes
```

## Evidence

Script:

```text
computations/2026-06-21-penrose-r52-curvature-deconfounds-drift.py
```

NODE validation:

```text
true selection=0.800, true assortment=0.800
one-covariate inferred selection=1.609
```

Small local-zero cases:

```text
affine drift b=-5: median slope online=-5, offline=-5, center curvature online=-1.0e9, offline=+3.125e2
affine drift b= 0: median slope online= 0, offline= 0, center curvature online=-1.0e9, offline=+3.125e2
affine drift b=+5: median slope online=+5, offline=+5, center curvature online=-1.0e9, offline=+3.125e2
```

Off-line quartet boundary:

```text
tau/a=0.00: C_a=+312.500000
tau/a=0.50: C_a=+150.000000
tau/a=1.00: C_a=+0.000000
tau/a=1.50: C_a=-36.982249
```

## Verdict

Dead end for non-reducing count. The result is correct and useful as a
deconfounding explanation, but it is exactly the existing local curvature
theorem shape: second derivatives remove affine drift, and off-line quartets
have positive core curvature. No new global bridge or invariant was produced.
