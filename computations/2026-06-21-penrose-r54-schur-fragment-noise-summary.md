# R54 - Schur fragment noise

Status: dead end / generic near-boundary Schur instability.

Random source chain:
- seed RandomNode: sensitivity to discretization of stochastic differential equations
- broad topic RNG: 14, cosmological N-body simulation discreteness noise
- NODE RNG: 6, warm dark matter simulations often form artificial filament fragments from discreteness noise
- target-file RNG: 1, `docs/consolidated/08-conjectures-required.md`
- target-topic RNG: 30, G-C19 primitive Schur/Hodge equivalence
- scientific-method RNG: 14, weaken
- perturbation-method RNG: 11, run experiments

## Transfer

The weakened G-C19 stress test is:

```text
finite primitive Schur/Pick signatures near a cutoff can contain artificial
fragments caused by tiny coefficient/discretization noise.
```

This tests the obstruction named in the proofing worklog: finite signatures
may pass fake families and need not detect missing geometry.

## Evidence

Script:

```text
computations/2026-06-21-penrose-r54-schur-fragment-noise.py
```

NODE validation:

```text
1D filament, 80 bins, 500 particles: artificial_peak_count=3
```

Schur-boundary toy:

```text
polynomial: z^36 - 1 + coefficient noise

eps=1e-12: inside_count range=14..22, mean=18.75
eps=1e-10: inside_count range=14..22, mean=18.75
eps=1e-08: inside_count range=14..22, mean=18.75
eps=1e-06: inside_count range=14..22, mean=18.75
eps=1e-04: inside_count range=14..22, mean=18.75
```

Tiny coefficient-scale perturbations split near-boundary roots differently
inside/outside the unit disk, creating large finite Schur-count variation.

## Verdict

Dead end for non-reducing count. This is a useful fake-family/noise stress for
G-C19, but it is generic Schur-boundary instability and does not construct the
missing primitive projective system, Hodge comparison, or source-built fake
failure theorem.
