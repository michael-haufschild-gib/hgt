# Penrose R41 - FID Hankel thin-cone volume bottleneck

Status: `[EXPERIMENTAL FINDING / CONJECTURE]`

Random path:

- Seed RandomNode: `Finite-size samples can mimic hyperuniformity because the smallest accessible k values are sparse and noisy`.
- Step 1 topic rng `14`: `Determinantal point processes`.
- Step 4 NODE rng `9`: determinant gives squared volume; near-linear dependence suppresses joint probability.
- Standing target: file rng `1` -> `docs/consolidated/08-conjectures-required.md`; target rng `18` -> `C-2026-06-18-044 (FID)`.

NODE constraint:

The determinant is a squared volume. Near-linear dependence suppresses determinant volume quadratically; a determinant gate can become tiny even when pairwise entries look harmless.

Transfer:

Using the corpus proxy `kappa_n = zeta(2n+1)` for free cumulants, form Hankel matrices

```text
H_m = [ kappa_{i+j+1} ]_{0<=i,j<m}.
```

Main data:

```text
size  min_eig        max_eig        log10_det    cond
2     6.376e-2       2.1466         -0.8637      3.37e1
3     5.049e-4       3.1054         -3.7836      6.15e3
4     1.144e-6       4.0803         -9.2817      3.57e6
5     9.906e-10      5.0643         -17.8015     5.11e9
6     3.933e-13      6.0534         -29.6953     1.54e13
7     5.176e-17      7.0457         -45.3230     1.36e17
8    -8.500e-17      8.0399         -61.0031     double precision loses sign
```

Perturbing only `kappa_3` downward until PSD failure gave thresholds:

```text
size 3: -7.078e-4
size 4: -2.337e-5
size 5: -1.736e-6
size 6: -2.100e-7
```

Step 11 weakened raw determinant positivity by projecting away the rank-one all-ones bulk from `kappa_n -> 1`. The projected tail remained rapidly ill-conditioned: projected condition number grew from `2.15e2` at size 3 to `2.45e15` at size 7, and double precision again lost the sign at size 8.

Interpretation:

FID positivity for this cumulant proxy lives in an extremely thin near-rank-one cone. The determinant/volume bottleneck is not a cosmetic numerical issue: it means any FID-to-RH bridge must use a basis or certificate that exposes the nontrivial tail without relying on raw Hankel determinants at increasing size.

Files:

- `computations/2026-06-21-penrose-r41-node-dpp-volume.py`
- `computations/2026-06-21-penrose-r41-fid-hankel-volume.py`
- `computations/2026-06-21-penrose-r41-step11-projected-tail.py`
