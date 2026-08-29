# Compact-Weil ground locking and close-pair collision

## Question

Does the finite compact-window Weil ground realize its tiny energy by locking transform zeros to
Riemann-zero ordinates, and does that mechanism survive close pairs? These questions are more
structural than extending the scalar floor table: zero-by-zero convergence is the unverified
spectral step after fixed-window ground simplicity.

All results below are computational evidence, not proofs. No number, zero table, fitted exponent,
or observed sign is imported into Lean.

## Method

On `[-L,L]` use orthonormal even Dirichlet modes

`phi_j(x) = L^(-1/2) cos((j+1/2) pi x/L)`.

Their Fourier transforms are

`F_j(t) = 2 (-1)^j alpha_j cos(L t) / (sqrt(L) (alpha_j^2-t^2))`,

with removable values at `t=alpha_j`. A zeros-side sampling matrix `V[k,j]=F_j(gamma_k)` gives the
finite Gram `2 V^T V`. Arb/FLINT diagonalization supplies a ground trial. High-precision root
finding then locates genuine transform roots, excluding removable basis poles.

This zeros-side construction uses critical-line zeta ordinates to propose the trial. Interpreting
it as the complete Weil form uses RH; it is therefore exploratory. Blind comparison with published
geometric-side Rayleigh quotients is the normalization check.

RunPod: 128 AMD EPYC hardware threads, 755 GiB RAM. Zeros used 64 processes; FLINT used 32 threads.
Main table contains 2,200 ordinates at 240 decimal digits. Independent recomputation and direct
`zeta(1/2+i*gamma)` residual checks at indices `1,400,1000,2200` were between `1e-236` and `1e-240`.

## Validation and ground-lock result

| L | modes | computed trial Q | `-log Q` | zeros below `T*=2*pi*e^(2L)` | roots matched | worst gap-normalized offset |
|---:|---:|---:|---:|---:|---:|---:|
| 0.8 | 24 | `2.2414e-17` | 38.3368 | 4 | 4 | `2.12e-7` |
| 1.0 | 40 | `8.0639e-30` | 66.9902 | 8 | 8 | `9.81e-14` |
| 1.2 | 70 | `9.7755e-49` | 110.5468 | 16 | 16 | `6.21e-20` |
| 1.4 | 119 | `1.7485e-77` | 176.7403 | 30 | 30 | `1.79e-30` |
| 1.6 | 200 | `7.9941e-121` | 276.5341 | 55 | 55 | `2.43e-45` |
| 1.8 | 333 | `3.2187e-184` | 422.5067 | 96 | 96 | `6.92e-68` |

Values through `L=1.6` reproduce published exponents and leading scales. At `L=1.8`, finite zero
tail is not fully converged: published `-log Q` is 426.22, versus 422.51 here. It is retained only
for root-lock structure, not a new floor claim. A `150`-digit repeat of `L=1.4` exactly reproduced
the `180`-digit, 800+200-zero run at displayed precision.

Outcome: every ordinate below saturation height received one distinct real transform root. Locking
strengthens rapidly with aperture and is weakest at saturation edge.

## Hostile close-pair attack

One ordinate was moved to separation `delta` from its left neighbor while all other sampling nodes
were held fixed.

- `L=1.4`, edge pair 27/28: both roots remain distinct at `delta=1e-10`, with relative errors about
  `0.017` and `0.018`. At `delta=3e-11`, only one root remains, near pair midpoint. Across
  `delta=1e-1 ... 1e-8`, relative root error scales numerically as `delta^-3` while `-log Q` is
  essentially unchanged.
- `L=1.2`, edge pair 14/15: same cubic regime appears through `delta=1e-4`; the pair has collapsed
  by `delta=1e-8`.
- `L=1.4`, interior pair 10/11: same cubic regime persists much deeper. Both roots remain resolved
  at `delta=1e-16` with relative error about `6.94e-6`; they have collapsed by `delta=1e-32`.

Thus failure is an aperture-edge conditioning layer. Scalar ground floor can remain nearly fixed
while multiplicity-exact pair resolution is lost.

## Interpretation and route consequences

1. **Positive evidence, limited scope.** Compact-Weil ground states really do spend their degrees
   of freedom on near-exact low-zero locking, rather than only diffuse cancellation.
2. **Finite locking is not arithmetic selection.** In an `n`-mode Dirichlet window, the transform
   is a Cauchy rational function with numerator degree `n-1`; arbitrary finite target frequencies
   can be imposed by interpolation. Existence of finite locking therefore cannot prove RH.
3. **Killed inference.** Tiny scalar floor, simple even ground, and excellent isolated-zero locking
   do not imply separation-uniform or multiplicity-exact convergence. A close pair can merge to one
   reporter while scalar energy barely notices.
4. **Route O sharpening.** Any cofinal Gamma-Slepian/compact-Weil landing must control an edge-layer
   divided difference or derivative jet. Point-value head positivity alone does not quantify the
   channel needed to distinguish a pair at separation `delta`.
5. **New testable conjecture.** Before collapse, observed relative root error is proportional to
   `delta^-3`; collapse scale is approximately cube root of baseline edge-lock error. This needs an
   analytic perturbation derivation and broader basis/aperture tests before being trusted.
6. **Promising replacement mechanism.** Add a Hermite sampling channel
   `(F(gamma+delta)-F(gamma))/delta`, whose collision limit is `F'(gamma)`. This retains multiplicity
   information, but a source-side lower bound paying its normalization remains open.

## Unconditional Lean consequence

`GaloisForLFunctions.RHTower.CompactWeilClosePairSamplingCollision` proves, without numerical
inputs:

- exact average/difference decomposition of two point-sampling energies;
- exact collision of the pair to one doubled reporter;
- vanishing of the antisymmetric channel at collision;
- quadratic law
  `||f(x+h)-f(x)||^2 / h^2 -> ||f'(x)||^2`.

Targeted `lake env lean` and targeted `lake build` passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Reproduction

On RunPod, using the included scripts and a Python environment with `mpmath`, `numpy`, `scipy`, and
`python-flint==0.9.0`:

```text
python generate_zeros.py --count 2200 --digits 240 --workers 64 --out zeros-2200-d240.tsv
python ground_lock.py --zeros zeros-2200-d240.tsv --L 1.4 --modes 119 \
  --ground-zeros 1800 --tail-zeros 400 --digits 210 --threads 32 --out result-L1.4.json
python collision_scan.py --zeros zeros-2200-d240.tsv --L 1.4 --modes 119 \
  --pair-left 27 --digits 180 --out collision-fine-L1.4-pair27.json
python verify_zero_table.py --zeros zeros-2200-d240.tsv --out zero-verification.json
```

Primary numerical context: [Weil positivity in compact windows](https://arxiv.org/abs/2608.24827).

## Artifacts

- `generate_zeros.py`, `ground_lock.py`, `collision_scan.py`, `verify_zero_table.py`
- `zeros-400-d120.tsv`, `zeros-2200-d240.tsv`
- `result-L*.json`
- `collision-*.json`
- `zero-verification.json`
- `SHA256SUMS`
