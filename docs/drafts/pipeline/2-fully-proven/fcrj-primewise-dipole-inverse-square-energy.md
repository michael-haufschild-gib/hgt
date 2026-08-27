# FCRJ primewise dipole inverse-square energy

- **ID:** FCRJ-PDISE
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper-proven; Lean implementation complete, lint promotion pending)
- **Source:** `critical-multiplicative-compensated-cancellation-rh.md` · Conjecture loop 63
- **Statement:** Literal primewise dipole transport controls complete differentiated endpoint
  energy, eliminating unresolved pair mass from physical FCRJ tail.

## Goal

For finite physical aperture, set

```text
W = sum_(p in P) log(p)/p,
D = sum_(p in P) (log(p)/p)|z_end(p)-z_start(p)|,
U_n = physical endpoint moment.
```

Prove unconditionally for every `N>=1`

```text
sum_(n>N) |U_n|^2/n^2 <= 4 W D,                       (DE1)
N sum_(n>N) |U_n|^2/n^2 <= 4 N W D.                   (DE2)
```

Also transport `(DE2)` through exact endpoint differentiation to raw FCRJ character amplitudes
with multiplier `A^2/(4 pi^2)`.

## Gates

- [x] 0 → 1 in-progress: corpus search, primary-literature audit, frozen source statement
- [x] 1 → 2 fully-proven: dependency-closed paper proof and hostile constant audit
- [ ] 2 → 3 formalized: exact Lean theorem, targeted build, axiom and lint gates
- [ ] 3 → 4 publication-ready: independent expert priority review

## Corpus frontier `[CORPUS]`

1. `norm_xiPhysicalPrimeLogEndpointCircleMoment_le_min_dipole_total` gives
   `|U_n|<=min(nD,2W)` for literal source.
2. `HilbertSchmidt.tsum_reciprocal_square_tail_le` gives symbolic tail
   `sum_(r>=0)(M+1+r)^(-2)<=1/M`.
3. `Summable.sum_add_tsum_nat_add` supplies exact finite-prefix/tail split.
4. Corpus search found no theorem combining these into physical `W D` energy law.

## External frontier `[LITERATURE]`

Fourier/transport comparisons and Kantorovich norms for signed measures are established general
infrastructure; relevant primary sources include Steinerberger, *Wasserstein Distance, Fourier
Series and Applications* (arXiv:1803.08011), Borda, *Berry--Esseen smoothing inequality for the
Wasserstein metric on compact Lie groups* (arXiv:2005.04925), and Piccoli--Rossi--Tournus,
*A Wasserstein norm for signed measures* (arXiv:1910.05105). Targeted search found no literal
prime-log aperture formula `(DE1)--(DE2)` or FCRJ use. Novelty claim is restricted to exact physical
specialization and route burden.

## Conjecture loop A — pointwise geometric-mean summation

`[FAILED]` Geometric interpolation of `nD` and `2W` yields harmonic majorant `2WD/n`, which is not
summable. Pointwise interpolation cannot close complete inverse-square energy.

## Conjecture loop B — source-scale head/tail split

`[PAPER-PROVED] [LEAN-PROVED] [POSITIVE SURVIVOR]` `(DE1)--(DE2)` hold.

### Paper proof plan

First prove `0<=D<=2W`. If `D=0`, loop 62 forces every `U_n=0`. For `D>0`, choose
`L=floor(2W/D)`. Loop 62 gives

```text
sum_(n>N) |U_n|^2/n^2
  <= L D^2 + 4W^2/(N+L).
```

Floor inequalities give `L D<=2W` and, since `N>=1`, `2W<=(N+L)D`. Each term on right is at most
`2WD`, proving `(DE1)`; multiply by `N` for `(DE2)`.

### Hostile audit

- `D=0` is handled separately; no division-by-zero convention is used.
- Cross-prime cancellation is not assumed; only exact primewise endpoint pairing enters.
- No activity, phase separation, cluster partition, asymptotic limit, or RH premise enters moment
  bound.
- Raw-amplitude corollary needs standard physical `A>0` and aperture-activity conditions solely for
  existing differentiation identity.
- Constant `4` is safe, not asserted sharp.

## Open core

Lean implementation is complete in
`formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeEndpointDipoleInverseSquareEnergy.lean`.
Direct checking, targeted build, axiom audit, and umbrella wiring pass; capstones depend only on
`propext`, `Classical.choice`, and `Quot.sound`. Global formal lint is presently blocked by unrelated
concurrent module `GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenBlockConvolution` missing its
theorem-area umbrella import, so Stage-3 promotion is withheld. Next determine whether moving
physical apertures force `N W D -> 0`; this arithmetic source estimate remains separate.
