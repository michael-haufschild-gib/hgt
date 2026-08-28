# Physical prime D2 Gaussian-rational window criterion

- **ID:** `physical-prime-d2-rational-window-criterion`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / exact RH criterion (Lean)
- **Source route:** D2 / PEP / EWQ-V physical direct-prime contour
- **Statement:** RH is equivalent to eventual finite lower boundedness, on every admissible
  rational rectangle and only at Gaussian-rational D2 contour samples, of the literal physical
  square times direct infinite-prime flux at exact natural logarithmic apertures.

## Goal

Close Loop93's uncountable-sampling burden. Pointwise rational centers do not detect an irrational
Xi zero because each rational center can have a smaller zero-free neighborhood. Rational compact
windows cover every possible off-line zero, while Gaussian-rational D2 samples are dense in every
window. The resulting observation family is countable in window, aperture, and sample index.

## Gates

- [x] 0 → 1 in-progress: corpus-derived rational-window and density attack
- [x] 1 → 2 fully-proven: dependency-closed paper proof and exact route classification
- [x] 2 → 3 formalized: closed Lean theorems, direct check, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem note and independent expert audit

## Exact theorem

For positive physical widths `L,A,c`, natural aperture `n`, and centered coordinate `z`, put

```text
P_n(z) = T_{log n/2}(z)^2 * (-i * infinitePrimeFlux(1/2+i z)).
```

Call a rational rectangle `(u,v) × (x,y)` admissible when its closed envelope satisfies

```text
0 < u < v,       0 < x < y < 1/2.
```

For an original `s`-plane Gaussian-rational point `s_q`, test `P_n` at its exact centered D2
coordinate

```text
z_q = primeFluxContourCoordinate(s_q) = -i(s_q-1/2).
```

`XiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow(L,A,c)` says that some
`N` makes every `n>=N` and every admissible rational rectangle possess a finite real lower bound
for `Re P_n(z_q)` over all Gaussian-rational D2 samples `z_q` in that rectangle. Lean proves

```text
L,A,c>0 =>
XiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow(L,A,c)
  <-> RiemannHypothesis.                                  (1)
```

The stronger all-apertures condition is also equivalent to RH. In particular, Lean closes the
premise-free unit specialization

```text
XiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow(1,1,1)
  <-> RiemannHypothesis.                                  (2)
```

## Proof

Every centered Gaussian-rational point indexed by `q=(r,t)` is exactly the D2 coordinate of the
original Gaussian-rational point indexed by

```text
(1/2-t, r).
```

Lean proves both the corresponding `s=1/2+i z` identity and

```text
primeFluxContourCoordinate(gaussianRatPoint(1/2-t,r))
  = gaussianRatPoint(r,t).                                (3)
```

At every regular centered point with `0<Im z<1/2`, nonvanishing of `XiC(z)` implies nonvanishing
of `zeta(1/2+i z)`. Analyticity of zeta and of the physical transform therefore makes `P_n`
continuous there. If a regular point in an open rational rectangle satisfies `Re P_n(z)<B`, the
intersection of that rectangle with the strict sublevel set is an open neighborhood. Density of
Gaussian rationals supplies an exact centered rational point in the same strict sublevel set;
`(3)` turns it into an original D2 Gaussian-rational sample.

Assume RH. Every point in the closed envelope of an admissible rectangle is regular. The source
is continuous on that compact rectangle, so its norm has a finite upper bound `C`; hence
`-C <= Re P_n` on every D2 sample. This proves the all-apertures direction.

Conversely, false RH supplies a centered zero `alpha` with

```text
Re alpha>0,       0<Im alpha<1/2.
```

Choose rational endpoints with `alpha` in an admissible rectangle. Loop93 gives, cofinally in
`n`, regular points arbitrarily close to `alpha` where `Re P_n` is below every prescribed level.
Choose such an `n` beyond the eventual threshold and such a point inside the rectangle, below its
claimed bound. The rational strict-sublevel transfer and `(3)` produce an exact tested D2 sample
below that bound, contradiction. This proves `(1)` and `(2)`.

## Strongest positive survivor and route impact

- **Exact killing mechanism:** Any false-RH zero destroys a claimed lower bound on one rational
  window at a cofinally selected exact natural aperture, already on a Gaussian-rational D2 sample.
- **Strongest positive survivor:** Exact rational D2 coordinate rotation `(3)`, continuity of the
  literal weighted prime source at regular points, rational strict-sublevel transfer, and the
  countable exact criteria `(1)--(2)`.
- **New insight:** Countable point centers are insufficient, but countable compact windows plus
  dense rational samples lose no zero-detection power. Loop93's continuous local criterion can be
  arithmetized without Gamma completion, complex sample parameters, or approximate coordinates.
- **Remaining burden:** Prove the eventual rational-window lower-bound predicate in `(1)` from
  unconditional prime arithmetic. This is now a countably sampled, direct-prime endpoint.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/XiPhysicalPrimeApertureThetaAbelEnergyPrimeD2GaussianRatWindowCriterion.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct source check: PASS
- Targeted build: PASS (`12923/12923`)
- Axiom audit: `[propext, Classical.choice, Quot.sound]`
- Principal declarations:
  `primeFluxContourCoordinate_centeredGaussianRatToPrimeFluxIndex`,
  `continuousAt_xiPhysicalThetaAbelEnergyPrimeWeightedSource_of_XiC_ne_zero`,
  `exists_gaussianRatPoint_mem_ratRectangle_primeWeightedSource_re_lt`,
  `xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsBoundedBelow_iff_riemannHypothesis`,
  `xiPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow_iff_riemannHypothesis`,
  `unitPhysicalThetaAbelEnergyPrimeD2GaussianRatWindowsEventuallyBoundedBelow_iff_riemannHypothesis`.
- Formal lint: new wired module clean; repository-wide lint remains blocked only by unrelated
  unwired dirty-tree modules.

## Novelty audit

Targeted corpus searches found a rational-window basis for divisor mass, Gaussian-rational
completed-source criteria, compact complex-box infrastructure, and Loop93's arbitrary-complex
local direct-prime detector. No corpus theorem combined literal direct-prime weighting, exact
natural apertures, rational compact windows, and original-coordinate Gaussian-rational D2 samples.

Primary-literature searches through 2026-08-28 found compact-window Weil positivity, continuous
screw/operator formulations, numerical Archimedean spectral laws, and finite-core Volterra/Weyl
reductions. None states `(1)--(3)` or this countable direct-prime D2 equivalence. Candidate-new
content is restricted to the exact route-specific synthesis proved here.

Primary comparison points:

- M. Chuk, [*Weil positivity in compact windows: certified two-sided bounds and a Landau--Widom
  decay law*](https://arxiv.org/abs/2608.24827).
- M. Suzuki, [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096).
- T. Kim et al., [*A Numerical Realization of Suzuki's Weil-Quadratic-Form Operator*](https://arxiv.org/abs/2607.24830).
- M. B. Freedman, [*Finite-core Volterra reductions for a Weyl-positive Riemann phase kernel*](https://arxiv.org/abs/2606.29555).

## Log

- 2026-08-28 — Mandatory corpus search identified rational compact windows as necessary to remove
  the irrational-center blind spot.
- 2026-08-28 — Proved exact Gaussian-rational D2 coordinate rotation, compact rational envelope,
  admissible-window selector, and regular-point continuity.
- 2026-08-28 — Proved strict-sublevel transfer to exact Gaussian-rational samples.
- 2026-08-28 — Proved all-aperture and eventual countable D2 window criteria equivalent to RH.
- 2026-08-28 — Direct source check, targeted `12923/12923` build, standard axiom audit, umbrella
  wiring, and local lint audit passed.
