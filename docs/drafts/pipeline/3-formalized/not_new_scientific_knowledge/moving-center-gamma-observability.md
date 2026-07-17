# Moving-center Gamma clocks retain orientation after unit-intensity collapse

- **ID:** `moving-center-gamma-observability`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Sources:** K. K. Ng, C. Zhang, J. Louko, and R. B. Mann, *A Little Excitement Across the Horizon*, arXiv:2109.13260, Appendix B; J. Huang and T. W. Ng, *Hypertranscendency of Perturbations of Hypertranscendental Functions*, arXiv:2007.10037; L. Di Vizio and F. Pellarin, *The Carlitz module and a differential Ax--Lindemann--Weierstrass theorem for the Euler gamma function*, arXiv:2508.21237v2
- **Statement:** For every even frequency-dependent Gamma center, frequency reflection makes the carrier reciprocal, its reflected-frequency intensity unit, and its orientation observation the carrier square wherever the two Gamma values are nonzero.  This applies exactly to the algebraically moving angular center in the Schwarzschild detector Coulomb-wave estimate.

## Goal

Test whether the phase--intensity selector is an artifact of affine fixed-center Gamma clocks.  The
black-hole detector formula supplies a harder case in which the center itself moves algebraically
with frequency through a square root.

## Gates

- [x] 0 → 1 in-progress: exact black-hole Coulomb phase and moving angular center extracted
- [x] 1 → 2 fully-proven: even-center reflection algebra proved without an affine-center assumption
- [x] 2 → 3 formalized: exact target, direct file check, axiom audit, and source scan pass
- [ ] 3 → 4 publication-ready: not a standalone publication target

## Source relation

Ng--Zhang--Louko--Mann Appendix B uses the Coulomb phase

`sigma_nu(eta) = -(i/2) log [Gamma(nu+1+i eta)/Gamma(nu+1-i eta)]`

with `eta=-2 M omega` and

`nu_a(omega)=(-1+sqrt((2 ell+1)^2-12(2 M omega)^2))/2`.

The center `nu_a` is even in `omega`, but is not an affine constant shift.  Lean formalizes this
exact algebraic center and the Gamma ratio used inside the logarithm.  The theorems are stated away
from Gamma poles because `Complex.Gamma` is the actual-value function rather than a meromorphic
field element.

## Exact positive statement

For any even center `c(-omega)=c(omega)`, write

`A(omega)=Gamma(c(omega)+i q omega)/Gamma(c(omega)-i q omega)`.

Then, wherever both Gamma values are nonzero,

`A(-omega)=A(omega)^(-1)`,

`A(omega) A(-omega)=1`,

and

`A(omega)/A(-omega)=A(omega)^2`.

The Schwarzschild square-root center is proved even, so all three relations apply.  Thus complete
reflected-frequency intensity remains blind even after the clock center moves with frequency;
orientation still retains the full carrier square.

## Expansion beyond the current HT field

The fixed-shift meromorphic Gamma orbit classifier does not represent `Gamma(c(omega)+i q omega)`
when `c` is nonconstant.  The missing theorem is therefore precise: hypertranscendence transport
for Gamma carriers under non-affine algebraic pullback, naturally formulated on a branched
algebroid cover.

Huang--Ng prove HT of `f ∘ g` for nonconstant entire `g`, which does not cover the square-root
branch.  Di Vizio--Pellarin prove differential independence for Gamma values with algebraically
moving shifts over a periodic-meromorphic base, but their hypotheses do not directly identify the
Schwarzschild frequency pullback.  These results make the new target plausible without licensing
an unconditional HT claim here.

## Corpus value

This separates two layers that were previously conflated:

1. reflection observability only needs parity of the center and already extends beyond affine
   clocks;
2. differential classification needs a new algebraic-pullback theorem.

The first layer is now reusable and unconditional.  The second is an explicit research route that
would enlarge HTGeometry from affine meromorphic clocks to algebroid clock coordinates used in
black-hole perturbation theory, gravitational waves, and other connection problems.

## Lean certificate

Module: `GaloisForLFunctions.HTGeometry.MovingCenterGammaObservability`

- `movingCenterGammaCarrierValue_neg`
- `movingCenterGammaIntensityValue_eq_one`
- `movingCenterGammaOrientationValue_eq_square`
- `schwarzschildDetectorRenormalizedAngularCenter_neg`
- `schwarzschildDetectorCoulombGammaIntensityValue_eq_one`
- `schwarzschildDetectorCoulombGammaOrientationValue_eq_square`

The exact missing module target and direct source check pass.  Every audited capstone depends only
on `propext`, `Classical.choice`, and `Quot.sound`; the source scan is clean.  No full build or
global lint was run.

## RH pressure test

For RH searches, the immediate result is again a route selector: unit modulus or reflected
intensity can erase an archimedean Gamma carrier even when its center depends nonlinearly on the
spectral parameter.  The larger opportunity is the missing algebraic-pullback theorem, which would
permit nonlinear spectral coordinates in Gamma-clock constructions.  Neither statement supplies
prime coupling, positivity, or off-critical-zero exclusion.

## Log

- 2026-07-17 — exact Schwarzschild detector formula located; arbitrary even-center reflection,
  intensity collapse, orientation-square relation, and square-root-center specialization proved.
- 2026-07-17 — promoted after serialized exact-target build, direct verification, standard-only
  axiom audit, and source scan.
