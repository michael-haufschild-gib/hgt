# CLG/TTF global modular energy and compact compensation

- **Stage:** 3-formalized
- **Scope:** Global bounds for the literal modular source orbit and `H_C≥10¹⁴M⁶>0` on `[0,8/95]` for every `C≥10⁹`.
- **Full chain:** Literal theta source → all signed center-mixed jet Hankel sections nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.
- **Remaining:** The fixed compact interval `(8/95,7/16)`, then the all-order hierarchy. Global mixed rank-six positivity and RH remain unproved.

## Exact source and global barrier

Write `u=−Re(thetaCuspModularDrift)`, `a=thetaCuspModularGapAmplitude>0`, `w=thetaCuspModularTransverseShear`, and `M=completedThetaProfile>0`. The corpus proves the following equations on the actual complete real orbit:

`u′=−3+u²/3+3a/4`, `a′=−2aw`, `w′=2+a/2+2u²/9+2uw/3`.

At zero, `u=w=0` and `a(0)=thetaCuspSelfDualModularScale²`. The existing theta-series enclosure gives

`191/10<a(0)<360000/18769<96/5`.

On the nonnegative half-line, `u,w≥0`. Define

`f(x)=exp(−2x)(1−u(x)/3)`.

Its exact derivative is

`f′=−exp(−2x)[(1−u/3)²+a/4]`.

Since `0<exp(−2x)≤1`, this implies `f′<−f²` on the positive ray. The corpus theorem `pos_of_deriv_lt_neg_sq_on_Ioi` proves that a differentiable function satisfying this strict contraction on a complete ray stays positive: a nonpositive value would force its negative reciprocal to reach zero in finite time. Applying it to the literal orbit proves

`0≤u(x)<3` for every `x≥0`.

This uses global existence already proved for the source; no terminal estimate, numerical trajectory, or zero-location premise is supplied.

## Two decreasing energies

The exact shear-gap identity is

`(w−2u/3−4x)′=2uw/3≥0`.

Hence `w≥2u/3+4x`. The first energy `E₁=a+4u²/9` satisfies

`E₁′=−2a(w−u/3)−(8u/27)(9−u²)≤0`.

Therefore `E₁≤a(0)<96/5`, and the Riccati equation gives `u′<57/5`. Integration from zero yields `u≤57x/5`. Combining this with the shear-gap inequality proves `w≥u` globally.

The stronger energy `E₂=a+4u²/3` then satisfies

`E₂′=−2a(w−u)−(8u/9)(9−u²)≤0`.

Thus `E₂≤a(0)<96/5` on the entire nonnegative half-line. Completing one square in the shear equation gives

`w′<58/5+w²/4`,

because the omitted term is `−(2u/3−w/2)²`. These are global source bounds, independent of the later compact determinant certificate.

## Actual compact orbit tube

On `[0,8/95]`, a first-contact argument against `w=(95/8)x` has `w≤1` at contact and therefore

`w′<58/5+1/4=237/20<95/8`.

Consequently `w≤95x/8`. Since `a<96/5`, the exact gap equation gives `a′≥−456x`, hence

`a(x)≥a(0)−228x²≥17`.

Together with the global tangent bound this proves `0≤u,w≤1`, `17≤a≤20` throughout the interval. The same tube gives `u′≥39/4`, so `u≥39x/4`. The two linear bounds retain the relative inequality `w≤5u/4`.

Every bound is for the complete source, derived by differential comparison from its exact initial value.

## Retaining favorable slope terms

The previously proved literal source coordinates are

`Φ=M Q`, `Φ′=M P`,

`Q=u²/24+a/16−3/8`,

`P=5u³/144+7ua/96−5u/16−aw/8`.

Let `L=aw/8+5u/16≥0`. On the actual tube, `w≤5u/4` and `a≥17` imply

`P+(2/3)L≥5u³/144+u(a−5)/48≥0`.

Since `(4/3)x≤137/1000` on `[0,8/95]`, this preserves the existing compact comparison exactly:

`G/M²=3Q²+2xQP≥3Q²−(137/1000)QL=oddCompactLowerSource(u,a,w)≥1`.

The final lower bound follows from `Q≥11/16` and `3Q−(137/1000)L≥3/2` on the coordinate box.

## Full determinant transfer

The existing exact polynomial certificate proves, throughout that box,

`oddCompactDet+10⁹ oddCompactHead·oddCompactLowerSource≥10¹⁴`.

The literal identities `H=M⁶ oddCompactDet` and `Δ=M⁴ oddCompactHead>0` therefore give

`H+10⁹ΔG≥10¹⁴M⁶`.

Because `G≥M²>0`, this holds for every `C≥10⁹` in place of `10⁹`. In particular it holds for the source-selected canonical coefficient `10⁹<K_*<3·10⁹`.

Combining with the [scale-seven tail](clg-ttf-scale-seven-compensated-tail.md), canonical positivity is proved on

`[0,8/95] ∪ [7/16,∞)`.

For every positive aperture, the corrected weighted determinant is positive on `0<r≤16/95` and on `r≥7/8`. Its tenth integrated entry remains unchanged by the already proved zero-integral correction. The intervening compact comparison is still required before the global mixed odd rank-three receiver applies.

## Lean coverage and audit

Four new modules in `GaloisForLFunctions/RHTower` contain 24 public declarations:

- `ThetaCuspModularGlobalDriftBarrier`: complete-ray barrier `0≤u<3`.
- `ThetaCuspModularEnergyBounds`: both energy comparisons, global tangent and shear bounds.
- `ThetaCuspModularEnergyTube`: the actual enlarged interval and relative shear estimate.
- `ThetaCuspOddEnergyCompensation`: literal correction reserve, determinant margin, canonical gap complement, and weighted transfer.

Each module was checked in scratch with `lake env lean`; identical checked source and the required olean were retained. All four are imported by the RHTower umbrella; no umbrella build was run. A scratch audit of the five new capstones reports only `propext`, `Classical.choice`, and `Quot.sound`. Formal lint passed. No added axiom, numerical source premise, or computational certificate is used. The determinant polynomial certificate was reused without expansion or rebuilding.
