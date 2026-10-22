# Hedenmalm--theta Möbius prime-cell Gamma-window provenance

- **ID:** P-G50
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + LEAN FORMALIZATION IN PROGRESS
- **Source:** P-G49 forced Gamma rapidity; actual Burnol co-Poisson exponential-window source
- **Statement:** Twice the P-G49 rapidity is length of a literal Burnol co-Poisson window whose lower endpoint is an exact rational function of running Euler odds and thermal ratio.

## Goal

Decide whether P-G49 Gamma characteristic is a post hoc receiver or arises from an actual corpus
source.  Required certificate must construct literal source seed and invoke existing Mellin
evaluation, not merely rename a real number.

## Gates

- [x] 0 → 1 in-progress: exact aperture/length law and literal Mellin source realization
- [ ] 1 → 2 fully-proven: finalize after Lean source check
- [ ] 2 → 3 formalized: module, umbrella, build, lint, axiom audit green
- [ ] 3 → 4 publication-ready: standalone exposition and external novelty audit

## P-G50 source window `[PROVED HERE]`

For running odds `a=qe^{-k}` and thermal ratio `T>1`, let

\[
 C=\frac{T-1}{T+a},\qquad
 L=2\operatorname{artanh}C.
\tag{1}
\]

P-G49 proves `0<C<1`, hence `L>0`.  Direct Cayley algebra gives

\[
 \boxed{
 e^{-L}=\frac{1-C}{1+C}
       =\frac{1+a}{2T+a-1}\in(0,1).
 }
\tag{P-G50}
\]

Therefore `[e^{-L},1]` is a literal logarithmic Burnol subwindow.  Existing corpus Mellin theorem
applies without new analytic hypotheses:

\[
 \int_0^\infty
   \operatorname{coPois}(1_{[e^{-L},1]})(t)t^{-w}\,dt
 =\operatorname{BurnolWindowZetaGerm}(L,w),
 \qquad 0<\Re w<1.
\tag{2}
\]

Since P-G49 Gamma characteristic is evaluated at `L/2`, nonlinear clock is canonical half-density
clock of this actual source window.

## Conjecture loop verdict

### Conjecture P-G50.A

P-G49 Gamma complement may be formal receiver with no source provenance.

**Killed.** `(P-G50)` constructs exact co-Poisson window and existing theorem gives its literal
Mellin evaluation.  No Xi zero or fibre-selected parameter is used; `L` is determined by source
Euler cell.

### Surviving obstruction

Source provenance does not imply saturation.  Actual primitive, Julia, and Gamma-window channels
obey conservative P-G49 budget.  A new law must annihilate or polarize one positive channel; merely
constructing all three is now exhausted.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  HedenmalmThetaMobiusPoleUnitPrimeCellGammaWindowProvenance.lean
```

Key declarations:

- `thermalBernoulliGammaWindowLength_pos`;
- `thermalBernoulliGammaWindowAperture_mem_Ioo`;
- `exp_neg_thermalBernoulliGammaWindowLength_eq_aperture`;
- `integral_Ioi_burnolCoPoisson_thermalBernoulliGammaWindow`;
- `thermalBernoulliGammaWindowAperture_eq_exp_neg`.

## Next hard gate

Use full alternating prime-power current of squarefree reporter.  Grade-one charge is no longer
the obstacle; determine exact higher-depth correction to P-G49 budget and whether it creates a
second signed identity or another positive conserved complement.

## Log

- 2026-08-12 — derived exact forced Burnol window endpoint and proved literal co-Poisson Mellin
  realization; P-G49 clock provenance closed, saturation still open.
