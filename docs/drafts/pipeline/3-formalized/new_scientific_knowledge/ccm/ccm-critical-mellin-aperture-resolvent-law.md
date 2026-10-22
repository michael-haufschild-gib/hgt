# CCM critical-Mellin aperture-resolvent law — formalization certificate

- **Stage:** 3 — core formalized in Lean 4
- **Paper theorem:**
  `../../2-fully-proven/new_scientific_knowledge/other/ccm-critical-mellin-aperture-resolvent-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/CCM/CCMCriticalMellinApertureResolvent.lean`
- **Umbrella imports:** `formal/GaloisForLFunctions/RHTower.lean` and
  `formal/GaloisForLFunctions/RHTower/RiemannHypothesisSOTA2026.lean`
- **RH used:** no
- **Computation used:** no

## Formal theorem surface

Lean proves unconditionally:

- `criticalMellinApertureAveragedMultiplier_eq`: general rate-`a` rational transfer law;
- `criticalMellinApertureAveragedMultiplier_one_eq`: unit-rate collapse to `-1/(w+1)`;
- `re_criticalMellinApertureAveragedMultiplier_one_neg`: strict negative real part on `Re(w)>0`;
- `criticalMellinApertureAveragedModeResponse_eq`: exact response of every positive-growth mode;
- `criticalMellinApertureAveragedMultiplierTail_eq`: exact omitted-aperture multiplier from any
  cutoff onward;
- `criticalMellinApertureAveragedModeResponseTail_eq`: exact omitted mode response from any cutoff;
- `criticalMellinApertureAdmissibleModeResponseTail_eq`: exact specialized admissible-width tail;
- `criticalMellinApertureAdmissibleModeResponseTail_tendsto_zero`: unconditional decay for
  `0 < Re(w) < 1/2`;
- `integral_criticalMellinApertureCausalKernel`: exact primitive of the averaged causal kernel;
- `criticalMellinApertureCausalKernel_volterra_collapse`: pointwise cancellation of Volterra
  memory to the unit exponential resolvent kernel;
- `criticalMellinChebyshevError_eq_exp`: exact logarithmic-coordinate source identity;
- `criticalMellinChebyshevResolventSource_log_eq`: exact Chebyshev resolvent source change of
  variables.

## Boundary

Module proves filter, omitted-tail, specialized tail decay, causal-kernel identities, and exact
Chebyshev source transport.  It does not assert a sector condition for the actual Chebyshev source,
one-sided Riesz bound, Weil positivity, or RH.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/CCM/CCMCriticalMellinApertureResolvent.lean`: passes.
- `lake build GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinApertureResolvent`: passes,
  3553/3553 jobs.
- `lake build GaloisForLFunctions.RHTower`: passes.
- Combined `#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan of module is empty.
- Module is reachable from both RHTower umbrellas.
