# CCM critical-Mellin aperture-resolvent law — formalization certificate

- **Stage:** 3 — core formalized in Lean 4
- **Paper theorem:**
  `../../2-fully-proven/new_scientific_knowledge/ccm-critical-mellin-aperture-resolvent-law.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/CCMCriticalMellinApertureResolvent.lean`
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
- `integral_criticalMellinApertureCausalKernel`: exact primitive of the averaged causal kernel;
- `criticalMellinApertureCausalKernel_volterra_collapse`: pointwise cancellation of Volterra
  memory to the unit exponential resolvent kernel.

## Boundary

Module proves filter, omitted-tail, and causal-kernel identities.  It does not assert a sector
condition for the actual Chebyshev source, one-sided Riesz bound, Weil positivity, or RH.  The
paper corollary that the specialized admissible-width tail tends to zero is not yet a Lean theorem.

## Verification

- `lake env lean GaloisForLFunctions/RHTower/CCMCriticalMellinApertureResolvent.lean`: passes.
- `lake build GaloisForLFunctions.RHTower.CCMCriticalMellinApertureResolvent`: passes,
  3553/3553 jobs.
- `#print axioms` for all eight theorem endpoints reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden-declaration scan of module is empty.
- Repository-wide formal lint reports only unrelated unreachable concurrent modules; it reports no
  defect in this module, which is imported by both RHTower umbrellas.
