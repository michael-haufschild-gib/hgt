# CCM unit-Riesz Möbius renewal law

- **ID:** `ccm-unit-riesz-mobius-renewal-law`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM, finite source core
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT RH]`
- **Paper parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/ccm-unit-riesz-mobius-wavelet-reduction.md`

## Formal theorem surface

Module:

`GaloisForLFunctions/RHTower/CCMCriticalMellinRieszMobiusRenewal.lean`

It proves unconditionally:

1. real part of the formalized unit-aperture Volterra primitive equals
   `2(exp(-x/2)-exp(-x))`;
2. critical normalization at `x=log(X/n)` is exactly
   `2/sqrt(X)*(1-sqrt(n/X))`;
3. complete Möbius--log future dressing equals the negative unit-Riesz von-Mangoldt renewal;
4. every atom of the collapsed renewal is nonnegative on physical support.

Principal declarations:

- `re_integral_criticalMellinApertureCausalKernel_eq_unitApertureRieszProfile`;
- `unitApertureCriticalPrimeWeight_eq_riesz`;
- `unitRieszMobiusFutureDressing_eq_neg_vonMangoldtRenewal`;
- `unitRieszVonMangoldtRenewal_atom_nonneg`.

The analytic Stieltjes wavelet reduction and its open half-unit coefficient bound are not claimed
formalized.  Formalized finite core certifies exact arithmetic resonance and the no-hidden-
probability-collapse conclusion used by the paper theorem.

## Gates

- [x] exact unit-rate profile
- [x] exact Riesz normalization
- [x] exact all-grade Möbius collapse
- [x] physical-support positivity
- [x] owned module check
- [ ] formalize critical boundary/Stieltjes wavelet after reusable API exists
- [ ] prove open coefficient bound
- [ ] RH
