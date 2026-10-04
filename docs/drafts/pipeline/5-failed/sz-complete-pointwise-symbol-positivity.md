# SZ: eventual pointwise positivity of the complete Fourier symbol

- **ID:** sz-complete-pointwise-symbol-positivity
- **Stage:** 5-failed
- **Type:** FALSIFIED (Lean)
- **Route:** SZ, canonical-head joint Gamma–prime–polar sign
- **Candidate:** The complete corrected symbol has a uniform lower bound on all sufficiently large apertures and all real frequencies; in particular, eventual pointwise nonnegativity might imply the required supported quadratic positivity.

## Exact obstruction

`RHTower.correctedCCMSymbol_zero_two_signed_windows` proves, for every real B and L, both a positive-length aperture interval after max(L,1) where correctedCCMSymbol(a,0)>B and another where correctedCCMSymbol(a,0)<-B. This contradicts every eventual constant pointwise floor, already at zero frequency. The theorem concerns the full Gamma–polar–prime symbol, with the archimedean constant and all admitted prime powers retained.

## Positive survivor and new insight

The substantive source theorem is `RHTower.criticalMellinCompletedError_two_signed_windows`: the literal completed arithmetic current has arbitrarily late closed intervals beyond each signed level. Prior absolute escape did not choose either sign. The proof adds the exact right derivative at every positive point, including prime seams, and transports both orientations of the actual logarithmic cusp by Bohr recurrence. Assuming a one-sided bound first forces RH internally through Landau, so the final two-sided source theorem has no RH or ordinate-independence premise.

This distinguishes oscillation of the complete source from positivity of its quadratic form on physically supported vectors. Negative symbol values do not supply a negative canonical-head energy. A successful producer must use correlations imposed by support and the full coherent Gamma–prime–polar pairing. Depth alone supplies neither an integrated signed-work bound nor the required phase credit.

## Proof and audit status

Dependency-closed paper proof and complete source/audit record: [signed-current theorem card](../3-formalized/sz-screw-cusp-signed-current.md). Lean module: `formal/GaloisForLFunctions/RHTower/SuzukiCompletedCurrentSignedWindows.lean`. Scratch2938 and final direct leaf60657 passed; new module wired once without an umbrella build. Public axiom audit53591 passed for all three declarations with only propext, Classical.choice and Quot.sound. Global lint49877 has21 unrelated unreachable modules and no new-leaf error. No RH proof or falsification is claimed.
