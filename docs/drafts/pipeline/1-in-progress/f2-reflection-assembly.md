# F2 — reflection assembly

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Goal:** Assemble PM, CWS and WTZ through an arithmetic Hecke action carrying the complete window form; prove its missing positivity without assuming RH.

## Established inputs

- `MayerWindowFoldTransfer`: logarithmic norm/inner-product transport; inversion becomes a twisted reflection; window lifts have an explicit negative Frobenius-square defect and two-sided fold bounds. Source present, dependency/final audit pending.
- `FareyLewisTransferAndCuspSeparation`: four-branch `lewisHeckeT2` commutes with inversion and intertwines the Farey defect. Source present, dependency/final audit pending.
- `TheSymmetriesOfTheTower`: Serre reflection conjugates truncated Dirichlet shifts to their adjoints.

## Missing bridges

1. Transport the four Hecke branches through the logarithmic transform, including their support and cusp terms. The two nonlinear branches sample `(a+1)/2` and `2a/(a+1)`; neither is a logarithmic translation.
2. Identify the resulting action on complete Weil energy, including archimedean and polar terms. Norm transport and fold bounds alone do not identify quadratic forms.
3. Establish arithmetic positivity on finite-cusp-energy resonances, or an exact positive realization of the complete window form. This remains the RH-strength input.

## Hecke support law — paper proof; Lean audit pending

For `f(x)=0` on `x>R`, `R≥0`, and `a>2R`, the first three Hecke branches vanish, giving

`(a+1)^(2s) T₂f(a) = f(2a/(a+1))`.

The increasing fractional-linear map `a↦2a/(a+1)` bijects an upper tail onto a left neighborhood of `2`; its inverse is `x↦x/(2−x)`. Therefore `T₂f` has an upper cutoff iff `f` vanishes on a left germ at `2`. This is an exact classification, not merely an asymptotic necessary condition.

For `f=windowPeriodLift s H`, the positive normalization gives `f(x)=0 ↔ H(−log x)=0` for `x>1`. Inversion fixes the Hecke image and exchanges its upper and lower tails. Hence the image lies in some finite multiplicative window iff `H` vanishes on a right germ at `−log 2`. Every window with `A<log 2` qualifies. At and beyond the first prime, endpoint value alone does not suffice.

**Consequence:** the direct finite-window Hecke endomorphism conjecture requires a germ restriction. The positive survivor is the exact cusp-channel recovery and finite-support classification. Keep the full channel in subsequent energy transport; do not project it away.

**Next conjecture:** a reflection-compatible compression has an exact Weil-energy boundary correction expressible through this recovered germ. Its sign must be proved jointly with the interior energy.

**Source:** `RenormalizedIntersectionTheory/MayerScattering/HeckeWindowCuspTransport.lean` (unverified).

## Completion gates

- [ ] Exact Hecke transport and sharp support/cusp law, paper proof and Lean.
- [ ] WTZ correspondence identification with complete Weil-form identity.
- [ ] Missing positivity proved; no assumed sign or resonance admission.
- [ ] Individual final Lean audits, standard-only transitive axioms, umbrella imports.
