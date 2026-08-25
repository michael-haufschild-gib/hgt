# Irregular Stokes cubic local ramification capacity (2026-08-25)

## Result

Formalized a pointwise ramification-capacity obstruction for every coefficient-generated irregular-microlocal/Stokes landing of the first negative cubic wall–Xi Malgrange residual.

For any nonnegative multi-Rees parameter, cubic landing `x`, and marked point `a`:
[
1 < -\mathrm{globalRankCoefficient}(g,d)\sum_i \mathrm{ramification}_a(i)^2.
]

This is stronger than the earlier raw-Euler candidate: no raw-source incidence is needed. On a genus-zero one-puncture model:
[
1 + \left(\sum_i e_i^2\right)^{-1} < \frac{K(0)+1}{N(0)}.
]
It strictly strengthens the previously formalized slope (>1) by a positive data-dependent gap.

## Mechanism

Let (P) be global Rees-positive energy, (T_a=\sum_i x_a(i)^2), (M_a=\sum_i e_a(i)^2), (r) common rank, (c) global rank coefficient.

- Cubic landing gives (P<(-c)r^2), (P>0), and (-c>0).
- Compatibility plus orbit descent gives (r=\sum_i x_a(i)e_a(i)).
- Finite Cauchy–Schwarz gives (r^2\le T_aM_a).
- Nonnegative local Rees blocks and other local energies give (T_a\le P).
- Therefore (P<(-c)PM_a), hence (1<(-c)M_a).

## Files

- Lean: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesCubicLocalRamificationCapacity.lean`
- Card: `docs/drafts/pipeline/3-formalized/route-p-cubic-local-ramification-capacity.md`
- Umbrella import: `formal/GaloisForLFunctions/RHTower.lean`
- Frontier map remained untouched/read-only.

## Verification

Targeted module check passed. Axiom audit for both public declarations returned exactly `[propext, Classical.choice, Quot.sound]`. Temporary scratch and generated dependency/module `.olean` files were removed.

## Novelty/audit

Corpus had component laws but no pointwise completed-Xi ramification-capacity theorem. Focused primary-literature audit of irregular RH, wild harmonic bundles/twistor D-modules, irregular holonomic D-modules, and Hurwitz irregular RH found no exact completed-Xi capacity law. Absence is an audit inference, not a priority claim.

Related memories: `mem:research/irregular_stokes_cubic_microlocal_witt_signature_2026_08_25`, `mem:research/irregular_stokes_cubic_diagonal_rees_transversality_2026_08_25`.

## Next scientific target

Use this local capacity inequality to classify/exclude low-ramification global landing types or combine it with a genuine source-to-Stokes incidence law. Avoid returning to the fixed-charge two-scale Rees subtype: diagonal transversality proved it empty, making its terminal-energy consequences vacuous.
