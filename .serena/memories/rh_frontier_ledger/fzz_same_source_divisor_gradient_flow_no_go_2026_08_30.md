# FZZ-P same-source divisor gradient-flow no-go (2026-08-30)

Formalized Stage-3 route kill in `formal/GaloisForLFunctions/RHTower/FZZCigarParitySameSourceDivisorGradientFlowNoGo.lean`; card `docs/drafts/pipeline/3-formalized/fzz-p-same-source-divisor-gradient-flow-no-go.md`.

Capstone: `RHTower.fzzCigarParity_sameSourceDivisorGradientFlow_noGo`.

Content:
- Any continuous family from any preconnected parameter space into the open-strip divisor of the unchanged literal FZZ parity Mellin source is constant. Proof lifts through `fzzCigarParityMellin_eq_zero_iff_xi_eq_zero` to the discrete Xi-zero subtype (`xi` entire, `xi 0 = 1/2`).
- Same-source reflected-Fermi horizontal gradient trajectory through an open-strip mode exists iff `rho.re = 1/2`.
- Universal trajectory realizability iff RH.
- Positive survivor: every nonconstant continuous open-strip path leaves the fixed FZZ divisor, so viable continuous zero motion must deform the source/function family.

Proof chain killed: literal FZZ source -> continuous transport inside same divisor -> reflected-Fermi inward gradient -> stationarity/completeness -> RH.

Verification: direct `lake env lean` PASS; targeted module `lake build` PASS; axioms only `propext`, `Classical.choice`, `Quot.sound`; corpus research index finds declarations. Umbrella import added to `RHTower.lean`. Global lint only reports unrelated `HTGeometry.RittFirstJetAffineDescent` reachability debt. No own stale Lean process.

Literature audit: Pakman hep-th/0606067 (classical scattering does not uniquely fix quantum reflection coefficient); Hikida-Schomerus 0805.3931 (FZZ duality proof); de Bruijn-Newman evolution 1904.12438 changes entire function `H_t`, consistent with source-deformation survivor. No audited fixed-source divisor transport/RH theorem through 2026-08-30.