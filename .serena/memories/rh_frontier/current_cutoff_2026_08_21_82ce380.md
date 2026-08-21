# RH frontier map snapshot — 2026-08-21

Authoritative document: `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`.

Evidence cutoff: committed Lean at `82ce380a1ece28cd48adc86b7694cc7abf6a3373`, plus explicitly marked current working-tree declarations. Lean-source search only; cards/papers not evidence. Documentation-only audit: no builds.

Counts: 18 live architectures; 13 candidates; 3982 lines (4000-line cap).

Main frontier shifts:
- O/CCM: source-self-polarized complex Dirac determinant has exact strict off-center sign. `CCMActualHeadMatchedPhaseProjectiveGaugeLinearReadoutNoGo.lean` proves projective gauge square-summable, reciprocal not square-summable, inverse-gauge cost divergent, and no square-summable exact linearizer. First open theorem is nonlinear/projective or singular coefficient-faithful landing into linear actual-head restricted-Weil floor; bounded L2 inverse-gauge landing is dead.
- HC: committed frequency reindex and exact zero/nonzero split. Working-tree `ChenGuptaLiLemma45DiagonalPoisson.lean` isolates all-equal row contribution as row count times explicit Poisson mass cubed, but is not build-audited. Remaining: off-diagonal zero-frequency term, conductor/height-uniform nonzero-frequency cancellation, height aggregation.
- T2: committed fixed-width tail monotonicity and canonical cutoff. Working-tree canonical packet and rung uniformization produce a fixed-width packet and finite rung union, not build-audited. Remaining: adaptive threshold, both Maynard two-alternative premises, weighted shell summation; signed/renormalized subhalf continuation remains separate. Existing 11/5 exclusion chain syntax defect must not receive proof credit.
- C1: Connes flow trace and local division-distribution laws committed. Local scaffold improved; global signed/non-dominating correction excluding two-pole escape remains open.
- SV2: deficiency kernel, inverse Neumann, Fourier decay committed. `SuzukiCutoffLogWindow.lean` proves logarithmic tail primitives; working-tree assembled cutoff bound not build-audited. Global projective target identification and reciprocal pole chart remain open.
- ABHN: local residue extensions/Frobenius strengthened, still no local reciprocity/global ABHN/Xi landing; pre-route.
- Generic Haferkamp, Wick/Pfaffian, Belinski-Zakharov additions remain source-independent and add no RH route.

No new independent route or candidate: O complex Dirac remains O because source and RH endpoint are unchanged; HC/T2/SV2 additions are connectors.
