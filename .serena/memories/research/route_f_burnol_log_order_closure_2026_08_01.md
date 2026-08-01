# Route F Burnol logarithmic-order closure (2026-08-01)

Current Route F was retired after proving exact order mismatch on canonical Sonin packets.

Paper/formal result: for every fixed annulus `0<b<c`, geometric tower `a₀>0, r₀>1`, and arbitrary finite height `n`, full concrete Burnol log-shell conductor quadratic form on `soninPacketEven b c ... (2*pi*A)` is at most `C₀+C₁*log A`, uniformly for `A>=1`. Combining with existing explicit positive-linear successive-layer coupling schedule proves completed packet values unbounded below for every height function.

Load-bearing Lean modules:
- `RHTower/SoninPacketHighTailPolynomial.lean`: uniform spectral density O(|xi|^-12), cutoff energy O(t^-11).
- `RHTower/SoninChannelMovingThreshold.lean`: height-uniform moving real threshold shell bound (avoids carrier-to-shell rounding).
- `RHTower/SoninBurnolFrequencyLogOrder.lean`: full conductor affine-log packet form.
- `RHTower/SoninBurnolFrequencyLogarithmicOrderNoGo.lean`: exact arbitrary-height no-floor theorem `not_bddBelow_soninCompletedPacketValueVar_soninBurnolLogShellConductorFamily`.

Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Final module build passed. Source modules contain no forbidden declarations.

Research records:
- formalized theorem card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/sonin-burnol-frequency-logarithmic-order-no-go.md`
- failed route card: `docs/drafts/pipeline/5-failed/route-f-all-prime-sonin-transfer.md`
- positive survivor backlog: `docs/drafts/pipeline/0-backlog/sonin-order-one-arithmetic-source-or-weyl-renormalization.md`

Scope boundary: theorem closes full geometric Burnol log-shell model, not every logically imaginable operator. No concrete source-faithful producer remains. Reopening requires a new arithmetic microlocal-order-one source or exact pre-conductor cancellation of Sonin Weyl-volume term; abstract postulated linear scalars are theatre.