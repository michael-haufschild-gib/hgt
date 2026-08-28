# HC88 phase-sensitive reflected-pair coherent-cancellation no-go (2026-08-28)

Formal module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhaseSensitiveReflectedPairCancellationNoGo`.
Card: `docs/drafts/pipeline/3-formalized/hb-phase-sensitive-reflected-pair-coherent-cancellation-no-go.md`.

New results: the calibrated actual BM chiral Ward coordinate is exactly odd under Xi functional-equation reflection. For arbitrary complex weights, raw physical seed, and copy q, the reflected-pair coherent return factors exactly as `(a M(q) - b M(Rq)) D(q)`. Off critical line, cancellation iff `a M(q)=b M(Rq)`. Choosing cross-weights `(M(Rq),M(q))` cancels identically. For every nonzero seed and off-line q, both cross-weights and both actual nonlinear BM raw channels are nonzero while coherent return is zero. Closed universal canonical-seed theorem included.

Route impact: reflected-pair/global phase-sensitive Ward conservation is not RH-bearing; functional-equation charge conjugation cancels two bright channels. Only copywise darkness or a source-native fixed-weight/no-cross-weight theorem survives across HB/FZZ-P/PW-B/RBH.

Audit: direct Lean passed; targeted build passed 12,004/12,004; representative axioms only `propext`, `Classical.choice`, `Quot.sound`; lint had only pre-existing unreachable modules and no HC88 finding. Umbrella import wired. Frontier map remained read-only.

Next hardest audit: determine whether literal source-FE cocycle fixes the reflected channel ratio and whether it equals the HC88 cancelling ratio. If yes, fixed source transport also fails; if no, isolate exact mismatch as surviving local producer.