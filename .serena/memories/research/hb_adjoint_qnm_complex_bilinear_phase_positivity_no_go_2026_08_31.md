# HB adjoint-QNM complex-bilinear phase/positivity no-go (2026-08-31)

Qualifying route kill completed.

- Exact hard HB chain attacked: diagonal adjoint-Teukolsky/QNM period positivity -> nonnegative complete full-cokernel orbit -> extinction -> source-FE unit physical-clock covariance -> RH.
- Corpus audit distinguished `d4BMXiGaugeFixedTotalRenormalizedAngularPeriod` (separately defined positive canonical period) from the literal nonlinear Schur-source causal cut; their identification still requires response-incidence and Einstein--Green reciprocity.
- Primary literature audit: Teukolsky QNM adjoint form is complex-linear in both entries, symmetric, not positive definite; discrete QNMs are not complete without continuum/branch-cut contributions (notably arXiv:2210.15935 and arXiv:2305.19332 context).
- New exact theorem: for complex-bilinear `B`, `B (z • x) (z • x) = z^2 B x x`; hence `B (I • x) (I • x) = -B x x`. Projective common-phase diagonal landing forces value zero. Any fixed nonzero calibration making all diagonal values real nonnegative annihilates the diagonal; symmetry plus polarization gives `B=0`.
- HB application: existence of projectively descended complex-bilinear diagonal landing for `hbXiPeierlsCanonicalFullCokernelUnitCarrierOrbitCut n q` iff `Re(q)=1/2`; universal landing iff RH. Thus it is a receiver, not producer.
- Combined with existing finite-KMS/Hermitian wrong-polarity result, this kills entire diagonal positivity dichotomy. Survivor: genuinely off-diagonal polarized source/left-QNM law with independent phase transformation.
- Lean module: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingHBAdjointQNMComplexBilinearPositivityNoGo.lean`.
- Capstone: `d4HBAdjointQNMDiagonalPositivityRouteKilled`.
- Umbrella wired in `formal/GaloisForLFunctions/RHTower.lean`.
- Direct Lean check and targeted module build passed. Axioms only `propext`, `Classical.choice`, `Quot.sound`. Global lint only unrelated concurrently unwired modules; new module reachable.
- Docs: `docs/drafts/pipeline/3-formalized/hb-adjoint-qnm-complex-bilinear-phase-positivity-no-go.md` and `docs/drafts/pipeline/5-failed/hb-adjoint-qnm-diagonal-positivity.md`.
- Frontier map was read-only and not edited.