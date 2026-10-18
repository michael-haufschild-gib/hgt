# Nonnegative endpoint order and calibrated short-window defect (2026-10-18)

Sixth contribution in ongoing THIM track; research goal remains active. Baseline label: New formulation of positive divisor incidence and elementary polarization, with Known/Corollary constituents. No external novelty claim. No signed Mobius/damped sign improvement.

Source: formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/NonnegativeWeightEndpointOrderAndCalibratedDefect.lean
SHA256: 0fc3ea2455ec3f5f9a792631545ae2e36b3cfda24fc6d8044bd3fc4af0e4df05
24 public theorems, no definitions, 2 private helpers. Imports ShortWindowCorrelationDefectAndIsoStateClassification only.

Exact mathematics: let a=M0+1, b=M0+M+1, DeltaD=D_N(M0+M;c)-D_N(M0;c), and E=short-window Dirichlet energy.
- sigma_N(k)|sigma_N(l) iff every visible divisor of k divides l iff s_c(k)<=s_c(l) for every nonnegative weight c.
- R_N(k)|R_N(l) iff visible prime inclusion iff response comparison for every nonnegative squarefree-supported c.
- DeltaD<=0 for every nonnegative c iff sigma_N(b)|sigma_N(a). For squarefree c replace sigma by R. Under order, DeltaD<=-E/2.
- Necessity remains on every fixed positive harmonic slice H_c=H>0 even with every coefficient in [0,H]. If q in [2,N] divides b but not a, u=delta_q, Q=DeltaD(u)-1/q, t=H/(|Q|+1), c=t*u+(H-t/q)*delta_1. Then c is nonnegative, bounded by H, calibrated to H, and DeltaD(c)=t^2*(Q+|Q|+1)>0. Failed radical order exposes prime q, hence squarefree support.
- For nonnegative c, H_c=0 iff all visible coefficients vanish. Then every response/defect vanishes. H<0 has no nonnegative realization. Universal defect nonpositivity on any fixed H slice iff H<=0 OR reverse endpoint state order, with radical analogue.

Paper proof/card: docs/drafts/pipeline/3-formalized/thim-positive-weight-endpoint-order.md. Ledger: logs/thim-radical-sawtooth-knowledge.md.
Actual final leaf compiled via lake --old env lean -o <leaf.olean> <leaf.lean>, exit0 no warnings. Untouched short-window dependency also compiled, SHA256 e090ac704457c67f228ff7e36e8dee4696f1cfb24516ee44cf93f80ffead6f9c. All 26 declaration closures exactly {propext, Classical.choice, Quot.sound}, scratch audit exit0. Artifact audit logs/thim-order-audit.json passed hash, closures,24 docstrings/API entries, fresh .oleans, unique umbrella import, MainTheorems reachability, whitespace and forbidden tokens. Evidence logs/thim-order-{lean,dependency-lean,axioms,index,lint}.txt. First index/lint saved as -first; one refresh fixed concurrent stale generated docs. Final lint exits1 with exactly3 unrelated structural errors: BVI InteriorMartingaleQuadraticGradientAndRenormalizedDriftBudget, BVI MultiLagBezoutLayerHierarchyAndFourStepInteriorCalculus unwired; existing root-registration complaint for TransHorizonIncidenceMechanics.lean. No new-leaf, forbidden-declaration, or stale-doc error. All owned jobs terminal; five /tmp scratch files deleted. No full/umbrella build, README edits, numerical experiments, added axioms, heartbeat changes, commits, or pushes.

Related: `mem:trans-horizon/active-sawtooth-interpolation-conditioning`, `mem:trans-horizon/active-sawtooth-power-recovery`, `mem:trans-horizon/radical-checkpoint-sign-rigidity`, `mem:trans-horizon/radical-state-defect-normal-form`, `mem:trans-horizon/all-horizon-radical-sawtooth-defect`.
