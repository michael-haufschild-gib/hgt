# Signed Cayley record and fixed-theta mismatch (2026-09-03)

Paper cards:
- docs/drafts/pipeline/2-fully-proven/universal-law-field/restricted-grassmannian-formation-geometry/cayley-collision-record-homotopy-defect.md
- docs/drafts/pipeline/2-fully-proven/universal-law-field/restricted-grassmannian-formation-geometry/cayley-theta-record-flatness-mismatch.md
- failed fixed-scale class: docs/drafts/pipeline/5-failed/universal-law-field/restricted-grassmannian-formation-geometry/fixed-scale-theta-record-completion.md

Correction to mem:cayley-collision-record-homotopy-defect-2026-09-03:
- Oriented source state is Omega_H=sqrt(105/8) delta(1-delta^2), not its absolute value.
- Survival is signed S=M_delta; exit E=M_sqrt(1-delta^2).
- e_n=sqrt(105/8) delta^(n+1) kappa.
- Prime swap J gives J Omega_H=-Omega_H, J S J=-S, J E J=E, J e_n=(-1)^(n+1)e_n.
- Positive dephased T=directSum |e_n><e_n| is J-even; orientation is exactly in coherent cross-grade parity before dephasing.
- Atomic state uses delta_pq/sqrt(1-lambda_pq), not positive sqrt(lambda/(1-lambda).

New theorem ULF-CTRFM-001:
- Literal theta polarization has the same signed complementary colligation S_a=tanh(ax), E_a=sech(ax); both source and theta full exit histories are isometries.
- Source marked spectral law dmu_H=(105/16)v^2(1-v^2)^2dv has cubic endpoint mass mu_H(|v|>1-eps)~(35/2)eps^3 and moments n^3 m_n->105/8.
- Literal theta superexponential envelope forces every fixed-a contrast pushforward to be flat to every endpoint order and its survival moments q_n(a)=o(n^-K) for every K.
- Hence no fixed-a state-preserving isometry can intertwine source Cayley survival with theta contrast.
- Surviving completion must be history-scale-running, singular at unit contrast, or change marked spectral law by an independently derived anomaly counterterm. It also needs an orientation-line twist because source marked input is odd while theta constant vector is even.

STATUS facts F512-F513, FAIL-83, CANNOT-236, MUST-158. No Lean edits/builds in read-only research phase.