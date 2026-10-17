# Source-line projection supplies no extra exact-clique gain

- **Stage:** 5-failed; only the proposed extra gain on exact source cliques is retired.
- **Scope:** Independent BiScale Uncertainty; full multiplier-lifting program remains active.
- **Status:** Boundary and positive survivor are paper-proved and Lean-verified.

For the actual odd source F, let P=sum a_p F(.+d_p) be the ordered difference
packet, R=h_F(0), K=<F,P>, G=||P||^2, mu=M/R, and Q=||q_mu||^2.
Source clique zeros give h_F(d_p)=0 for every off-diagonal pair. Consequently
K=0 and the explicit source correction E_c=0 for every scalar center c.
Projecting P off F subtracts K^2/R=0. It therefore cannot improve the earlier
mean-centered multiplier envelope. The exact statement is

U_perp=U_mu<=U_c for every real c.

This proves the sharp boundary of this particular optimization route. It does
not refute other projections, stronger source-grid estimates, or odd positivity.

## Positive survivor

For arbitrary signed source correlations, q_mu is orthogonal to F and the
actual compact source P_perp=P-(K/R)F has energy G-K^2/R>=0. Thus

|D-E_mu|<=sqrt(Q(G-K^2/R)),
U_perp<=E_c+sqrt(Q_c G) for every c.

The second inequality follows from E_c=E_mu+(c-mu)K,
Q_c=Q+R(c-mu)^2 and the exact two-dimensional square identity
(a^2+x^2)(b^2+k^2)-(ab-xk)^2=(ak+xb)^2.
At R=0, Cauchy--Schwarz forces M=K=0, so no nonzero-energy premise is needed.
The source Schur bound transfers into the complete secant/plastic receiver,
retaining its positive plastic remainder, negative odd moment and support factor.
This is a useful signed-correlation refinement and an exact classification of
where source-line projection stops helping. Boundary and survivor count together
as contribution six, not as multiple contributions.

## Formal evidence

Module: `formal/GaloisForLFunctions/BiScaleUncertainty/ProjectedHyperbolicGramControl.lean`.
Namespace: `GaloisForLFunctions.BiScaleUncertainty.ProjectedHyperbolicGram`.
Boundary: `sourceClique_centering_boundary`.
Positive survivor: `odd_defect_abs_sub_meanCorrection_le`,
`projectedDefectUpper_le_every_center`, `odd_plasticCrossover_ge_projected`.
Actual-source compilation passed without warnings. All 16 public theorem axiom
audits used only `propext`, `Classical.choice`, `Quot.sound`.
SHA256: `27a0251e688b257952cca194ea612814c5c73f5b9e1e3a01349932f9411b0384`.
Global lint limitations and complete paper proof are on the continuing master card
`docs/drafts/pipeline/1-in-progress/hyperbolic-multiplier-lifting-2026-10-17.md`.
