# Route E weighted projection + recurrence Dirichlet frontier (2026-08-11)

Status: Route E and RH remain open. No Lean source edits or builds during corpus refactor. Internal corpus only; no literature/computation.

## Main exact projection lane
For normalized source/target laws alpha,beta on finite physical relation E, reachable target marginal polytope C_E has
d_E^2 = min_{gamma in C_E} sum_t (gamma_t-beta_t)^2/beta_t.
Minimum physical centered energy is (A^2/B)d_E^2. Exact finite projection dual:
d_E = sup_f [sum_s alpha_s min_{t~s} f_t - E_beta f]_+ / sqrt(Var_beta f).
Zero iff normalized weighted Hall. One-sided density r<=1+epsilon yields only Var_beta(r)<=epsilon sharply; endpoint needs epsilon<=X^(-1+o(1)), or two-sided epsilon<=X^(-1/2+o(1)). Exact Hall is zero-energy stronger.

## New grown-Lean direct lane
Read-only basis: formal/GaloisForLFunctions/RHTower/MobiusBoundaryOppositeSignTransport.lean, umbrella imported. Existing unconditional unused-conductance/degree-normalized consumer implies, for symmetric parity-flipping graph with edge length <=H,
|J_V(x)| <= W_iso(x)+xH Z_V(x)+sum_{n<m} b_nm e^(-xm)|1/D_n-1/D_m|.
For nonnegative substochastic recurrence kernel P, set r_n=sum_m P_nm, ell_n=sum_m P_mn, b=(P+P^T)/2, D=(r+ell)/2, q=1/D. Define
E_P(x)=sum_{n<m} b_nm e^(-xm)(q_n-q_m)^2.
Exact Cauchy bridge:
|J_V(x)| <= W_{P,0}(x)+xH Z_V(x)+(1/2)sqrt((1+e^(xH)) Z_V(x) E_P(x)).
At x=1/X, H=X^(1/2+o(1)), Z=X^(1+o(1)), sufficient producer:
W_{P,0}<=X^(1/2+o(1)), E_P<=X^(o(1)).
This retains recurrence weights, strict-half prime-dilation displacement, Gibbs weights, finite alternating signs; no Metropolis overlap/detailed balance.

One-sign firewall (correct orientation-general form): if rows only S->T, source row mass 1, target rows 0,
E_P(x)=2 sum_{t:ell_t>0} omega_t(x)(ell_t-1)^2/ell_t,
omega_t=ell_t^(-1) sum_s P_st e^(-x max(s,t)),
with e^(-xH)e^(-xt)<=omega_t<=e^(-xt). Equality omega_t=e^(-xt) holds for monotone s<t transitions. Hence at strict-half scale this is uniformly equivalent to reverse column chi-square; one-sign restriction gives no burden reduction.

Complete-bipartite blocks prove edge displacement and degree exponents cannot force small degree-BV. Literal bounded one/two/four-prime replacement graph is retired: formal y-friable isolation plus existing failed-route density audit gives linear isolated Gibbs mass under every sublinear pruning. Arbitrary endpoint-optimized max-flow is theatre (complete-bipartite optimum equals signed imbalance).

Live direct target:
ENTROPY-COMPLEMENT-RECURRENCE-WEIGHTED-INVERSE-LOAD-DIRICHLET-STRICT-HALF.
Instantiate parity-agnostic source-defined outgoing rows on both Möbius signs on one common physical aperture; retain seam/recurrence labels; prove W_{P,0}<=X^(1/2+o(1)) and E_P<=X^(o(1)) uniformly on nested apertures.

Key docs:
- docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/route-e-weighted-hall-anova-projection-duality-law.md
- docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/route-e-degree-normalized-gibbs-boundary-variation-law.md
- docs/drafts/pipeline/1-in-progress/route-e-cofinal-parity-energy-covariance-accumulation.md
- docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md