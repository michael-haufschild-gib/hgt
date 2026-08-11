Created dependency-closed Stage-2 card:
- docs/drafts/pipeline/2-fully-proven/capacitary-observer-sector-excision-law.md
- master log appended in docs/drafts/pipeline/1-in-progress/static-local-complexity-law.md

Exact theorem:
For reversible gate Markov P, fugacity 0<a<1, target A, first-entrance potential h_A, charge q_A=(I-aP)h_A, and cap=<h,q>, normalized charge rho_A=q_A*pi/cap is a probability supported on A. For every finite P-invariant bounded real eigenmode sector E containing constants,
<h_A,phi_j> = cap E_rho[phi_j]/(1-a lambda_j).
Thus Pi_E h_A = cap/(1-a)+cap int R_E,a(x,y)d rho(y), and for every endpoint probability law nu, even singular to Haar,
|nu(Pi_E h_A)-cap/(1-a)| <= cap B_E,a.

New leverage closure:
If K_E^0 is centered projection kernel and L_E=sup_x K_E^0(x,x), Neumann resolvent + Markov L-infinity contraction gives B_E,a<=L_E/(1-a). For homogeneous K-dimensional sectors L_E=K-1. For realified k-copy U(D) matrix coefficients of U^⊗k⊗bar(U)^⊗k, dim_R E<=2D^(4k)+1 and B<=2D^(4k)/(1-a). Hence every poly(log D)-copy locality observer is exp(o(D)) and capacity-blind against exp(-Theta(D)) targets.

Complete union:
nu{C_epsilon<=s} <= (M/a)^s [cap((1-a)^-1+B_E,a)+R_E,a^+], where R_E,a=nu((I-Pi_E)h_A). Therefore only the high-mode Bellman remainder remains.

Pointwise complexity/recurrence coordinate:
(a/M)^C<=h_A<=a^C and r_E=(I-Pi_E)h_A obeys
r_E(return)>=1-cap((1-a)^-1+B),
r_E(C>=s)<=a^s-cap/(1-a)+cap B.
Thus recurrence and complexity plateau live in high observer modes, while permanent locality modes remain capacity-small.

Hostile limits:
- classical potential/spectral machinery; novelty is circuit composition and exact locality-complexity sector separation;
- no Brown-time decay of high-mode remainder proved;
- fixed a required; arbitrary observer must be placed in named invariant sector;
- no Lean written because shared corpus refactor is active.

Next core:
Prove Brown-skeleton decay of high-mode Bellman remainder after common return and fast-forwardable-carrier removal. Do not retry positive gate smoothing: suffix damping pays (M/a)^ell and cannot beat circuit entropy. Related memories: `mem:quantum_recurrence/first_entrance_gate_capacity_frontier_2026_08_10`, `mem:quantum_recurrence/bellman_duality_and_static_reuse_frontier_2026_08_09`.