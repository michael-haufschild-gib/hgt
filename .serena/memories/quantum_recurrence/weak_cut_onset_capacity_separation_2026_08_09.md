# Weak-cut Brown-onset/capacity separation, 2026-08-09

New Stage-2 card:
- docs/drafts/pipeline/2-fully-proven/weak-cut-complexity-onset-capacity-separation-law.md

Exact theorem:
- For H=H_A tensor I + I tensor H_B + V and a product seed, Duhamel plus factor synthesis gives
  C_epsilon(exp(-itH)chi) <= S_A(eta_A)+S_B(eta_B)
  throughout |t| ||V||_op <= epsilon-eta_A-eta_B.
- Balanced split cap is 2^(n/2) poly(n)=o(2^n/log n).
- Product of two cubic-phase seed families has basis-uniform mean spectral collision <=4/2^n even against an entangled eigenbasis.
- For every prescribed delay L, density of generic simple/cyclic/maximal-projective-rank nearest-neighbor shell points near a decoupled point yields one fixed ordinary local H and one product cubic seed that remain below full-scale complexity until L but later have an Omega(2^n/log n) plateau for exp(Omega(2^n)) time, recurrence, and permanent local two-query Haar separation.
- Therefore collision O(1/D) and maximal projective rank control capacity but not first onset.
- A path edge has 9 coupling coefficients. On the uniform m=12n-9 shell their squared norm has Beta(9/2,(m-9)/2) law. The single-edge delay floor is c_n L^-9.
- Pauli HS/operator comparison rho_e <= ||V_e||op <= 3 rho_e and union over n-1 edges gives F_m,9(x/3) <= P(g_path<=x) <= (n-1)F_m,9(x). At inverse Brown scale this is exp(-Theta(n)), up to polynomial factors.

Frontier correction:
- Unconditioned first-onset theorem cannot have a smaller failure tail.
- Condition on path conductance good and pay the weak-cut tail once.
- Conductance is necessary for product seeds but not proved sufficient. Remaining core: quenched geometric-skeleton Bellman escape on conductance-good shell.
- This is a no-go/frontier theorem, not Brown closure or Nature readiness.
- No Lean file/process touched during refactor.
Related memories: `mem:quantum_recurrence/geometric_skeleton_brown_ramp_transfer_2026_08_09`, `mem:quantum_recurrence/bellman_duality_and_static_reuse_frontier_2026_08_09`.
