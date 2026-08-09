# Low-replica complete-incidence frontier correction (2026-08-09)

Persistent goal: prove Brown–Susskind full growth–plateau–recurrence for ordinary static fixed-local Hamiltonians plus permanent non-Haar locality.

New paper-proved theorem:
`docs/drafts/pipeline/2-fully-proven/low-replica-complete-incidence-influence-law.md`.

Key correction:
- Bounded binomial complete-incidence reporter at fixed fidelity slack delta needs only
  `r_n = ceil(4 log n / delta^2)`, giving threshold error <= n^-2 for an arbitrary finite target image, independent of target count and circuit depth.
- Thus r=Theta(D), growing-replica observer crowding, worst character gradients, pseudodeterminants, and Bures nuclear contraction are not mandatory physical invariants. They remain older sufficient proof routes.

Low-influence theorem:
- Orthogonal phase orbit psi(phi)=sum_j exp(-i phi_j)u_j, p*=max ||u_j||^2.
- For arbitrary finite unit target set Z, Y=max_z |<z,psi>|^2, F=B_(r,k)(Y).
- Since B'<=r and sum_j |partial_j X_z|^2<=4p*, finite max preserves the bound:
  ||grad_phi F||^2<=4r^2 p*.
- Product-torus Poincare: Var_phase F<=4r^2 p*, with no |Z|.

Common light filter:
- collision C=sum p_j^2, threshold tau=C/rho^2, retain p_j<=tau.
- removed norm^2<=rho^2 and retained p*<=C/rho^2.
- If C<=c/D, Var_phase F_light<=4cr^2/(rho^2D)=O((log n)^2/D).
- Fidelity threshold transport costs only fixed observational slack.
- Return restriction remains exact via parent Theorem B'.

Honest remaining core:
Prove quantitative fixed-shell physical-graph mixing for this one bounded low-influence complete-incidence observable at Brown time/depth, after target-independent return excision. Low Haar variance alone does not suffice because the static phase graph is singular and may lie in a Haar-rare set. No current new Lean module supplies this. No Lean written or built due active refactor.

Related memories: `mem:research/static_local_complexity`, `mem:quantum/return_shell_coarea_frontier_2026_08_07`.