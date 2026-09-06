# Chronological arithmetic averaging: scale theorem and finite evidence

Frozen [R] remains OPEN: real uniformly bounded arrays a(k,N), actual full L² heat residual q+sum a_k h(kt) -> 0, h=1/t-1/(exp(t)-1). RH NOT proved. Do not affirm user competitor/IPO allegations. Current goal was paused, not complete. No subagents were used or authorized.

Previous closed raw heat obstruction and geometric-damping exclusion: see `mem:research/chronological-raw-heat-obstruction-2026-09-06`.

## New exact Lean result
Module formal/GaloisForLFunctions/RHTower/ChronologicalArithmeticAveraging.lean, namespace RHTower; 12 public declarations plus 1 private helper. Scratch passed; final LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ChronologicalArithmeticAveraging exit0, requested leaf only, 8.5sec. All12 #print axioms checked: only propext/Classical.choice/Quot.sound. Authoritative lint passes existing size warnings. Umbrella import wired; no full/umbrella build. Total chronological repair program: 11 leaves/142 public declarations audited.

D_N(w)=q+sum mu(k)w(k)h(kt). For w0=1, exact Abel:
D_N=wN R_N+sum_(k<N)(wk-w(k+1))R_k.
Positive decreasing w gives positive coefficients with total1. If strict earlier raw norms <=C, then
||wN^-1 D_N-R_N|| <= (wN^-1-1)C.
For positive decreasing row weights w(N,k), w(N,0)=1 and w(N,N)->1, weighted convergence iff raw convergence. Volterra induction supplies boundedness; it is NOT assumed.
ArithmeticWeight epsilon k = exp(-epsilon log k), w0=w1=1; epsilon>=0 gives antitone positive weights and |mu*w|<=1.
CLOSED chronologicalArithmeticDamping_no_small_scale:
no epsilon_N>=0 with epsilon_N log N ->0 AND actual weighted residual norm ->0.
chronologicalArithmeticDamping_scale_floor:
every successful nonnegative power schedule has some delta>0 with epsilon_N logN>=delta at arbitrarily large N. Cofinal, NOT eventual or universal delta. No separate epsilon->0 assumption needed. Positive mass interpretation: >=1-exp(-delta) away from terminal cutoff cofinally.

Paper certificate docs/drafts/pipeline/3-formalized/chronological-arithmetic-averaging-scale.md.
Failed subroute card 5-failed/chronological-negligible-arithmetic-damping.md includes exact positive survivor and completed paper/Lean statuses. General [G] power schedule epsilon_N->0 remains OPEN.
Scratch artifacts /tmp/chronological_arithmetic_{manifest.json,axioms.lean,axioms.txt,axiom_summary.json,build.txt,lint.txt,index.txt}.

## Runpod experiments completed and downloaded
Local docs/drafts/pipeline/2-fully-proven/computations/chronological-arithmetic-averaging-2026-09-06/
Remote /root/chronological-arithmetic-averaging-20260906, authorized SSH root@157.157.221.29 port27094 key ~/.ssh/id_ed25519.
REPORT.md, scripts, all coeff/support CSV and NPZ, JSON diagnostics, plot PNG/PDF saved locally; report also remote.
Python3.8.10 NumPy1.24.4 SciPy1.10.1 mpmath1.3.0; 4worker processes*4BLAS threads. All mathematics computed remote, none feeds Lean.

N128,512,2048,8192:
best power eps found .001557958,.027173781,.040576755,.063893765
validated power norms .0025150095,.0677148529,.1517290657,.1706855227
final positive-average norms 6.5500532522e-7,1.6824284711e-8,1.2939677503e-9,1.0150298430e-9.
Averages alpha>=0,sum1; a_k=mu(k)sum_(j>=k)alpha_j; signs preserved,nonsquarefree0,C1.
Active cutoffs13,22,29,35; terminal masses0. N8192 chosen34singular-mode simplex cancellation, cutoff range5..7995, massquantiles10/50/90=73/302/1286.
Initial fully corrective Wolfe stagnated or hit2000iterations, so kept feasible incumbents; refinement deterministic SVD + LP + nonnegative renormalization, comparisons with smaller initial candidates. Solverfailure not infeasibility.
Training logGauss24, independent shifted48(power)/60(finalavg), omitted left energy<=1e-30, exact harmonic far-tail energy plus negligible exponential norm bound.52mp80spots/finalvector,maxdiff8.51e-15. No rigorous quadrature intervals or certified optima. N128 floatingdual6.54864e-7 nearprimal; larger dual bounds0 provide no floor.
Finite averages competitive with earlier boxfits but not all: previous N4096 C1fixedm16 norm3.50601e-10. Do NOT infer power schedule asymptotics or full convergence from four cutoffs. No zero inputs.

## Hard unclosed source question
Zero in closed convex hull {R_N:N>=1}; equivalently no v in L²,c>0 with <R_N,v>>=c allN. Positive distributions would solve[R] withC1, but no uniform residual control as rank/cutoff grow. Fixed mode feasibility is insufficient.
Uniformly norm-bounded raw subsequence at unbounded cutoffs plus local convergence would give weak0 then convexification; cofinal bounded recurrence itself unproved (related corpus Fatou route already exists). A best-prefix norm doesn't prove recurrence.
Other dual C1 attack: |<q,v>|<=sum|<h(kt),v>|. Compact-away tests with integral v/t=0 follow from Lambert/Mobius. Extending requires graph-norm density of correlation map to ell1, not L² density; Fatou wrong direction. Unproved.
Primary reference https://arxiv.org/pdf/0812.1689 (Balazard-de Roton): these power weights in classical NB setting have RH-conditional truncation/shifted-zeta estimates. Rates not transferred to heat norm; no novelty claim.

Main compact notes updated: 1-in-progress/chronological-bounded-repair-attack.md; focused chronological-arithmetic-averaging.md; CTF paragraph/table in rh-current-frontier-map.md. Concurrent external work in repo: preserve changes. No commit/push. Own Lean/Runpod drivers exited; external Lean jobs are not ours, never kill them. One foreground Lean per agent, --old leaf audits only; clean owned jobs. Numerical work remote only. No remaining experiment or formal audit required from this pass.
