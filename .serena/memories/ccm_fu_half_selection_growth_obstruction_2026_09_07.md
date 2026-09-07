# CCM-FU PE5 fully refuted; actual normalized mean unbounded

## Goal and boundary
RH goal remains ACTIVE. Full chain: completed Guinand–Weil source → marked rectangular current → affine Suzuki checkpoints → signed curvature → coherent prime–polar–Gamma/unit-Riesz boundary → Xi-screw Green → RH. PE5 independent averaging is now unconditionally REFUTED in Lean. PE4 adaptive original-ceiling path, SD1 final diagonal bound, and RH remain OPEN. No exact sign or asymptotic for the deformed mean is claimed.

## New closed endpoint (root namespace RHTower)
`MobiusHalfSelectionGrowthObstruction.lean` (7 public theorems):
- `squareRootAbelPrefix_halfSelectionDivisorConvolution N`: generic weighted prefix equals cast of actual `mobiusDivisorHalfSelectionHead (N+1)`.
- `not_exists_mobiusDivisorHalfSelectionHead_linear_bound`: no real C bounds |H(M)| by C*M for all M.
- `exists_mobiusDivisorHalfSelectionHead_gt_linear C`: some M exceeds any proposed linear envelope.
- `exists_mobiusDivisorHalfSelectionHead_gt_linear_after C M₀`: some M>=M₀ has C*M<|H(M)|.
- `exists_mobiusDivisorHalfSelectionEnergy_gt_diagonal_multiple K M₀`: some M>=M₀ has K*Q(M)<E_half(M).
- `not_exists_eventual_mobiusDivisorHalfSelectionEnergy_diagonal_budget`: no K,M₀ give the energy bound on the tail.
- `not_forall_mobiusDivisorHalfSelectionEnergy_le_initial`: direct original PE5 factor-one ceiling fails.
The proof combines the new exact transfer below with the PREVIOUSLY audited `not_exists_analytic_halfSelectionDivisor_extension`. Finite-prefix absorption gives every-tail growth. Existing H²≤E and Q≤722M² give all fixed energy budgets, using C=sqrt(722*|K|). No computation enters the proof.

## Exact two-Abel transfer (new and closed)
`SquareRootAbelDirichletKernel.lean` (7 public theorems, 2 definitions):
- u(x)=sqrt x+sqrt(x+1), cancels sqrt(x+1)-sqrt x exactly.
- u(x)≤3sqrt x for x≥1; |u(x+1)-u(x)|≤1/sqrt x for x>0.
- K(x,s)=u(x)*(x^(-s)-(x+1)^(-s)).
- norm K≤3norm(s)*x^(-Re(s)-1/2).
- norm(K(x,s)-K(x+1,s))≤(3norm(s)norm(s+1)+norm(s))*x^(-Re(s)-3/2).
- K entire in s for x>0.
`SquareRootAbelDirichletContinuation.lean` (4 public theorems, 2 definitions):
- term A n s = A(n+1)*(K(n+1,s)-K(n+2,s)); sum is its tsum.
- If norm(A n)≤C(n+1), C≥0, term dominated by 2C*(3norm(s)norm(s+1)+norm(s))*(n+1)^(-(Re(s)+1/2)).
- Absolute summability, locally uniform summability, AnalyticOnNhd on Re(s)>1/2.
- Uses mathlib SummableLocallyUniformlyOn_of_locally_bounded, compact minimum real part and maximum norm; term differentiability from kernel.
`SquareRootAbelDirichletTransfer.lean` (7 public theorems, 1 definition):
- squareRootAbelPrefix g N = sum(k∈Icc1N)(sqrt(k+1)-sqrt k)*sum(n∈Icc1k)g n.
- Exact successor and clock-inverse prefix-increment identities.
- sum_dirichlet_eq_squareRootAbel g s N: sum(n≤N)g(n)n^-s = G_N*(N+1)^-s + A_N*K(N+1,s) + sum(n∈rangeN)term A n s.
- Linear A bound yields norm(G_N)≤6C(N+1)^(3/2).
- First boundary tends zero Re(s)>3/2; second Re(s)>1/2.
- squareRootAbelDirichletSum_eq_LSeries hC hA hs hg: candidate equals literal LSeries where Re(s)>3/2 and LSeriesSummable g s.

## Verification already completed; do NOT repeat
All four leaves passed scratch and foreground `lake env lean <leaf> -o <exact olean>`; all exact oleans exist. They are wired ONCE at RHTower.lean after MobiusHalfSelectionPoleObstruction. NO umbrella, large, dependency or lake build run. All25 NEW public theorems were axiom-audited ONCE: only propext, Classical.choice, Quot.sound. Never re-audit these or the earlier26 Euler/pole theorems.
Global `scripts/formal_tools.py lint` ran once; sole error at that snapshot: unrelated concurrent unwired `RHTower.ThetaCuspEffectiveLikelihoodCooling`. No new CCM-FU leaf flagged. `formal_tools.py index` ran once (5 changed,0 removed); git diff --check passed. Four new leaves are149,111,182,114 lines. All task scratch/log files cleaned and no owned Lean process left.

## Documentation current state
- Moved PE5 from in-progress to `docs/drafts/pipeline/5-failed/ccm-fu-bernoulli-prime-energy.md`; strongest positive survivor and exact paper/Lean status recorded. Updated every docs link. Old memories referring to prior path are historical.
- New certificate `docs/drafts/pipeline/3-formalized/ccm-fu-half-selection-growth-obstruction.md`.
- Updated frontier CCM-FU paragraph, SD1 card, PE4 card, earlier Euler/pole certificate.
- Extended universal MUST-217: unbounded normalized exact mean on every tail excludes fixed larger average budgets and finite-prefix repairs; this does not refute adaptive path existence.

## Efficient Lean / pitfalls
One foreground Lean process per agent; poll same session, never restart on timeout. Prefer source scratch then only needed exact olean. No umbrella builds. Keep other agents' processes and unrelated edits.
Mathlib oleans are under formal/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.
Real power limit corpus helper GaloisForLFunctions.RHTower.tendsto_rpow_neg_nat_atTop; compose tendsto_add_atTop_nat 1 and const_mul, simpa.
Finset.sum_Ico_eq_sub generated from prod_Ico_eq_div: reindex Icc1N and sum range(N+1), zero LSeries.term at0.
For Complex norm positive-real cpow, make `have h := Complex.norm_cpow_eq_rpow_re_of_pos hx (y := -s)` and `simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,Complex.neg_re] using h`; rw may normalize casts too soon.
Avoid tokens `|C|*` (parsed |*); add spaces. Avoid `σ≤s.re` graph notation. For single_le_sum with let-defined finite sum, explicit f binder needed.
`rw [sum_mul_eq_partial_mul_diff_ring] at hfirst` rewrites the wrong first sum; bind hsecond with exact F/kernel then rw [hsecond].
Next substantial work must address actual PE4/SD1 or another full CCM-FU source mechanism, not reopen the refuted independent average or weaken its frozen ceiling.
