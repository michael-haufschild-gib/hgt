# Chronological repair: growing-prefix tests and exact harmonic normalization

[R] remains OPEN: actual full L² heat residual q+sum_(k<=N)a(k,N)h(kt)->0 with one finite coefficient bound, h=1/t-1/(exp(t)-1). RH NOT proved. [G] power schedules remain open. Goal was paused, no budget; do not mark complete or use tools to resume. User insists attack hardest source estimate each turn, not just receivers/auxiliary formalization. No subagents authorized or used. Competitor/IPO claims are unverified and do not change standards.

Prior results: `mem:research/chronological-arithmetic-averaging-2026-09-06` and `mem:research/chronological-raw-heat-obstruction-2026-09-06`.

## New closed Lean positive result Q/Q+
formal/GaloisForLFunctions/RHTower/ChronologicalHarmonicCharge.lean (~311 lines), namespace RHTower.
12 public declarations, 3 private helpers. Scratch /tmp/ChronologicalHarmonicCharge.lean passed.
Final LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.ChronologicalHarmonicCharge exit0, only requested leaf compiled, 10sec.
All12 public #print axioms audited: only propext/Classical.choice/Quot.sound. Authoritative lint passed existing size warnings. Umbrella import wired; no full/umbrella build.
Total chronological repair program:12 leaves/154 public declarations audited.

S(a,N)=sum_(k<=N) a_k/k, B(a,N,t)=sum a_k/(exp(kt)-1).
Exact residual r=S/t+exp(-t)-B.
If |a_k|<=C,C>=0,t>=1, |B|<=4C exp(-t), independent of N.
For every T>=1:
|S| <= (T+1)(||r||₂+(1+4C)exp(-T)).
Proof integrates t*r identity over (T,T+1] and Cauchy–Schwarz; finite geometric bounds, no computations.
Therefore every bounded successful array has S_N->0.
Normalize a'_k=a_k-[k=1]S_N; exact charge0, residual change -S_N h(t).
Consequently for EVERY eta>0 a successful array with bound C gives an exactly zero-charge successful array with bound C+eta: after |S_N|<eta use that correction; finitely many earlier rows zero.
This does NOT preserve exact C=1 or an exact frozen Möbius prefix. It does not construct a successful array or control t->0 concentration.
Main theorem chronologicalSuccessfulRepair_zeroCharge_normalization; quantitative chronologicalHarmonicCharge_L2_bound; limit chronologicalHarmonicCharge_tendsto_zero.
Full coordinatewise convergence to mu [E] remains unformalized/open as a formal target; do not claim it closed.

Certificate docs/drafts/pipeline/3-formalized/chronological-harmonic-charge.md (moved our new paper card out of 2-fully-proven after audit).
Artifacts /tmp/chronological_charge_{manifest.json,axioms.lean,axioms.txt,axiom_summary.json,build.txt,lint.txt,index.txt}.

## New experiments, complete / downloaded / report remote and local
Local docs/drafts/pipeline/2-fully-proven/computations/chronological-escaping-averages-2026-09-06/
Remote /root/chronological-escaping-averages-20260906
Authorized ssh root@157.157.221.29 -p27094 -i ~/.ssh/id_ed25519
REPORT.md and plots escaping-averages.png/.pdf saved.
Scripts escaping.py, release_monotonicity.py, plot_results.py depend on sibling remote /root/chronological-arithmetic-averaging-20260906/{kernel_reference.py,averaging.py}.
All mathematical computation was Runpod only; no proof inputs. No driver left running.
32CPU,128GB; Python3.8.10 NumPy1.24.4 SciPy1.10.1 mpmath1.3.0.
H:4workers*4BLASthreads,43.15sec including checks. J:3workers*4BLASthreads,12.59sec.

Frozen H: all integer raw cutoffs j in [M,N] available, positive alpha,sum1, a_k=mu_k sum_(j>=k)alpha.
Thus first M coefficients exactly mu, signs preserved,nonsquarefree0,C1.
N512 / M=1,8,32,128,256 norms:
1.682428471e-8,1.689966606e-8,2.359106211e-8,1.512012923e-7,9.047941963e-6.
N2048 / M=1,32,128,512,1024:
1.293967744e-9,3.941703737e-9,8.632402192e-9,3.525014513e-7,9.030980235e-6.
N8192 / M=1,128,512,2048,4096:
1.015029843e-9,2.528261242e-9,9.242963235e-9,7.154861443e-8,5.933280168e-6.
Half-prefix floating quadrature primal/dual nearly coincide all3N; N8192 dual5.933273756e-6, 5active cutoffs range4885..7966. No interval certificate or asymptotic floor.
Wolfe+deterministic SVD/simplex LP. Retained all narrower-window candidates in wider windows. Nested-set monotonicity verified. DifferentN with growingM are not nested.

Frozen J independently BEFORE running: N8192 M4096 C1, release monotonicity; prediction sign-preserving error<=1e-8.
Sign-preserving nonmonotone squarefree:1.293389917e-8,636 envelope increases along squarefree indices.
Signed squarefree box:1.204789476e-8.
Full box:6.054397431e-9.
Prediction NOT ATTAINED, but NOT mathematically refuted: dual bounds0 all3 relaxed classes. Do NOT relabel full-box success as sign-preserving pass. Same exact frozenhead,C1 throughout.
SVD exact-leading-mode and balanced-mode bounded LP, actual kernel reevaluation after clipping, stricter-family incumbent retention. No optimum claim.
Training Gauss24; independent shifted60; left omitted energy<=1e-30; exact harmonic tail energy at80 plus negligible exponential norm bound;32mp80 spots/vector, largest displayed H N8192 difference3.12e-14,J5.40e-14. No rigorous quadrature intervals.
JSON all diagnostics, CSV all vectors/supports, NPZ including rescaled H profiles, raw run.log/release.log preserved.

## Hard attacks and remaining gap
Current focused card docs/drafts/pipeline/1-in-progress/chronological-escaping-averages.md; main compact chronological-bounded-repair-attack.md updated, previous averaging card linked, CTF paragraph/table updated.
1 Positive infinite divisor coefficients b_eps(n)=prod_(p|n)(1-p^-eps) give exact pointwise residual 1/[zeta(1+eps)t]-sum_(n>=2)b_eps(n)e^-nt. Positivity controls no critical discrepancy; direct absolute estimates lose half exponent.
2 Reflected zeta quotient bound is unconditional, but identifying it with Mellin transform of actual L² truncation limit is not. Primary https://arxiv.org/pdf/math/0205003 pp4-6 explicitly uses RH for convergence/membership before reflected-bound step. No heat-rate transfer claimed. https://arxiv.org/pdf/0812.1689 conditional approximation estimates.
3 Scalar zero-phase cancellation does not cancel moving profiles: Mellin exponent rho-s over entire line. Cutoff-dependent physical rescaling changes target/dilations and is not[R].
4 Local convergence/slow variation alone insufficient; concentration can escape to t0. Finite mode feasibility has no quantitative uniform rank/cutoff bound.
Still need actual bounded arrays with full norm->0; positive averaging is a restrictive open subfamily. Exact charge normalization removes far tail only. No source route retired; no RH proof or novelty claim.

Process discipline: one foreground Lean per agent, scratch lake env lean, final leaf lake build --old (ordinary builds spawned dependency workers previously; never full builds). Standard axioms only. No new norm_num/native_decide/decide tactics. Current own Lean/remote driver sessions exited. Concurrent external edits/commits continue in repo: preserve them, no commit/push by us. Read-only inspection of external MobiusDivisorAbelDiagonalBound found only a diagonal ceiling, explicitly no RH cross-term estimate; it was not used in proofs.
