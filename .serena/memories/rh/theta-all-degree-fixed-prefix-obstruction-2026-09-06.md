# All-degree theta Hankel producer remains OPEN

Target: actual theta density -> logarithmic moments M_k -> all finite Hankel forms >=0 -> RH. No all-degree producer was found in this turn. Actual full-source degree-one closure from `mem:rh/theta-gibbs-stein-first-source-minor-2026-09-06` remains valid; degree two and beyond remain open. User explicitly objects to replacing the hard source sign with interfaces or finite checks.

## New exploratory evidence (Runpod only)
Folder `docs/drafts/pipeline/2-fully-proven/computations/theta-all-degree-source-2026-09-06/`, REPORT.md, scripts, all raw JSON downloaded.
- First theta atom logarithmic Hankel form fails degree 3: scaled min eigenvalue -4.678667293227019e-5, Schur -0.0015489838759958548.
- First two theta atoms pass tested degrees 1..11, fail degree12: min eigenvalue -2.163911251826798e-18, Schur -8.741364044713950e-15.
- Third atom repairs tested degree12: min eigenvalue +6.277005214926623e-19.
- Six atoms positive through tested degree12. NOT an infinite-source theorem.
- Ward formula in x at220dps agrees to45displayed digits with direct positive density in y=exp(2x) at160dps. Both have numerical integration cutoffs; no interval sign certificates. No computed value enters Lean. All own Runpod jobs ended. Another task's worst_aperture.py was running; do not kill it.

## New unconditional Lean source theorem
`formal/GaloisForLFunctions/RHTower/ThetaFiniteShellFourierBoundary.lean` (~350lines), umbrella wired. Write C_f(t)=int_0^infty f(x)cos(tx)dx. For every finite nonempty canonical prefix P_N of actual theta density Phi:
- t^2 C_(P_N)(t) -> -P_N'(0)<0.
- t^2 C_(Phi)(t) ->0.
- t^2 C_(Phi-P_N)(t) ->P_N'(0)>0.
Both prefix negative and remainder positive eventually. This exposes exact leading Fourier compensation across EVERY finite cutoff. A negative cosine value is NOT a negative Hankel witness; do not claim formal all-prefix Hankel failure.
Proof uses polynomial-Gaussian derivative integrability and decay, exact two half-line IBPs, existing positive finite-prefix seam slope, complete-source reflection, Riemann-Lebesgue. No numerical premises.
Capstones `tendsto_thetaFiniteShellCosine_mul_sq`, `eventually_thetaFiniteShellCosine_neg`, `tendsto_thetaFullCosine_mul_sq_zero`, `tendsto_thetaShellRemainderCosine_mul_sq`, `eventually_thetaShellRemainderCosine_pos`.
Scratch/source lake env lean checks and named leaf build passed. All five axiom audits only [propext, Classical.choice, Quot.sound]. Formal index refreshed. scripts/formal_tools.py lint passed (existing large-file warnings only). Final git diff --check passed. All own Lean and Runpod computation processes ended.

## Producer implication and documents
A positive fixed first-atom/all-degree foundation is numerically false; two-atom replacement also fails later. Full arithmetic tail or joint degree/cutoff/conditioning control is required for this approach. Exact cancellation alone supplies no surviving Hankel sign.
Active card `docs/drafts/pipeline/1-in-progress/theta-all-degree-hankel-producer.md`; formal proof card `docs/drafts/pipeline/3-formalized/theta-finite-shell-fourier-boundary.md`; frontier updated only current state near central source Hankel first minor; universal route-independent approximation constraint added.
Heavy corpus searches tested hard-exclusion cumulant collapse (no actual theta realization), Schur/Feshbach (identity only, no sign), Ising/FK stability (no theta membership), Bessel order integrals (no actual source-preserving realization), atomwise Stein extension (numerically false all degrees). Do not advertise any of these as a producer. No route retired merely from numeric evidence.

Worktree has other tasks' changes: deleted/renamed CCMRestrictedWeilPoleDiagonalSharpConstant, new PoleBoundaryLogSharpConstant, chronological tensor modules, Euler-deletion research. Preserve them. No commit/push. Goal was paused when inspected; RH remains unproved.