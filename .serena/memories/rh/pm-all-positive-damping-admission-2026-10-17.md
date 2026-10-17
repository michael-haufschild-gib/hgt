# PM: original forced response admitted for every positive damping

2026-10-17. Positive contribution completed for PM under the active cross-route goal. Objective attachment: `/Users/michael/.codex/attachments/96420293-cf9b-451e-9b1d-1fcd84b70704/pasted-text-1.txt`. Read it before continuing. Goal remains active: every one of 21 live routes and 23 candidates needs its own significant positive obstacle-removing result. Pick a previously unworked route/candidate next turn; PM has now been worked. Earlier XN, HF, IRK, EGC, OWU, RN attempts did not earn strict positive-contribution credit. Do not equate their formal results with completion.

## Exact proved delta

`RHTower.D4BMForcedSmallDamping.causalJointForcedResponse_memLp_pos` proves for every actual `XiZeroCopy q`, branch, amplitude, and real k>0:
`MemLp (fun t => expRay (k:ℂ) t • D4BMJointSource.causalJointForcedResponse q branch amp t) 2 (volume.restrict (Ioi 0))`.
Old admission needed `principalKernelGrowth q < k`. The exact original response now has arbitrarily small positive damping admission. This is the credited endpoint, not merely an intermediate bound.

Same namespace:
- `causalJointFrequencyResponse_differentiableAt_pos`: original frequency response holomorphic throughout Re w>0.
- `causalJointForcedResponse_integrable_pos`: original response has an absolute Bochner Laplace integral for every Re w>0.
- `causalJointForcedResponse_laplace_pos`: that integral equals the original `causalJointFrequencyResponse`.
No RH assumption, added analytic premise, or replaced source/response. All three principal exponents and amplitudes, cutoff commutators, and native square remainder retained. Positivity conditions specify domains only.

## Mechanism and files

1. `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPrincipalReflectionAdmission.lean` (4 public theorems). Legendre ODE gives P_{-1}=1, hence exact normalized height mean=1. This bounds the actual Legendre derivative throughout 0≤Re m≤2. Direct/reflected invariants differ by ≤2; single-cone invariant lies in [1,3]. Complete reflected Dirichlet causal kernel is uniformly bounded.
2. `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPrincipalSmallDamping.lean` (5 public theorems). Reflect the actual odd source before taking norms. Literal retarded response grows polynomially; finite propagation controls radial L2. Exact native/principal identification transfers to every physical channel. Complete original cusp forcing is Laplace L1 for all Re w>0.
3. `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMForcedSmallDamping.lean` (4 public theorems). Positive joint resolvent and admitted source give shifted Cauchy-Hardy data for every c>0. Laplace uniqueness identifies the shifted construction with the existing forced response. Taking c=k/2 proves original L2 admission for every k>0.
All three wired into `formal/GaloisForLFunctions/RHTower.lean`.

Full dependency-closed paper proof, conjecture loop, exact criterion assessment, and validation:
`docs/drafts/pipeline/3-formalized/pm-small-damping-source-admission-2026-10-17.md`.
Moved from `1-in-progress`. Frontier map was not edited by this task; concurrent sessions have unrelated changes, including that file. Preserve them.

## Verification

All three final direct builds passed with no warnings: `lake --old env lean -j1 -o .lake/build/lib/lean/<module>.olean <module>.lean` from `formal/`.
All 13 public theorem axiom audits passed from a separate /tmp import: only `propext`, `Classical.choice`, `Quot.sound`.
`scripts/formal_tools.py lint` exited 0, printed `formal lint passed`; repository large-file warnings remain. No full/umbrella builds, no heartbeat increases, no numerical experiments, no web or external novelty check. Only one owned foreground Lean process at a time. All build/audit/lint processes exited.

## Limits

No k=0 admission, uniform zero-damping limit, Haar approximation, optical magnitude, ordered cap limit, all-divisor extinction, or RH claim. These remain separate PM obstacles. Overall goal is incomplete.

## Workflow lessons

Use the documented research command directly. Second targeted PM deep search completed with partial=false; first broad query was partial due malformed judge output. No background-service interference.
Reuse `HTGeometry.SmoothAngularAverage.average_hasDerivAt` to avoid expensive ad hoc differentiated compact-integral proofs.
For nested ContinuousAt composition, specify `(f := fun y => max 1 (invariant h x y)) (x := y)`; otherwise Lean may infer `f := max 1` prematurely.
Use `(f := ...)` in `norm_integral_le_of_norm_le_const` and explicit `(a := 0) (b := T)` for interval bounds.
Use `.congr` for integrability transports when inferred ContinuousENorm instances differ.
Do not disable `RCLike.innerProductSpace` in the forced-response module: it needs complex Hilbert instances.
Use `MeasurableSet.univ`, not nonexistent `measurableSet_univ`; use the existing physical-green-band scalar Laplace uniqueness pattern.
Serena symbol operations ignore Lean in this repo, so scoped read-before-edit patches are necessary.
