# RP72 — Nonzero causal mass correction cannot retain the native coprime budget

- **ID:** rp72-causal-mass-compensation-budget
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** Route RP; rp-joint-coprime-native-coercivity-2026-10-04 in 1-in-progress.
- **Statement tested:** Replace the native log profile a by the causal residual a+lambda*m, with nonzero lambda and m(T)=integral_0^T a, while retaining admission of its complete critical coprime source at damping in [0,1].

## Exact killing mechanism

The primitive has total mass D/3>0, so the residual has total mass lambda*D/3. Its full dilation source has leading term `(lambda*D/3)*exp(T)`. The complete coprime source has leading term `(lambda*D/3)^2*(6/pi^2)*exp(T)`, retaining every pair. Every nonzero coefficient therefore destroys the relevant combined-source admission.

Lean: `routePNativeMassCoprimeSource_integrable_iff_zero` in RoutePNativeMassCoprimeAdmission. The original source is exactly the coefficient-zero member, not a replacement toy source.

## Strongest positive survivor

`routePNativeMassCoprimeSource_asymptotic` proves the exact strictly positive source coefficient for every nonzero lambda. `routePNativeMassCompensatedProfile_energy` retains the complete native finite-window square and the nonnegative terminal mass square. The admission boundary is exactly lambda=0 for every damping in [0,1].

## New insight

The signed first moment, previously available as a boundary jet, becomes an actual positive pole coefficient after causal mass compensation. Compensating the finite energy boundary therefore changes the complete arithmetic source's admission domain. Original source admission cannot be copied to this residual family.

## Paper and Lean status

Dependency-closed paper proof and five audited, umbrella-wired leaves are recorded in 3-formalized/rp-causal-mass-compensation-coprime-pole-2026-10-04.md. All16 new public theorems passed the combined axiom audit37812, with only standard Lean axioms. Global lint18348 remains failing with unrelated unreachable-module diagnostics; no global pass is claimed.

## What remains live

This retires only the single causal residual replacement. The cutoff-dependent zero-total-mass completions and the original native joint positive-damping energy problem remain live. Signed high-LCM cancellation and both physical history debts remain unpaid. This is neither an RH proof nor an RH falsification.
