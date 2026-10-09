# Exact noise geometry for projective matrix clocks

- **ID:** clock-noisy-projective-matrix-recovery
- **Stage:** 3-formalized
- **Type:** PROVED CORPUS BRIDGE / exact noisy feasible-value classification
- **Source:** `ProjectiveWignerSmithTomography`, `ConformalClockMatrixRecovery`,
  `ClockGapEnvelopeRecovery`.
- **Statement:** Projective-panel noise between real scales of a known mass matrix
  equals `|s1-s2| * norm(projectiveDelayPanel M)` exactly, independently of both
  common scalar defects. Consequently a Lipschitz scale-error field has a feasible
  anchor a under uniform panel-noise budget epsilon iff every x satisfies
  `g(x)|a| <= epsilon + g(x)L dist(x,p)`, where g(x) is that panel norm.

## Paper proof [PROVED HERE]

Each existing reporter is complex-linear in the normalized matrix, and reference
normalization is complex-linear as well. Write J for the existing projective panel.
Then `J(s1 M+d1 I)-J(s2 M+d2 I)=(s1-s2)J(M)`. The norm on the finite complex
reporter space therefore gives the stated exact identity. This uses the fixed
corpus panel's maximum norm; no basis-invariant spectral-gap assertion is intended.
The weight g vanishes exactly when M is scalar, by the existing exact scalar-fiber
classification. Single-channel matrices yield an empty panel and weight zero.

For a fixed reference scale b(x), let u(x)=other(x)-b(x). The panel-noise constraint
is precisely g(x)|u(x)|<=epsilon, even if the reference and competing scalar defects
vary independently with x. Apply the established weighted Lipschitz feasibility iff.
For sufficiency take the existing signed distance tent u and set other=b+u.
No regularity of M, b, or either defect is assumed. The classified regularity budget
belongs to the scale difference; continuity alone does not provide that budget.

## Corpus audit

`research "projective delay panel norm scale noise" --no-refresh --json` returned
the existing projective panel, scalar-defect quotient and exact scale-observation
interfaces, but no matching norm-factorization or noisy feasible-anchor theorem.
Their actual Lean definitions and source statements were inspected. partial=false;
source-only freshness and unmeasured semantic coverage. Only Lean entries were read.
No web search or external reading; no external-novelty claim.

## Plan

- [x] Inspect actual reporter definitions and scalar-fiber interfaces; complete paper proof.
- [x] Formalize panel homogeneity, norm factorization and exact zero-weight boundary.
- [x] Formalize full noisy scale-error feasible-anchor iff and realizing scale shift.
- [x] Direct leaves, all-declaration axioms, umbrellas, index and lint audits.

## Final Lean audit (2026-10-08)

`formal/GaloisForLFunctions/HTGeometry/ConformalClockNoisyMatrixRecovery.lean` proves
five theorems: `projectiveDelayPanel_smul`, `projectiveDelayPanel_zero`,
`projectiveDelayPanel_norm_zero_iff_scalar`, `projectiveMixedClock_noise_exact`,
and `noisyProjectiveClock_feasible_iff`. The final direct command
`lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/ConformalClockNoisyMatrixRecovery.olean GaloisForLFunctions/HTGeometry/ConformalClockNoisyMatrixRecovery.lean`
passed with no diagnostics. Imported axiom checks for all five reported only
`propext`, `Classical.choice`, and `Quot.sound`. The final existence proof makes
the NNReal sensitivity coercion explicit; no auxiliary source estimate is assumed.

Umbrella integration occurs exactly once, index regeneration passed, and all five
API rows are present. No forbidden declaration, heartbeat change, trailing
whitespace, full build or numerical experiment was introduced. Global lint has
the seven unrelated unreachable modules listed in `clock-finite-window-gap-recovery.md`;
neither new leaf has a lint error. All owned `/tmp/hgt-window-gap*` scratch is cleaned
after recording the audit; unrelated work is untouched.

## Next constraint

The theorem classifies real competing scales. Strict positivity is not asserted.
`clock-positive-noisy-scale-feasibility.md` now proves the exact additional
positivity guard for a positive exponential reference scale, including an
exponential competing-scale receiver. The real-scale theorem remains unchanged.
