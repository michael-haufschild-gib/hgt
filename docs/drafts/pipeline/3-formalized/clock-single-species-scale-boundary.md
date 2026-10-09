# Exact single-species scale boundary

- **ID:** clock-single-species-scale-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / corrected broad claim
- **Source:** `ConformalClockScaleBlindness.lean`, `ClockLocalTwoSpecies.lean`.
- **Statement:** For independent algebraic defect channels, a single clock potential determines
  scale exactly when the conjugation weight is zero and calibrated squared mass is nonzero.

## Context and attack

The existing `exists_ne_scaleDefect_with_eq_conformalPotentialData` proves that the PAIR
(scale, Laplace defect) is not identifiable for any weight and mass. Its prose claims
that neither coordinate is determined, but the weight-zero branch changes only the
Laplace defect. At weight zero and nonzero mass the data are mass times scale, so scale
is identifiable. The Lean theorem is correct; its prose overstates the conclusion.

Corpus search `single species zero weight conformal scale` returned the already-proved
`conformalPotential_weight_zero` and `conformalDimensionWeight_two` in
`ClockLocalTwoSpecies`. No new two-dimensional conformal effect is claimed.
Search completed with source-only candidates, unmeasured semantic coverage and an older
coverage snapshot. The exact source formulas, not novelty inferred from search absence,
drive this correction.

External check: Alinea–Chua, https://arxiv.org/abs/2208.10953 concerns classical
Klein–Gordon transformation laws; its abstract is adjacent context, not evidence for
this exact classification. The classification follows directly from the installed
corpus formula. Verdict: **FALSE** for universal single-species scale blindness;
**BRIDGE / correction** for the exact classification, no external novelty claim.

## Paper proof [PROVED HERE]

Write P(w,m,s,L,G)=m*s-w*L-w²*G, with G fixed and L freely varying.
If w=0, equality of P is equality of m*s; it determines s iff m is nonzero.
If w is nonzero, then for every prescribed s and data value v, choosing
L=(m*s-w²*G-v)/w gives P=v. Thus every scale is compatible, even within positive
scales (choose s=1 and s=2). If w=m=0, P=0 independently of scale.
These three cases exhaust all parameters and prove the exact criterion.

Positive survivor: complete scale identifiability classification and exact all-value
fiber criterion. These concern independent algebraic channels. They do not construct
two conformal factors whose actual derivatives realize arbitrary L and G.

## Working plan

- [x] Inspect original proof and search stronger/overlapping corpus facts.
- [x] Complete exact paper classification and audit algebraic versus geometric meaning.
- [x] Formalize unconditional iff statements and correct original prose.
- [x] Direct Lean, axiom, import, index and lint audits; then close this increment.

## Log

- 2026-10-08 — discovered weight-zero exception during follow-up to continuous closure
  classification; all original proof statements preserved.
- 2026-10-08 — `ConformalClockSingleSpeciesBoundary.lean` directly compiled via
  `lake --old env lean -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/ConformalClockSingleSpeciesBoundary.olean GaloisForLFunctions/HTGeometry/ConformalClockSingleSpeciesBoundary.lean`:
  exit 0, no diagnostics. Corrected original `ConformalClockScaleBlindness.lean` also passed
  direct `lake --old env lean`, exit 0. All three imported theorem axiom reports contain
  only `propext`, `Classical.choice`, `Quot.sound`.
  Unique umbrella import and all three generated API rows verified; index exited 0.
  Global lint exited 1 on seven unrelated unreachable modules: the six listed on
  `clock-continuous-probe-closure` plus `XiGaussianOneSidedIdentityRH`.
  No owned finding or proof-debt error. Scoped `git diff --check` passed.

## No-go closure

- **Killing mechanism:** at w=0, m nonzero, P=m*s, so equality of P forces equality of s.
  The old theorem's distinct-pair witness changes only L in that branch.
- **Strongest positive survivor:** complete single-species scale classification, exact
  Laplace-channel data fiber, and positive-scale ambiguity at precisely w nonzero or m=0.
- **Lean:** `conformalPotentialData_scale_identifiable_iff`,
  `conformalPotentialData_laplace_fiber_iff`,
  `conformalPotentialData_positive_scale_ambiguity_iff`.
- **Meaning:** source theorem proofs were sound; interpretation needed correction. Independent
  algebraic channel ambiguity does not prove an ambiguity between actual conformal geometries.
- **Next cycle:** `clock-matrix-scale-projective-recovery` tests whether existing projective
  matrix tomography removes the claimed procedural need to diagonalize mixed species.
