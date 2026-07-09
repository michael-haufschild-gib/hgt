# Remote RH Defect Principle

- **ID:** remote-rh-defect-principle
- **Stage:** 0-backlog
- **Type:** CANDIDATE / CONJECTURE
- **Source:** user prompt, 2026-07-09; `../../door/G5-unitarity-gatekeeper.md`;
  `rh-landscape-proof-gate.md`; `../2-fully-proven/not-new/phase-cancellation-crux.md`;
  `../3-formalized/seam-collision-mechanism.md`;
  `../3-formalized/krein-inertia-equals-deck-charge.md`
- **Statement:** `[CONJECTURE]` If RH is false in the HGT/G5 language, the falsifying zero is a finite
  off-line seam defect, but its non-mirror certificate lives at an escaping source scale. For an off-line
  partner `rho = 1/2 - a + i gamma` with `a > 0`, the natural finite-degree visibility scale is
  `N_vis(rho) ~ gamma^2 / a`: large height and small lateral displacement both delay the first faithful
  finite certificate. Thus the right reading of "beyond computation" is not a zero at infinity; it is a
  negative square whose witness degree/window can escape every fixed finite probe.

## Goal

Turn the user's "a counterexample must be huge" intuition into a source-side, constraint-compatible
object. The target is not to search for an off-line zero. The target is to define a monotone visibility
scale for a possible `kappa_- > 0` defect and prove either:

1. a source-built lower bound excluding every defect at every visibility scale, or
2. a sharp nonselection theorem showing that any finite source probe can be matched while planting a
   defect with larger `N_vis`.

## Bridge Facts Already Available

`[BRIDGE]` Li/Bombieri-Lagarias visibility scale. For `rho = 1/2 - a + i gamma`,

`|1 - 1/rho|^2 = 1 + 2a / (gamma^2 + (1/2 - a)^2)`.

Hence `log |1 - 1/rho| ~ a / gamma^2` when `gamma` is large and `a` is not comparable to `gamma`.
The off-line term becomes visible in finite Li/Markov degree only when

`n log |1 - 1/rho| = O(1)`,

so the natural delay scale is `n ~ gamma^2 / a`, with extra logarithmic or phase overhead before it
dominates a smooth positive baseline. This is a bridge calculation, not new HGT content.

`[BRIDGE]` Local curvature window. The existing phase-cancellation card computes the off-line quartet's
curvature contribution as positive on `|t - gamma| < a`. Thus a zero with large `gamma` and tiny `a`
is vertically remote and transversely narrow at the same time.

`[PROVED]` In the finite seam model, an off-line pair gives a negative Krein direction, and
`kappa_-` equals the off-line count in the formalized carrier cards. This card does not reprove that.

## Attack

- This does **not** prove that the first false-RH zero must be huge. Existing finite verification only
  gives a finite lower bound; mathematics alone does not impose a current numeric height.
- This does **not** place a zero "beyond infinity." A false RH zero is a finite complex zero. What can
  escape is the certificate scale in a chosen source chart.
- This is not a computational search plan. If a finite zero is known approximately, interval methods can
  certify it. The issue is blind discovery by finite probes.
- If the all-order seam-log Markov/Hankel tower is already source-built, a real negative square has some
  finite polynomial witness. Therefore "remote" means the first witness degree may exceed every fixed
  prior bound, not that no finite witness exists.
- Novelty risk: the `gamma^2/a` estimate is classical Li-criterion bridge material. Native content begins
  only if `N_vis` becomes a source-built monotone invariant of the polarized seam, not a zero-fed
  parameter.

## Approach

Define the remote-defect scale

`N_vis(rho) := ceil((gamma^2 + (1/2 - a)^2) / a)`

for a left-side off-line partner `rho = 1/2 - a + i gamma`.

Then build one of two source-facing results:

- `[CONJECTURE]` Nonselection direction: for every finite source-probe bound `N`, there is a polarized
  fake matching the source probes through degree `N` while carrying an off-line quartet with
  `N_vis > N`.
- `[CONJECTURE]` Exclusion direction: the actual completed Euler/Gamma/FE object has a source-built
  monotone that forbids `kappa_- > 0` at all `N_vis`.

The first direction extends the existing finite-codimension nonselection guardrails. The second is the
G5 source theorem and must not be stated as `kappa_- = 0` unless the source monotone is built first.

## Gates

- [x] 0 -> 1 candidate shape: finite zero / escaping certificate distinction; `N_vis` order parameter;
  attacks listed
- [ ] 1 -> 2 fully-proven: prove a nonselection theorem with prescribed `N_vis > N`, or prove a
  source-built monotone excluding all defects
- [ ] 2 -> 3 formalized: isolate the bridge estimate and finite nonselection lemma in Lean
- [ ] 3 -> 4 publication-ready

## Log

- 2026-07-09 - created from user prompt: false-RH counterexample as remote defect, not literal infinity.
