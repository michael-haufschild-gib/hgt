# WP05 — Produce a settled phase for the actual spectral measure

Status: open detection route. Mode: paper research, then Lean. Read [shared contract](/Users/michael/Documents/code/hgt/docs/reports/weil-work/README.md).

## Single objective

Derive the inputs of `RHTower.WeilSpectral.vonMangoldt_and_riemannHypothesis_of_settled_atomic_phase` from full positivity, rather than assuming them. The exact constant-phase version asks for:

- Nonnegative weights `c_j`, ordinates `t_j ≥ 1` tending to infinity, and `Σ c_j/t_j² < ∞`.
- The theorem's **exact Poisson-transform representation** of `boundaryMeasure hW` by the symmetric atoms at `±t_j`.
- Constants `θ, δ, C, Y₁`, with `δ > 0`, such that for every `Y ≥ Y₁`,

\[
\int_Y^{2Y}|e^{2\pi i S(y)}-e^{2\pi i\theta}|\,dy
\le C Y^{1-\delta},\qquad
S(y)=\sum_{t_j<y}c_j.
\]

An alternative is to produce all hypotheses of the existing almost-periodic settled-phase receiver, with its exact coefficient summability and arithmetic nonresonance conditions. Choose one version as the package's active target; do not pursue two unrelated proof projects.

## Starting evidence

- [Constant-phase receiver](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeSettledAtomicPhase.lean:61) and [almost-periodic receiver](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilConeSettledAtomicPhase.lean:179).
- [Exact phase-sum convention](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilFractionalMassTailRigidity.lean:566): preserve strict ordinate cutoff and mass normalization.
- [Power-growth fractional-mass rigidity source](/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilAbelianTwistPowerRigidity.lean:685): search located a pre-existing receiver for sublinear-power fractional mass. Verify its full statement and installed export before reuse; it was not one of the audit's 54 checked declarations.
- [Current Bohr/phase research card](/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/bohr-route-detection.md): distinguish formal results, paper mechanisms and still-open linear-growth cases.

## First research milestone

Identify one new source-derived estimate on the cumulative phase or fractional mass, and prove it for an explicitly defined spectral class beyond the refreshed corpus's existing rigidity hypotheses. State whether the estimate is pointwise, mean, Abelian or Cesàro, then prove any transfer to the receiver's dyadic `L¹` estimate.

If atomicity or the support restriction is not yet available, keep that as a separate unpaid premise and prove a substantive phase lemma conditional on it. Do not manufacture a representation by discarding diffuse mass or low ordinates. Any extension of the receiver must account for those components exactly.

## Exclusions and traps

- Ordinary almost periodicity or bounded phase does not by itself imply convergence to one phase in the required mean with a power saving.
- Rationally resonant frequencies are explicitly restricted in the AP receiver. Inspect the exact condition rather than replacing it by a generic “nonzero frequency” assumption.
- Finite fractional mass, summable tails and sublinear-power fractional-mass rigidity already have corpus treatments. Producing those properties from the arithmetic system could be new; reproving a receiver under the same assumptions is not.
- A cumulative counting asymptotic need not control its exponential phase. Preserve signed cancellation rather than inserting unjustified absolute bounds.
- The theorem concludes `λ = Λ`; proving it for every full-positive λ is stronger than general RH detection. A scoped failure does not refute the weaker existence-to-RH route.

## Search entry points

```sh
scripts/formal_tools.py research 'settled atomic phase' --module Weil
scripts/formal_tools.py research 'fractional mass power growth' --module Weil
scripts/formal_tools.py research 'arithmetic phase settlement linear mass rational resonance' --mode deep --budget-seconds 300
```

## Completion and handoff

`CLOSED` requires all representation and settlement hypotheses from arbitrary `hW`, followed by the existing rigidity theorem. A new phase estimate under an unproduced spectral condition is `CONDITIONAL ADVANCE`. Give WP01 or WP04 the exact missing property, not a vague request for “more regularity.” If a phase mechanism has a sharp failure threshold, prove and formalize its positive range.

Owned result directory: `/Users/michael/Documents/code/hgt/docs/reports/weil-work/results/05-settled-phase/`.

Owned initial card: `/Users/michael/Documents/code/hgt/docs/drafts/pipeline/1-in-progress/weil-work-05-settled-phase.md`.

Reserved new Lean scope: `/Users/michael/Documents/code/hgt/formal/GaloisForLFunctions/RHTower/WeilWorkSettledPhase*.lean`. Existing modules are read-only. Output `RESULT.md`, `PROOF.md`, `EVIDENCE.md`.
