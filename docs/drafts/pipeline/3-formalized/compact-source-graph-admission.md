# Compact-source mixed graph admission

- **ID:** compact-source-graph-admission
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every physical L² velocity has finite source mass, diffuse and
  arithmetic jump energy, integrated slack and nodal energy for the mixed graph
  constructed from an arbitrary continuous compact source and arbitrary finite
  nonnegative atom coefficients.

## Exact result

Let B be the radius of the actual source ψ. The singular resistance density
extends continuously as `2exp(u+h/2)/(1+exp(-h)) ψ(u)²ψ(u+h)²`. Its support
is compact. All atom lags `log(n+2)>2B` vanish. Total resistance mass C is
therefore finite and has an exact nonsingular integral plus finite-sum formula.
Congestion satisfies `K≤C 1_[-B,B]`, giving finite weighted derivative energy
for every actual L² velocity. The preceding exact path identity transfers this
to jump energy and slack; the nodal bound includes arbitrary added constants.
Continuity and compact support also prove weighted source-mass finiteness.

Paper: `docs/reports/BiScaleUncertainty/CompactSourceGraphAdmission.md`.
Namespace: `GaloisForLFunctions.BiScaleUncertainty.PathCongestion`.
Lean leaves: `CompactSourceResistanceMass.lean`, `CompactSourceGraphAdmission.lean`.

## Gates

- [x] Corpus audit and dependency-closed paper proof.
- [x] Both final direct leaf checks passed without diagnostics; normal `.olean` outputs.
- [x] All 40 public theorem/definition declarations audited: only `propext`,
  `Classical.choice`, `Quot.sound`. Main signatures have no analytic admission premise.
- [x] Umbrella wiring, all 32 theorem names in generated indexes, formal lint and whitespace check.

## Significance and boundary

One connected certified contribution, bringing the active goal to **4/100**.
This discharges finite-energy admission
for the actual compact-source mixed kernel without an assumed congestion bound
or atom-summability premise. Total edge mass may remain infinite. Closed-form
operator domains, spectral coercivity, and unitary affine actions are not proved.
Generic Sobolev-to-jump-domain admission is classical; no external novelty claim.

Detailed certificates and logs: `docs/reports/BiScaleUncertainty/ContinuumCoprimeShear-FACTS.md`,
package 4. Its variance-coercivity successor is now certified in
`compact-source-variance-coercivity.md`.
