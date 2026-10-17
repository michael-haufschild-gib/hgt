# Exact infinite-edge logarithmic path congestion

- **ID:** infinite-edge-logarithmic-path-congestion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** A constructed diffuse-plus-countable-line edge measure admits
  exact transport from rough logarithmic Sobolev derivative energy to jump energy
  plus nonnegative edge slack, and controls the integrated nodal pairing.

## Exact theorem

For e=(h,u), let a=min(u,u+h), b=max(u,u+h), R=exp b−exp a, and
P(e,y)=R1_(a,b](y). Construct κ as weighted Lebesgue measure on h>0 plus
a countable sum of weighted Lebesgue measures pushed onto prescribed lag lines.
For actual q∈L2(R), set F(t)=∫₀ᵗq and f(x)=F(exp x). Define

    K(y)=∫P(e,y)dκ(e),
    B(e)=R∫_(exp a)^(exp b)q(t)²dt,
    J(e)=|f(u+h)−f(u)|²,       S(e)=B(e)−J(e)≥0.

Every B(e) is finite. With nonnegative extended integrals,

    ∫K(y)exp(−y)|f'(y)|²dy = ∫J(e)dκ(e)+∫S(e)dκ(e).

This is an addition identity even when totals diverge. The constructor proves
s-finiteness; joint kernel measurability and actual derivative transport are proved.
No energy-integrability or finite truncation premise occurs. The exact diffuse and
all-line expansions of J-energy and K are formalized. Four times the integrated
opposite-sign pairing of c+f is bounded by J-energy for every real c.

## Proof and audit

Paper: `docs/reports/BiScaleUncertainty/ContinuumPathCongestion.md`.
Detailed evidence: `docs/reports/BiScaleUncertainty/ContinuumCoprimeShear-FACTS.md`,
package 3. Namespace: `GaloisForLFunctions.BiScaleUncertainty.PathCongestion`.

- `LogarithmicPathKernel.lean`: 22 public theorems.
- `MixedEdgePathCongestion.lean`: 12 public theorems and 3 measure instances.
- Both final direct `lake --old env lean` checks passed without diagnostics.
- All 37 public theorem/instance axiom reports contain only `propext`,
  `Classical.choice`, `Quot.sound`, including their private dependencies.
- Umbrella imports and generated indexes updated; whitespace check passed.
- Global lint reports six unrelated concurrent missing imports, listed in the ledger.

## Significance and boundary

One contribution, bringing the active goal to 3/100. This removes the finite-edge
restriction from the rough-state jump/nodal comparison for the intended mixed
measure geometry. The underlying path-comparison principle is classical; no
external novelty claim for Cauchy–Schwarz or Tonelli.

A bounded congestion kernel and source-mass membership are still needed for a
finite graph-domain theorem. No unitary affine or application-specific spectral
conclusion is claimed. Next candidate: construct compact-source mixed weights
and exploit physical resistance to cancel the singular diffuse lag factor.

The compact-source case is now certified in `compact-source-graph-admission.md`,
including finite weighted source mass. General kernels and closed-operator
identification remain separate obligations.
