# Finite Dirichlet carrier Perron mass discharge

- **ID:** dirichlet-poly-perron-mass
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** formal Perron carrier interface audit
- **Statement:** `[PROVED IN LEAN]` Every finite Dirichlet carrier constructs its coefficient sequence, global `LSeries` representation, flank mass, horizontal mass, horizontal and boundary escape, strip mass, boundary charge, quiet-flank bounds, and right-edge Perron bound without Prop-valued interface inputs.

## Goal
Make the Perron interface stack actually inhabited by a concrete globally differentiable carrier,
and push its elementary finite structure through every compatible consumer.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete proof, `[PROVED IN LEAN]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `dirichletPoly_hasVariablePerronBoundaryCharge`, exact module builds green, axiom audit and formal lint pass
- [ ] 3 → 4  publication-ready: not applicable to infrastructure classified as not-new

## Proof
On `Re s ≥ -M`, termwise complex-power norms give
`|dirichletPoly N s| ≤ Σ_{1≤n≤N} n^M`.  Domination by `(1+t²)⁻¹` constructs both weighted mass
interfaces.  The coefficient sequence is the indicator of `Finset.Icc 1 N`; finite support proves
summability everywhere, and its `LSeries` reduces exactly to `dirichletPoly N`.

The horizontal mass constructs pointwise and variable horizontal escape, hence pointwise and
variable boundary escape.  Together with the flank mass it constructs `HasPerronStripMassAt`,
`HasPerronBoundaryChargeAt`, both quiet-flank coefficient interfaces, and the right-edge integral
bound.  No named Prop-valued producer remains in those concrete theorem signatures.

This is formal analytic infrastructure rather than new mathematical knowledge.

## Log
- 2026-07-10 — Exact modules compile and build.  Axiom footprints are only `propext`,
  `Classical.choice`, and `Quot.sound`; project formal lint passes.
