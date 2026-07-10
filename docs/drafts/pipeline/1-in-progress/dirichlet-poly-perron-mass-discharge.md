# Finite Dirichlet carrier Perron mass discharge

- **ID:** dirichlet-poly-perron-mass
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** formal Perron carrier interface audit
- **Statement:** `[PROVED IN LEAN, AUDIT PENDING]` Every finite Dirichlet carrier constructs its coefficient sequence, global `LSeries` representation, flank mass, horizontal mass, boundary escape, boundary charge, and right-edge Perron bound without Prop-valued interface inputs.

## Goal
Make the Perron interface stack actually inhabited by a concrete globally differentiable carrier,
and push its elementary finite structure through every compatible consumer.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `dirichletPoly_hasVariablePerronBoundaryCharge`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
On `Re s ≥ -M`, termwise complex-power norms give
`|dirichletPoly N s| ≤ Σ_{1≤n≤N} n^M`.  Domination by `(1+t²)⁻¹` constructs both weighted mass
interfaces.  The coefficient sequence is the indicator of `Finset.Icc 1 N`; finite support proves
summability everywhere, and its `LSeries` reduces exactly to `dirichletPoly N`.  Compose these
constructors into the boundary-charge and contour-integral consumers.

This is formal analytic infrastructure rather than a claim of new mathematical knowledge.

## Log
- 2026-07-10 — All claimed constructors and capstones compile in
  `RHTower/DirichletPolyPerronMass.lean`; generated-index, axiom, lint, and umbrella audits remain.
