# Route Q boundary hyperbolic plane (2026-08-16)

Lean-closed advance in `XiHurwitzOrientationBoundaryHyperbolicPlane.lean`:
- For exact null witnesses `b₊=(w+e)/2`, `b₋=(w-e)/2`, reflection exchanges them with minus sign, and `2‖b₊‖²=2‖b₋‖²=E`.
- Exact real-coordinate law: `xiWeilHilbertQuadratic (α b₊ + β b₋) = -αβ E`.
- Off RH (`E>0`): same-sign quadrant is negative, opposite-sign quadrant positive, coordinate axes complete null cone.
- For arbitrary separated packet reconstructions of both boundaries, scaled fusion energies converge to `-αβE`; same-sign fusions are eventually negative off RH and opposite-sign fusions eventually positive.

Universal principle: null source rays can have a decisive hyperbolic mixed defect invisible to diagonal positive-boundary approximation. Orientation target `w=b₊+b₋` is same-sign negative direction off RH. Any successful Q selector must retain transverse theta/prime–Gamma mixed incidence before closure; independent boundary saturation/diagonal energies cannot supply it.

Evidence: direct Lean and exact leaf build passed; umbrella import wired; axiom endpoints only `[propext, Classical.choice, Quot.sound]`; no umbrella/full build. Card: `docs/drafts/pipeline/3-formalized/route-q-boundary-hyperbolic-plane.md`.