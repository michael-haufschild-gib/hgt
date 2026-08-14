2026-08-14 Lean frontier advance for universal quantum recurrence paper.

New verified modules:
- RHTower/FiniteGridChoiRayCap.lean: exact ZMod phase-grid Choi embedding; arbitrary normalized ray cap in full d^2 Choi Hilbert space is contained in one translated coherence cap; finite dictionary cardinal bound.
- RHTower/PrimeTorsionCircuitRayPolygon.lean: if prime p, 2n<p, 0≤epsilon<1/2, and ((p-1)|Y|) n! d^(-n) < sqrt(1-4epsilon^2)^(2n), then one q has every nonzero scalar multiple >epsilon in pure trace distance from every arbitrary normalized target.
- RHTower/PrimeTorsionAutonomousCircuitPolygon.lean: strict complete polygon plus p-return is a nonempty open projective target; maximal projective phase flow hits it syndetically. Same fixed spectrum shadows all nonidentity vertices at a.val*tau and returns within arbitrary rho>0 at p*tau. No quantitative Diophantine/min-gap premise.
- RHTower/PauliLocalPrimeTorsionCircuitPolygonLaw.lean: specializes to generic ordinary bounded-weight Pauli Hamiltonians and composes permanent same-Hamiltonian two-query separation above exact Haar benchmark at every real time.

All four wired into RHTower.lean. Scoped lake builds succeeded for final modules. #print axioms reports only propext, Classical.choice, Quot.sound. No sorry/admit/axiom/opaque/unsafe. Whole-corpus formal lint still fails only on unrelated concurrent unwired modules; these four imports are reachable.

Stage-3 cards:
- prime-torsion-circuit-ray-polygon-law.md
- prime-torsion-autonomous-circuit-polygon-law.md
- pauli-local-prime-torsion-circuit-polygon-law.md

Remaining actual frontier: formalize bounded-dependence trace-monoid/heap dictionary cardinal enough for Brown-scale depth; then first-onset growth from time zero. Late autonomous hard polygons, ordinary local-H instantiation, return endpoint, complete circuit union, and permanent non-Haar separation are now closed.