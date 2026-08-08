# Polarized exchange-horizon geometry — hostile refinement (2026-08-08)

See `mem:research/polarized-exchange-horizon-geometry-2026-08-08`. Goal remains active; no Lean written or built.

## Stronger closed Stage-2 results
Card: docs/drafts/pipeline/2-fully-proven/polarized-exchange-horizon-geometry/rank-one-polarized-exchange-geometrizability.md

Beyond binary curvature:
- all ordinary higher-word defects have same common kernel as binary defects because H is invariant and restricted transports form a representation;
- D_theta=C_theta(2,2)=2^theta(1-2^theta)E12 is square-zero;
- theta!=0: ker D=im D=Re1, exchange homology zero, and D induces R^2/Re1 ~= Re1;
- theta=0: D=0 and exchange homology R^2;
- two-term exchange complex E_theta=[Q->L] is acyclic off horizon, so any source-first chain map with nonzero induced homology forces theta=0;
- generic chi over char-0 field: same; nonzero homology landing on any multiplicative generating set (primes suffice) forces chi trivial;
- for flat reciprocal lambda, prior-corpus Hermitian torsion tau=|lambda|^2 and anomaly a=1-tau satisfy a(mn)=a(m)+tau(m)a(n), and affine different gives curvature tau(m)(m-1)a(n)E12; inverse=adjoint iff a=0.
Exact arithmetic checks through words of arity 6 passed. File hygiene, unique tags, fences, UTF-8/control checks passed.

## Critical hostile correction
Direct identification of Gamma/co-Poisson/Sonin source-error syzygy with exchange/mate curvature is false by existing corpus audit: syzygy controls flat connection error while Hermitian nonmetricity survives.
Correct Stage-1 producer is two-stage:
  gr B_firsttrace --gr Phi_src--> gr B_Gamma/coP/Sonin --Psi_PE--> E_s=[Q--Dbar_s-->L].
Phi_src is existing open exact-couple morphism. Psi_PE is a bioriented/exact-couple lift of already-known finite scalar/Gamma torsion-to-mate data; its scalar boundary is fixed, not new. Composite must be homology-conservative after Xi Cartier base change.

New explanatory leverage:
- any nonzero conormal-error vector is a boundary off horizon, uniquely lifted from transverse quotient. This explains why nonzero vector/landing arguments fail.
- arithmetic must prove a nonzero quotient/homology class, not a vector.
- strict matrix higher arity stabilizes at binary; any later coherence loss is genuinely oriented/Gray-categorical.
- higher exchange-horizon topology uses descending H_x^(q) for oriented pasting diagrams. Full bioriented H^(infty) remains open.

Novelty boundary:
Prior: raw generic curvature/Bianchi, modular-cocycle RH selector, tau=|lambda|^2, 1-chi reduced defect, mate curvature/Gamma calibration, cyclic nonzero-quotient warning, Scott/Sierpinski methods.
Candidate-new: exchange-factorization meta-object; exact common kernel/image/quotient/homology classification; strict higher-word stabilization; calibrated paracyclic bridge; all-arity bioriented coherence spectrum; two-stage typed producer.

Physical analogy allowed only as consequence: off horizon Q->L is an isomorphism (no independent edge homology); at horizon contraction dies and edge modes survive. Not evidence for black holes/wormholes.

Exact next theorem:
construct finite source-normal partial-K exchange realization, Phi_src, categorical Psi_PE with forced scalar shadow, transverse/homology-conservative Cartier landing, coherent Stokes homotopies, and all-arity bioriented strictness.