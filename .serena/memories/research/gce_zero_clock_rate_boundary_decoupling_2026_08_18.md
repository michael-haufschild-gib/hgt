# G-CE zero-clock rate / boundary transport decoupling (2026-08-18)

Formal result: `formal/GaloisForLFunctions/RHTower/MobiusGammaXiMarkedClockBoundaryRateDecoupling.lean`.

Core theorem `exists_mobiusGammaXiMarkedZeroClockRate_boundaryTransport_debt` combines:
- canonical zero-clock marked odd-port quotient identically zero for every source depth and head;
- finite positive self-adjoint G-CE realization;
- operator-norm and complete boundary-column transport;
- base-node source response converging to critical coefficient `d`;
- budget converging to `4 + |d|²`;
- `d = 0 ↔ RiemannHypothesis`.

Reason: at u=0, clock damping is identity, hence pure commutator odd port vanishes exactly; squarefree boundary overlap equals 1. But every canonical G-CE head includes u=0 and singular response there equals d. Therefore requested moving-boundary little-oh rate is unconditionally satisfied yet RH-blind. Arbitrary schedule acceleration cannot fix coordinate mismatch.

Surviving open core: construct lawful affine pointed producer before scalarization with nonzero zero-clock completed prime–polar–Gamma charge plus positive-clock commutator jet. It may not import `continuedXiAntiCausalWardResponse`, Xi divisor, or universal opposite controller; those would encode desired cancellation.

Paper card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/ccm/g-ce-zero-clock-rate-boundary-decoupling.md`.
Verification: target `lake env lean`, target-only `lake build GaloisForLFunctions.RHTower.MobiusGammaXiMarkedClockBoundaryRateDecoupling`, axiom audit only `propext`, `Classical.choice`, `Quot.sound`.