# Hawking–Teukolsky minimal FE–Schwarz cubic resonance (2026-08-24)

Authoritative formal file:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo.lean`.

New exact results:
- Quadratic output from any two positive-branch Xi BM QNMs or real-field partners reaches neither plus nor minus Xi QNM branch.
- Cubic negative-branch matching forces `n0=n1+n2+n3+1` and `Σ Re ρj=2`.
- Every FE–Schwarz quartet is exactly resonant:
  `ω+_{n1}(Cq)+ω+_{n2}(Rq)+ω+_{n3}(RCq)=ω-_{n1+n2+n3+1}(q)`.
- Hawking-specific mechanism is affine, not generic group/KMS: four orbit angular momenta satisfy `κ(q)+κ(Cq)+κ(Rq)+κ(RCq)=i`; equivalently other three sum to `-κ(q)+i`. BM decay offsets convert this one thermal unit into one overtone step.
- Orbit is closed under physical real-field frequency involution:
  `ω+_n(Cq)=-conj(ω+_n(q))` and `ω+_n(Rq)=-conj(ω+_n(RCq))`.
- Reflected and conjugated source spectral sectors collide iff `Re ρ(q)=1/2`. Thus resonant process needs two distinct real QNM sectors off line and collapses to one real sector on line.

Lean checks:
- Target compiled.
- New declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.
- Scratch files removed.
- Formal lint reached only pre-existing unrelated umbrella error: `HTGeometry.SecondOrderConstraintDescent` unreachable.

Hostile audit:
- Prior same-sector AIME source is not actual cross-branch frequency incidence; it is a self-energy component.
- Existing completed triple-Eisenstein scalar vertex is only a quadratic exchange angular kernel, not full gravitational cubic response.
- Remaining coefficient must be full tree-level chiral four-graviton return:
  contact N3 plus all N2–Green–N2 exchange channels, evaluated in FE–Schwarz MHV quartet.
- Exact open core: prove this coefficient nonzero for tilted quartet, or classify its cancellation divisor. Any nonzero off-line resonance is genuine cross-sector mixing; on-line resonance is sector-collapsed.
