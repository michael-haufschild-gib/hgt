# Signed prime–polar packet Gram transport

- **ID:** signed-prime-polar-packet-gram
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Scope:** Actual finite-window signed measure; arbitrary compact continuous sources.
- **Ledger:** `docs/reports/BiScaleUncertainty/SignedPrimePolarTransport-FACTS.md`

## Target

Construct P(u)=Σ Λ(n)/√n f(u+log n)−∫₀ᴸ 2cosh(t/2)f(u+t)dt.
Prove that Q=∫P² controls signed correlation increments by
|⟨ν,h(·+y)−h⟩|²≤2Q(h(0)−h(y)). Transfer this cancellation-sensitive
bound through annular averaging to the existing exact Chebyshev work identity.
No grid blindness, source derivative, assumed packet admissibility, or arithmetic
estimate may enter the theorem interface.

## Dependency-closed proof plan

- [x] Corpus search: finite signed Gram packets exist; continuum polar packet gap remains.
- [x] Critique: unsigned estimates destroy cross terms; scalar support stabilization
  does not prove packet-energy stabilization as the cutoff grows.
- [ ] Construct continuous compact polar packet and signed packet.
- [ ] Prove mixed correlation representation by justified Fubini.
- [ ] Apply source translation chord identity and Cauchy–Schwarz.
- [ ] Transfer through annular averaging and reciprocal-weight Young inequality.
- [ ] Record exact mathematical boundary, paper proof, Lean audit, umbrella wiring.

## Distinctness and limits

This package concerns arithmetic–polar cancellation inside a Hilbert norm.
Finite discrete Gram results alone do not construct its continuum component.
No cutoff-uniform bound is claimed. A full-half-line scalar extension remains a
separate outstanding obligation in the parent program and is not counted here.
