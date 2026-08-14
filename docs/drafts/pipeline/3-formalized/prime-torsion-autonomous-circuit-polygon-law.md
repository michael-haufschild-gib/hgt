# Prime-torsion autonomous circuit-polygon law

- **ID:** `prime-torsion-autonomous-circuit-polygon-law`
- **Stage:** 3 -- formalized
- **Type:** THEOREM (Lean)
- **Extends:** `prime-torsion-circuit-ray-polygon-law.md`
- **Lean:** `RHTower/PrimeTorsionAutonomousCircuitPolygon.lean`

## Exact unconditional law

Fix a finite normalized target dictionary `Y`, a prime `p`, a replica order `n` with `2n<p`, a
resolution `0≤epsilon<1/2`, and a return tolerance `rho>0`.  Let
`energy : Fin (d+1) → ℝ` have maximal projective rank.  If

\[
 ((p-1)|Y|)\,n!\,(d+1)^{-n}
 < \left(\sqrt{1-4\epsilon^2}\right)^{2n},
\]

then there is a finite `L≥0` such that, after every starting time `A`, some base time
`tau∈[A,A+L]` has both properties:

1. for every nonzero `a∈ZMod p` and every target `y∈Y`, the projective Choi state at physical time
   `a.val * tau` is farther than `epsilon` from `y` in pure-state trace distance;
2. the same fixed spectral flow at physical time `p*tau` is within `rho` of the identity Choi ray.

Thus all `p-1` hard vertices and the return endpoint belong to one autonomous cycle of one fixed
time-independent spectrum.  The base times occur syndetically; no quantitative Diophantine rate,
randomness, mixing, design, or minimum spectral gap is assumed.

## Mechanism proved in Lean

- `zmodUnitAddCirclePhaseHom`: finite cyclic phases form an additive homomorphism into the physical
  additive circle.
- `fullUniformPhaseChoiDensity_eq_zeroAnchored`: the full Choi density erases exactly one common
  phase.
- `finiteGridProjectivePhase_mem_polygonTarget`: strict finite-grid hardness and `p`-torsion return
  supply one point of a stable open projective target.
- `maximallyProjective_complete_circuitPolygon_shadow_syndetic`: dense maximal-projective flow hits
  that complete finite-power target with bounded gaps.
- `maximallyProjective_exists_complete_circuitPolygon_of_replicaBudget`: the replica budget
  constructs the polygon and composes it with autonomous shadowing in one theorem.

## Frontier after closure

Autonomous late-time shadowing is no longer an open obligation.  Remaining paper-critical work:

1. instantiate the finite dictionary by dependency-normalized local circuit heaps at Brown-scale
   depth;
2. prove first-onset growth from time zero.  Current theorem gives late recurrent hard polygons,
   not monotonicity or first hitting time.

The downstream `pauli-local-prime-torsion-circuit-polygon-law.md` closes ordinary bounded-weight
Pauli-Hamiltonian instantiation and permanent same-Hamiltonian Haar separation.

## Gates

- [x] arbitrary full-space normalized circuit rays
- [x] complete `p-1` vertex union
- [x] return endpoint in same autonomous cycle
- [x] one fixed time-independent spectrum
- [x] arbitrarily late and syndetic base times
- [x] no quantitative Diophantine or gap hypothesis
- [x] no computation and no unproved declaration
- [x] RHTower umbrella import
- [x] ordinary local-Hamiltonian plus permanent Haar composition (downstream)
- [ ] Brown-scale heap dictionary instantiation
- [ ] first-onset growth

## Log

- 2026-08-14 -- formalized stable open finite-power target and syndetic autonomous composition.
- 2026-08-14 -- downstream Pauli-local capstone composes generic bounded-weight locality and the
  permanent two-query Haar separator on the same fixed Hamiltonian.
