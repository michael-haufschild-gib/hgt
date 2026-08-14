# Prime-torsion circuit-ray polygon law

- **ID:** `prime-torsion-circuit-ray-polygon-law`
- **Stage:** 3 -- formalized
- **Type:** THEOREM (Lean)
- **Paper parent:** `../2-fully-proven/prime-torsion-recurrence-polygon-complexity-law.md`
- **Extends:** `prime-torsion-target-cap-polygon-law.md`

## Exact unconditional law

Let `p` be prime, `d>0`, `2n<p`, and let `Y` be any finite dictionary of normalized vectors in the
full Choi Hilbert space `EuclideanSpace ℂ (Fin d × Fin d)`.  If `0≤epsilon<1/2` and

\[
 ((p-1)|Y|)\,n!\,d^{-n}
 < \left(\sqrt{1-4\epsilon^2}\right)^{2n},
\]

then there is `q : Fin d → ZMod p` such that, for every nonzero `a : ZMod p` and every `y : Y`,
the normalized diagonal Choi vector with phase `a q` has pure-state trace distance strictly greater
than `epsilon` from target `y`.

Targets are arbitrary normalized rays.  They need not be diagonal, grid-valued, mutually
orthogonal, or fixed before `q` is selected.

## Formal package

`RHTower/FiniteGridChoiRayCap.lean` proves:

- exact embedding of `ZMod M` phases into normalized diagonal Choi vectors;
- exact relative-overlap identity with uniform coherence;
- any arbitrary normalized-ray `epsilon`-cap that captures a grid point is contained in one
  translated coherence cap at threshold `sqrt(1-4 epsilon^2)`;
- one-ray and complete finite-dictionary cardinal bounds.

`RHTower/PrimeTorsionCircuitRayPolygon.lean` proves:

- `exists_primeTorsion_complete_circuitRay_avoidance`, the exact bad-cardinality form;
- `exists_primeTorsion_complete_circuitRay_avoidance_of_replicaBudget`, the displayed factorial
  replica-budget law.

The complete nonidentity orbit is retained: the target union and all `p-1` powers are paid for in
one incidence budget.  No minimum spectral-gap hypothesis appears.

## Frontier now isolated

This formalization closes the former “arbitrary normalized circuit rays” gap.  The downstream
`prime-torsion-autonomous-circuit-polygon-law.md` now also identifies these exact grid polygons with
syndetic approximate polygons of one fixed maximally projective autonomous spectrum.  Remaining
obligations are:

1. explicit ordinary local-Hamiltonian instantiation together with the permanent Haar separator;
2. explicit circuit/heap cardinal asymptotics sufficient to instantiate `Y` at Brown-scale depth;
3. the separate first-onset growth law from time zero.

These are the formal research frontier; none is hidden as a hypothesis of the theorem above.

## Gates

- [x] arbitrary normalized targets in full Choi space
- [x] exact trace-distance-to-coherence cap reduction
- [x] exact finite-dictionary union
- [x] complete nonidentity prime orbit
- [x] independent replica and torsion orders (`2n<p`)
- [x] no computation and no unproved declaration
- [x] RHTower umbrella import
- [x] autonomous fixed-Hamiltonian polygon shadowing (maximally projective spectrum; downstream)
- [ ] Brown-scale circuit/heap instantiation
- [ ] first-onset growth

## Log

- 2026-08-14 -- formalized full arbitrary-ray reduction and complete circuit-ray polygon law.
- 2026-08-14 -- downstream autonomous-shadowing theorem closes the fixed-spectrum phase-flow
  composition without a quantitative Diophantine hypothesis.
