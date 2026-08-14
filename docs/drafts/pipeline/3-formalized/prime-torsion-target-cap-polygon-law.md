# Prime-torsion target-cap polygon law

- **ID:** `prime-torsion-target-cap-polygon-law`
- **Stage:** 3 -- formalized
- **Type:** THEOREM (Lean)
- **Paper parent:** `../2-fully-proven/prime-torsion-recurrence-polygon-complexity-law.md`
- **Statement:** A finite target dictionary on a prime torsion phase grid admits a complete
  nonidentity avoiding power orbit whenever its growing-replica coherence-cap budget closes.

## Goal

Certify the dependency-closed finite combinatorial core needed for hard recurrence polygons while
keeping autonomous-time shadowing and circuit asymptotics as explicit downstream obligations.

## Exact theorem package

### General automorphism law

`HTGeometry/PrimeTorsionOrbitAvoidance.lean` proves:

- `automorphism_preimage_card`;
- `automorphismAvoidance_bad_card_le`;
- `automorphismAvoidance_card_lower`;
- `exists_automorphismAvoidance_of_card_lt`;
- `primeTorsionAvoidanceSet_card_lower`;
- `exists_primeTorsion_complete_avoidance`.

For a finite set `X`, bad set `A`, and finite automorphism family `S`, at least
`|X|-|S||A|` points avoid `A` under every selected automorphism.  For
`X=(Fin d -> ZMod p)` with prime `p`, nonzero scalars supply `p-1` automorphisms, hence at least
`p^d-(p-1)|A|` complete avoiding generators.

### Exact finite-grid cap moment

`HTGeometry/FiniteGridCoherenceMoment.lean` proves:

- modular injectivity on the replica band for every `2n<M`;
- exact zero-character/permutation-floor identification;
- exact `2n`-th norm moment on the `M`-torsion grid;
- deterministic coherence-cap cardinal bound;
- factorial-square-moment bound;
- translated-cap membership and cardinal invariance;
- finite target-union cardinal bound.

The resulting inequality is

\[
 |C_{M,n}(u)|u^{2n}
 \le M^d n!\left(\sum_iw_i^2\right)^n,
 \qquad 2n<M,quad u\ge0.
\]

No probability axiom, asymptotic approximation, or computation is used.

### Complete target-cap polygon

`HTGeometry/PrimeTorsionTargetCapPolygon.lean` proves
`exists_primeTorsion_complete_targetCap_avoidance_of_replicaBudget`:

\[
 (p-1)Nn!\left(\sum_iw_i^2\right)^n<u^{2n},
 \qquad p\text{ prime},\quad 2n<p,
\]

implies existence of a phase `q` such that every nonzero scalar multiple `a q` avoids every one of
the `N` translated coherence caps.

## Unconditionality and boundary

- All theorems are definitions plus proofs; no `axiom`, `sorry`, `admit`, `opaque`, or `unsafe`
  declaration is introduced.
- Literature statements are not encoded as hypotheses or renamed theorems.
- The theorem concerns exact finite phase grids.  It does not by itself prove dense autonomous-time
  shadowing, first recurrence time, continuous-time hardness, or Brown--Susskind initial growth.
- The already-formalized same-Hamiltonian permanent non-Haar separator remains a separate
  composition theorem, not part of this cap count.

## Gates

- [x] paper proof dependency-closed
- [x] finite automorphism union bound
- [x] prime nonzero scalar automorphisms
- [x] arbitrary modulus `M` with independent replica order `2n<M`
- [x] exact finite-grid moment
- [x] factorial cap bound
- [x] finite translated target union
- [x] complete nonidentity prime-torsion power orbit
- [x] umbrella import
- [ ] autonomous recurrence-shadowing composition
- [ ] arbitrary normalized-ray target reduction
- [ ] circuit-count asymptotics

## Log

- 2026-08-14 -- formalized exact finite-grid, cap, and complete prime-power-orbit core.
