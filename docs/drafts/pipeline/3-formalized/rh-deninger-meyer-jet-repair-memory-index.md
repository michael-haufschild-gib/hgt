# Deninger–Meyer jet repair memory index

## Claim `DM-JET-REPAIR-INDEX`

Let `S` be a finite packet of Xi divisor points, all off `Re(s)=1/2`. Let `G_S` be closure of full multiplicity-bounded Xi-jet graph in canonical half-density completion, and let `π_S : G_S → H_{1/2}` be source projection. For every finite-dimensional complex record `R : G_S → E`,

`(π_S, R) injective  ⇒  Σ_{ρ∈S} ord_ρ(Xi) ≤ dimℂ E`.

Interpretation: analytic multiplicity is minimum auxiliary memory needed to repair information erased by half-density completion. It is not only spectral/Jordan multiplicity.

## Novelty audit

- Meyer proves generator algebraic multiplicity equals Xi zero order; no completion-repair dimension law.
- Canonical linear-relation decomposition identifies multivalued/singular part; no Xi multiplicity computation.
- Corpus separately proves full vertical Xi-jet defect, generic erased-kernel record bound, and abstract Xi-reporter optimality. Search found no theorem joining closed half-density relation to repair-memory lower bound.
- Status: preliminary novelty; no priority claim.

## Paper proof

1. `ker π_S` is linearly equivalent to vertical fibre `mul(G_S)` by `y ↦ ((0,y), membership)` and second projection.
2. Off line, `mul(G_S)` is full Xi jet packet.
3. Packet dimension is `Σ ord_ρ(Xi)`.
4. Injectivity of `(π_S,R)` makes `R|ker π_S` injective.
5. Finite-dimensional rank monotonicity gives `dim ker π_S ≤ dim E`.

## Falsifiers

- Any failed equivalence in step 1 means vertical defect does not measure erased source information.
- Any faithful record of smaller dimension refutes claim.
- If result reduces to arbitrary full-product projection without using off-line graph closure, interpretation is theatre and card must be retired.

## Status

Formalized in `DeningerMeyerHalfDensityFiniteXiJetRepairIndex.lean`:

- `deningerMeyerFiniteXiJetVerticalSourceKernelEquiv`
- `finrank_deningerMeyerFiniteXiJetClosedSourceProjection_ker_of_offline`
- `deningerMeyerFiniteXiJetRepair_finrank_lower_bound`
- canonical record proves bound sharp.

Targeted Lean and module build pass. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
