# Finite lattice-direction capacity, verticality, and Pontryagin law — Lean certificate

- **ID:** `cmr-finite-lattice-direction-capacity-verticality-pontryagin-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `finite-lattice-direction-capacity-verticality-pontryagin-law.md` (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean modules

| Module | Content |
|---|---|
| `.../ConstraintMotiveRelativity/LatticeDirectionCapacity.lean` | `rankOne`, `LatticeDirectionData`, its capacity chart, the divergent span, Theorem 2.1 |
| `.../ConstraintMotiveRelativity/LatticePontryaginSplit.lean` | the integral part, primitivity, freeness of the quotient, the character exact sequence |
| `.../ConstraintMotiveRelativity/LatticeDirectionPortLaw.lean` | the relation-valued form `(FLD.5)` |
| `.../ConstraintMotiveRelativity/SymmetricSquareRoot.lean` | spectral data of a symmetric positive operator |
| `.../ConstraintMotiveRelativity/WeightedCoordinatePort.lean` | weighted `ℓ²(J)` coordinate ports and their exact stage Gram operators |
| `.../ConstraintMotiveRelativity/LatticeDirectionRealization.lean` | Proposition 2.2, the exact nested Hilbert realization |
| `.../ConstraintMotiveRelativity/CofinalDirectionCountermodel.lean` | Theorem 4.1, the cofinal-direction countertheorem |

All are imported by the area umbrella `GaloisForLFunctions.HTGeometry`.
Namespace: `HTGeometry.ConstraintMotiveRelativity`.

## Formal statement chain

1. `rankOne a` — the operator `a ⊗ a`, with `inner_rankOne`, `rankOne_symm`, `rankOne_smul`.
2. `LatticeDirectionData Y r` — `(FLD.1)`–`(FLD.2)`: a symmetric positive-definite baseline, `r`
   marked directions, and nonnegative nondecreasing weights.
3. `LatticeDirectionData.gram`, `inner_gram`, `gram_symm`, `gram_pos`, `gram_mono`,
   `LatticeDirectionData.chart` — the family is an increasing capacity chart.
4. `divergentIndices`, `divergentSpan` — `(FLD.3)`.
5. `weight_bddAbove_of_not_divergent` — a nondecreasing sequence is bounded or divergent.
6. **`LatticeDirectionData.boundedCapacity_eq_orthogonal`** — the bounded-capacity sector is
   `Vᗮ`, proved from `⟪G_n x, x⟫ = ⟪A₀ x, x⟫ + ∑_i c_i(n) ⟪a_i, x⟫²`.
7. **`LatticeDirectionData.ker_cometricLimit_eq_divergentSpan`** — Theorem 2.1, `(FLD.4)`:
   `ker Q_∞ = span_ℝ {a_i : c_i(n) → ∞}`.
8. **`multivaluedHorizon_eq_divergentSpan`** — `(FLD.5)`: a Hilbert port tower realizing the
   family has vertical fibre exactly `V`.
9. `latticePart`, **`latticePart_primitive`** — `(FLD.6)` and primitivity.
10. `isTorsionFree_quotient`, **`free_quotient`**, `exists_splitting` — `Λ/Λ_V` is torsion free,
    hence free, hence the quotient splits.
11. `restrictChar`, `inflateChar`, **`inflateChar_injective`**, **`range_inflateChar`**,
    **`restrictChar_surjective`** — `(FLD.7)`: exactness of
    `0 → Hom(Λ/Λ_V, T) → Hom(Λ, T) → Hom(Λ_V, T) → 0` for every abelian target `T`; for `T` the
    circle group and `Λ` discrete this is the Pontryagin sequence.
12. `span_latticePart` — when `V` is spanned by lattice vectors, `Λ_V` spans `V`, so its rank is
    `dim V`.
13. `eigBasis`, `eigVal`, `apply_eigBasis`, `eigVal_nonneg`, `eigVal_pos`, `apply_eq_sum`,
    `symSqrt`, `symSqrt_symm`, **`symSqrt_symSqrt`** — the spectral data and symmetric square root
    of a symmetric positive operator.
14. `PortCoord`, `portBasis`, `orthonormal_portBasis`, `portEmb`, `portMass`, `weightedPort`,
    `portStage`, `portStage_le`, `portWitness` — weighted coordinate ports.
15. **`portGram_portStage`** — the exact stage Gram identity
    `T_F T_F^* = ∑_{j ∈ F} (wt j)² · dir j ⊗ dir j`, proved through the new co-lift
    characterization `portCoLift_eq` / `portGram_eq_of_coLift`.
16. `latDir`, `latWt`, `latStageSet`, **`latGram_eq`**, **`latPortFilling`**, `latStage_iSup`,
    **`latTower`**, **`latTower_gram`**, **`latTower_multivaluedHorizon`** — Proposition 2.2,
    `(FLD.8)`–`(FLD.9)`: every family with `c_i(0) = 0` is the Gram family of a nested surjective
    finite-dimensional port tower, whose vertical fibre is `V`.
17. `planeDir`, `continuous_planeDir`, `exists_rat_planeDir`, `rotDir`, `rotGram`, `rotChart`,
    **`rotChart_boundedCapacity`**, **`rotChart_ker`**, **`rotChart_line_lattice_trivial`**,
    **`rotDir_lattice_provenance`** — Theorem 4.1, `(FLD.14)`: an increasing chart whose every
    increment is a positive multiple of `a ⊗ a` for a nonzero integer vector `a`, but whose
    limiting cometric kernel is an irrational line meeting `ℤ²` only in `0`.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/LatticeDirectionCapacity.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/LatticePontryaginSplit.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/LatticeDirectionPortLaw.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/SymmetricSquareRoot.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/WeightedCoordinatePort.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/LatticeDirectionRealization.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CofinalDirectionCountermodel.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.LatticeDirectionRealization
```

All green with no warnings from these modules.

`#print axioms` on `LatticeDirectionData.ker_cometricLimit_eq_divergentSpan`,
`LatticeDirectionData.boundedCapacity_eq_orthogonal`, `multivaluedHorizon_eq_divergentSpan`,
`latTower_multivaluedHorizon`, `latGram_eq`, `latPortFilling`, `portGram_portStage`,
`symSqrt_symSqrt`, `latticePart_primitive`, `free_quotient`, `restrictChar_surjective`,
`range_inflateChar`, `inflateChar_injective`, `span_latticePart`, `rotChart_ker`,
`rotChart_boundedCapacity`, `rotChart_line_lattice_trivial` and `rotDir_lattice_provenance`
reports only `propext`, `Classical.choice`, `Quot.sound`.

## Scope notes

The Lean proof of `(FLD.4)` replaces the block-inverse computation `(FLD.10)`–`(FLD.13)` by the
polar-sector identity of the parent card: the bounded-capacity set of the family is visibly `Vᗮ`,
and the parent card's `boundedCapacity_eq_orthogonal` converts that into `ker Q_∞ = V`.  This is a
shorter proof of the same statement, not a weaker one.

The character sequence is formalized for an arbitrary abelian target, which specialises to the
circle group; `Λ` is a discrete lattice, so every character is continuous and the algebraic
sequence *is* the Pontryagin sequence.

§5 of the paper card lists three corpus realizations and a hostile scope matrix.  Those are
statements about other cards' objects (the polarized Stokes multi-Rees family, the rooted
prime-support Hodge cofactor family, and the weighted prime port); they are recorded there and are
not re-proved here.
