# Prime-radial excess intersection and normalized discriminant law — formalized

- **ID:** `prime-radial-excess-intersection-discriminant-law-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `prime-radial-excess-intersection-discriminant-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.PrimeRadialExcessDiscriminant` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/PrimeRadialExcessDiscriminant.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.  All declarations live in namespace
`HTGeometry.ConstraintRelativity`.

## Corpus reuse

Nothing below was rebuilt.

- `HTGeometry/CommonFactorKoszulHomology.lean` — the entire split-coordinate Koszul layer:
  `unitWeightedAugmentation` (the card's `h_F`), `unitWeightedSection`,
  `unitWeightedAugmentation_section`, `unitWeightedSplitEquiv` (the splitting `(7)`),
  `unitWeightedRelations`, `unitWeightedRelationsBasis` and `card_unitWeightedAway`
  (`E_F` free of rank `N−1`), `splitCommonFactorKoszulCycles`,
  `splitCommonFactorKoszulBoundaries`, `splitCommonFactorCyclesEquiv` (cycles `≅ ⋀^{p+1}E`),
  `map_scalarRange_splitCommonFactorCyclesEquiv_eq_boundaries` (boundaries `= z·⋀^{p+1}E`),
  and the arbitrary-index versions `unitWeightedFinsuppAugmentation`,
  `unitWeightedFinsuppRelations`, `unitWeightedFinsuppAway`,
  `unitWeightedFinsuppRelationsBasis`.
- `HTGeometry/ConstraintRelativity/PhaseSubdiscriminantKaehlerSmith.lean` — `contactSheets`,
  `contact_cokernel_equiv`, `detIdeal_contact`, `detIdeal_contactScale_eq_sq`,
  `isUnit_det_vandermonde_of_separated`, `residueMult`, `contactScale`.
- `HTGeometry/ConstraintRelativity/UltrametricHorizonEnergySmith.lean` — `sheetDiscriminant`.
- `HTGeometry/VandermondeSign.lean` — `vandermondeProd`, `det_vandermonde_eq_vandermondeProd`,
  `vandermondeProd_comp`.
- `HTGeometry/DVRFiniteSpan.lean`, `HTGeometry/DeterminantalIdeal.lean`,
  `HTGeometry/SmithNormalFormDVR.lean` — the DVR/Smith/determinantal-ideal layer
  (`addVal_of_isUnit`, `addVal_prod`, `detIdeal`, `exists_smithNormalForm`,
  `cokernel_equiv_pi_of_diagonal`).
- From mathlib: `IsDiscreteValuationRing.addVal`, `Matrix.vandermonde`,
  `Submodule.quotientPi`, `Submodule.Quotient.equiv`, `exteriorPower.finrank_eq`,
  `exteriorPower.map_surjective`, `Finsupp.sum_mapDomain_index_inj`,
  `Module.nontrivial_of_finrank_pos`.

**mathlib has no Koszul complexes at all** (no `Mathlib/**/Koszul*` file); the corpus does, and
the card's Theorem 1 is two corpus facts glued by `Submodule.Quotient.equiv`.

## Formal theorem chain

### Theorem 1 — exact excess-intersection homology, cards `(5)`, `(6)`, `(9)`

1. `splitKoszulHomology`, `splitKoszulHomologyEquiv` — **`(5)`, `(9)` boxed**: in split
   coordinates the Koszul homology of a common-factor family is
   `H_{p+1}(K) ≅ (⋀^{p+1}E) ⧸ z·(⋀^{p+1}E)`, i.e. `R/(a) ⊗ ⋀^• E_F`.  The statement is
   proved for an *arbitrary* module `E`, which is what makes Theorem 5 free.
2. `finrank_exteriorPower_ker_weightedSum` — **`(6)` boxed**: the homology dimensions are
   `C(N−1, j)`.

Forming the nested quotient `↥(cycles) ⧸ boundaries` needs `set_option maxSynthPendingDepth 4`;
without it instance search fails to find `HasQuotient` even though every ingredient is present.

### Corollary 2 — literal weighted root conormal, cards `(10)`–`(14)`

3. `weightedSum`, `meanSum`, `weightDiag`, `weightDiag_map_ker` — **`(10)`, `(11)`, `(12)`**: the
   weighted diagonal `(c_p) ↦ (c_p log p)` is a linear isomorphism carrying the weighted syzygy
   hyperplane `{∑ c_p log p = 0}` onto the mean-zero type `A_{N−1}` root space `{∑ d_p = 0}`.
4. `weightedSum_surjective` — **`(13)` boxed**: the syzygy functional is surjective, so the
   underived horizon port is one-dimensional.
5. `finrank_ker_weightedSum` — **`(14)` boxed**: the excess conormal has rank `N − 1`.

### Theorem 3 — normalized discriminant is a cutoff-independent horizon, cards `(15)`–`(20)`

6. `vandermondeProd_contactSheets` — **`(20)`**: the orientation of `f_p = a·u_p` is
   `a^{N(N−1)/2}` times the residue orientation.
7. `addVal_pow`, `addVal_sheetDiscriminant_contact` — **`(17)`, `(18)`, `(19)` boxed**: the
   discriminant has order exactly `N(N−1)` in the horizon parameter, so the normalised divisor is
   independent of the cutoff.

### Theorem 4 — exact observer Smith/Bockstein staircase, cards `(20a)`–`(20k)`

8. `primeRadial_cokernel_equiv` — **`(20c)`, `(20d)` boxed**: the exact Smith form
   `diag(1, a, …, a^{N−1})` and the barcode `⊕_j R/(a^j)`.
9. `primeRadial_detIdeal` — every determinantal ideal of the observer.
10. `primeRadial_fitting_square` — **`(20j)` boxed**: the orientation ideal squares to the
    cotangent Fitting ideal, at every height.
11. `primeRadial_grade_card`, `primeRadial_grade_eq_rootCount` — **`(20e)`, `(20f)`**: the
    `a`-adic grade dimensions are `N−1, N−2, …, 1`, matching the type `A_{N−1}` positive-root
    height distribution `N − h`, and their sum is the observer defect length `C(N,2)`.

### Theorem 5 — compatible infinite excess, no stable top determinant, cards `(21)`, `(22)`

12. `unitWeightedFinsuppAugmentation_mapDomain_comp`,
    `mem_unitWeightedFinsuppRelations_mapDomain_iff`,
    `mapDomain_mem_unitWeightedFinsuppRelations` — **`(21)`**: zero extension along an injection of
    prime sets carries excess conormals into excess conormals, so the finite relation modules form
    a compatible system.
13. `mapDomain_subtypeDomain_support`, `exists_finiteCutoff_unitWeightedFinsuppRelations`,
    `unitWeightedFinsuppRelations_eq_iSup` — **`(21)` boxed**: `E_∞` is the filtered colimit of
    the finite-cutoff `E_F`, in the concrete form `E_∞ = ⨆_F (zero extension of E_F)`; every
    excess conormal is born at the finite cutoff carrying its support.
14. `exists_cutoff_exteriorPower_ne_zero` — **`(21)`**: every fixed exterior degree is nonzero
    from a finite cutoff on.
15. `infinite_unitWeightedFinsuppAway`, `nontrivial_exteriorPower_of_infinite_basis`,
    `nontrivial_exteriorPower_infinite_excess` — **`(22)` boxed**: over an infinite prime set the
    excess conormal is free on an infinite basis and *every* exterior degree is nonzero, so there
    is no largest nonzero degree and no stable top determinant line.

The card's proof passes through filtered colimits of vector spaces and the interchange
`⋀^j(colim E) ≅ colim(⋀^j E)`.  The Lean proof does not need either: `unitWeightedFinsuppRelations`
is already defined over an arbitrary index type, so `E_∞` is a module in its own right, item 13
proves it *is* the colimit, and Theorem 1 (item 1) applies to it verbatim because it was stated for
an arbitrary `E`.  Nonvanishing of `⋀^n E_∞` is proved by choosing `n` distinct basis indices,
projecting onto `R^n`, and using `exteriorPower.map_surjective` against the one-dimensional
`⋀^n R^n` — no rank arithmetic in infinite dimension is needed.

### Theorem 6 — phase-torus non-Abelian conormal curvature, cards `(22a)`–`(22e)`

16. `trace_commutator_eq_zero` — **`(22e)` boxed**: the determinant-line/first-Chern curvature is
    flat.
17. `commutator_eq_zero_of_finrank_one` — **`(22d)` at `N = 2`**: a one-dimensional excess bundle
    has vanishing phase curvature.
18. `rankOneOp`, `rankOneOp_not_commute` — the `N ≥ 3` mechanism: non-orthogonal, non-collinear
    rank-one Hermitian operators do not commute.
19. `orthoProj`, `inner_orthoProj_orthoProj`, `orthoProj_not_collinear`,
    `phaseCurvature_commutator_ne_zero` — **`(22d)` boxed, `N ≥ 3`**: orthogonal unit vectors
    project to non-orthogonal ones (`⟪P₀a, P₀b⟫ = −⟪a,w⟫⟪w,b⟫ ≠ 0`), a third direction meeting the
    weight vector separates them, and hence every pair commutator `[Q_p, Q_q]` of the phase
    curvature is nonzero.  Stated over an arbitrary complex inner-product space rather than in
    prime coordinates, so no `EuclideanSpace` bookkeeping is needed.

### Theorem 7 — canonical root frame and forced half-density connection, cards `(22f)`, `(22g)`

20. `rootFrame_normalised`, `rootDifference_mem_relations` — the canonical root frame
    `s_p = u_p⁻¹ e_p` is normalised and its ordered differences are excess syzygies, reusing the
    corpus `unitWeightedSection` and `unitWeightedAugmentation_section`.

## Scope

The card contains no RH claim and the Lean file makes none.  `H_k`-style walls, the "derived-only
growth" corollary and the "RH boundary" section are commentary on the formalized statements, not
extra theorems: the corollary is the degree count already carried by items 2 and 15, and the RH
boundary section explicitly records that the construction is divisor-blind.  The "Hostile audit"
section is commentary.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/PrimeRadialExcessDiscriminant.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.PrimeRadialExcessDiscriminant          # green
```

`#print axioms` on `vandermondeProd_contactSheets`, `addVal_sheetDiscriminant_contact`,
`primeRadial_cokernel_equiv`, `primeRadial_detIdeal`, `primeRadial_fitting_square`,
`primeRadial_grade_card`, `primeRadial_grade_eq_rootCount`, `weightedSum_surjective`,
`finrank_ker_weightedSum`, `splitKoszulHomologyEquiv`, `finrank_exteriorPower_ker_weightedSum`,
`rootFrame_normalised`, `rootDifference_mem_relations`, `trace_commutator_eq_zero`,
`commutator_eq_zero_of_finrank_one`, `exists_cutoff_exteriorPower_ne_zero`,
`rankOneOp_not_commute`, `orthoProj_not_collinear`, `phaseCurvature_commutator_ne_zero`,
`mapDomain_subtypeDomain_support`, `unitWeightedFinsuppAugmentation_mapDomain_comp`,
`mem_unitWeightedFinsuppRelations_mapDomain_iff`, `mapDomain_mem_unitWeightedFinsuppRelations`,
`exists_finiteCutoff_unitWeightedFinsuppRelations`, `unitWeightedFinsuppRelations_eq_iSup`,
`infinite_unitWeightedFinsuppAway`, `nontrivial_exteriorPower_of_infinite_basis` and
`nontrivial_exteriorPower_infinite_excess` returns only `[propext, Classical.choice, Quot.sound]`.
