# Stage-3 sweep ledger — 04-rg-stochastic-quantum-fields (17 cards)

Goal: unconditional Lean for every proven theorem on every card; promote to `3-formalized`.
Rules: no hypotheses wrapping unproven input; no umbrella builds; `lake env lean` for checking,
`lake build <module>` only for final audit; `#print axioms` only on new capstones.

| # | Card | Remaining Lean obligation | Status |
|---|---|---|---|
| 1 | thermodynamic-divisor-charge-finite-ancestor-or-boundary-index | DONE — `RHTower/ThermodynamicBoundaryIndexCarrier.lean` | **PROMOTED** |
| 2 | balanced-causal-fracture-torsor-classification | DONE — AIIIGramFibreTorsor, HermitianConeStrictConvexity, ColorGramGlobalTrivialization, ColorGramTrivializationSmoothness, HermitianSymmetricDimensionBalance | **PROMOTED** |
| 3 | common-profile-boolean-anchor-curvature | (CG1),(CG3),(CG4),(CG6),(SG10),(SG9) | TODO |
| 4 | coherence-graph-volume-recurrence-exponent-law | (1),(2),(3) + rank-zero boundary | TODO |
| 5 | schwarzian-projective-erosion-tower | Schwarzian tower depth law, strict descent, intersection = K | TODO |
| 6 | bbm-pullback-completion-purely-continuous-law | pullback completion unitary + reducing-subspace lemma + dilation a.c. | TODO |
| 7 | q-geometric-generalized-free-field-hypertranscendence | moments, positivity, self-similarity, Hankel, + ADH q-difference dichotomy | TODO |
| 8 | ultrametric-thermal-mahler-hypertranscendence | (3) constraint + uniqueness (done?), non-rationality, HT | TODO |
| 9 | ultrametric-one-loop-resolvent-hypertranscendence | (5),(9),(10) coefficientwise (claimed done), HT | TODO |
| 10 | reciprocal-q-ladder-kallen-lehmann-field | pushforward positivity, (13), (15), HT, de Sitter clock (21),(22) | TODO |
| 11 | de-sitter-ultrametric-detailed-balance-hypertranscendence | (5),(8),(9) + DA-invariance under w=exp(-a/H) | TODO |
| 12 | gadc-tree-population-rg-clock-hypertranscendence | algebra formalized; HT classification remains | TODO |
| 13 | noisy-binary-tree-channel-rg-clock-hypertranscendence | algebra formalized; HT classification remains | TODO |
| 14 | exact-rational-rg-generation-dichotomy | Poincare/Ritt DA dichotomy, cocycle equivalence | TODO |
| 15 | exact-rg-clock-hypertranscendence-equivalence | clock/beta DA equivalence | TODO |
| 16 | rg-tower-differential-incoherence-obstruction | coherence obstruction via Boshernitzan-Rubel | TODO |
| 17 | erosion-threshold | backbone + 19a + 19b assembly | TODO |

## Log
- 2026-08-29 — ledger created; all 17 cards read; named modules confirmed present in tree.
- 2026-08-29 — cards 1 and 2 promoted.

## Blocker analysis (2026-08-29)

Shared external theorems that gate whole groups of cards:

| Needed theorem | Cards blocked |
|---|---|
| Adamczewski--Dreyfus--Hardouin rational-or-hypertranscendental dichotomy for linear `q`-difference and Mahler equations | 7, 8, 9, 10, 11 |
| Ritt / Becker--Bergweiler classification of Schroeder, Abel and Poincare functions of rational maps | 12, 13, 14 |
| Boshernitzan--Rubel coherent families + Bergweiler's solution of Rubel's problem | 16 |
| Differentially algebraic germ category with analytic local inversion | 14, 15, 16 |
| Unbounded self-adjoint operator theory (resolvent, reducing subspaces, a.c. spectrum) | 6 |
| Selberg CLT and the abscissa/coboundary backbone | 17 |

Self-contained builds (no external import needed):

| Card | Build |
|---|---|
| 3 | arithmetic `B_(c,r,h)` reduction, physical-profile identities, protected-anchor row identity, an exact statement for `(SG9)` |
| 4 | forest-coordinate volume law, minimax exponent, a.e. exponent, rank-zero boundary |
| 5 | Schwarzian tower over a family: level independence, strict descent, depth law, trivial intersection |

Corpus assets found for card 5: `FreeCoordinateField.lean` (free rational coordinate field,
`mem_freeCoordinateField_iff`, coordinate derivations, common kernel), `FreeDifferential*`
(free jet field, translation and scaling automorphisms), `ProjectiveHorizonSchwarzian*`
(single-generator Schwarzian coordinate system, `schwarzianBasisEquiv`,
`algebraicIndependent_schwarzianSystem`), `DifferentialTranscendenceDegree.lean`,
`DifferentialIndependence.lean`.  The remaining work is the family (`A x N`-indexed) version of
the Schwarzian coordinate change and the tower built from it.

## Card 5 design (Schwarzian projective erosion tower)

Ambient object: `FreeCoordinateRationalField C (ι × ℕ)` with the family jet-shift derivation
`(a, m) ↦ (a, m+1)`.  This is `K<Y_a : a ∈ ι>`, the card's `F_0`.

1. `freeFamilyJetShift` — family jet-shift derivation and `Differential` instance (new module
   `FreeFamilyJetShift.lean`), mirroring `ProjectiveHorizonFreeJetReciprocalTail.freeJetShift`.
2. `schwarzianFamily a = schwarzian (familyJet a 0)`; substitution
   `Φ (freeCoordinate (a, m)) = differentialJet m (schwarzianFamily a)`, built from
   `freeCoordinateBasisEval` at the family `(a,m) ↦ differentialJet m (𝔖_a)` once that family is
   proved algebraically independent.
3. `Φ` intertwines the derivation: the locus where `Φ (f′) = (Φ f)′` is an intermediate field
   containing every coordinate, and coordinates generate everything
   (`freeCoordinateField_univ`).
4. `F n := (Φ^[n]).fieldRange`; `F (n+1) ≤ F n` from `Φ^[n+1] = Φ^[n] ∘ Φ`.
5. **Depth key lemma** `Φ g ∈ lowField (k+3) → g ∈ lowField k`, where
   `lowField k = freeCoordinateField C (ι × ℕ) {p | p.2 < k}`; iterate to
   `Φ^[n] g ∈ lowField (3n + k) → g ∈ lowField k`, hence `F n ⊓ lowField (3n) = ⊥`.
6. Consequences: depth law (item 3), strict descent (item 2, using
   `Y^[n] ∈ lowField (3n+1) \ C`), trivial intersection (item 4, since every element lies in
   `lowField N` for some `N` by `exists_finset_mem_freeCoordinateField`).
7. Level independence (item 1) from differential transcendence degree: `F n` is generated by the
   `|ι|`-family `Y^[n]`, and `F 0` is differentially algebraic over `F n` through the Schwarzian
   relation `2 q' q''' − 3 (q'')² − 2 s (q')² = 0`.
8. Item 5 (translation orbits) is the same statement for `ι` a translation orbit; the Schwarzian
   tower commutes with the index relabelling.
