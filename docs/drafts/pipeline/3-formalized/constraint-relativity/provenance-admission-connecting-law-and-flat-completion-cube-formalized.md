# Provenance-admission connecting law and flat completion cube — formalized

- **ID:** `provenance-admission-connecting-law-flat-completion-cube-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `provenance-admission-connecting-law-and-flat-completion-cube.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.ProvenanceAdmissionCube` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/ProvenanceAdmissionCube.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.  Declarations live in namespace
`HTGeometry.ConstraintRelativity`.

## Corpus reuse

The card is self-contained abstract algebra plus one analytic example, so the module rests only on
mathlib: `FreeAbelianGroup`, `Submodule.mapQ`, `Submodule.Quotient`, `Submodule.quotEquivOfEqBot`,
`Submodule.topEquiv`, `LinearEquiv.ofInjective`, `Memℓp`, `lp`, `memℓp_gen_iff`,
`Memℓp.of_exponent_ge`, `Real.summable_one_div_nat_pow`, `Real.not_summable_one_div_natCast`.

## Formal theorem chain

### Theorem 2.1 — the closure-insertion cube, cards `(2.1)`, `(2.2)`

1. `closureCubeStage`, `closureCubeStage_zero`, `closureCubeStage_succ` — the transport chain with
   the closures indexed by a finite set `S` inserted, card `(2.1)`.
2. `closureCubeStage_mono` — inserting more closures never decreases the stage value; the proof is
   the card's one-index argument, by induction on the stage.
3. `closureCubeVertex`, `closureCubeVertex_mono` — **`(2.2)`**: `S ↦ x_S` is monotone from the
   Boolean lattice.
4. `closureCubeVertex_closed` — every vertex is closed, by idempotence of the terminal closure.

### Proposition 2.2 — the additive Bianchi law, cards `(2.3)`–`(2.5)`

5. `provenanceEdge`, `provenanceEdge_self` — card `(2.3)`.
6. `provenanceEdge_trans` — edges telescope.
7. `provenanceEdge_square` — **`(2.4)`**: every square face obeys the Bianchi law.
8. `provenanceEdge_path` — **`(2.5)`**: the sum along any path is the difference of its endpoints,
   so the cube is flat and formal completion cannot create higher holonomy.

### Theorem 3.1 — the complete primitive-escape classification, cards `(3.2)`–`(3.5)`

9. `admittedBoundaries`, `admittedCocycles`, `primitiveEscape`,
   `admittedBoundaries_le_primitiveEscape`, `primitiveEscape_le_admittedCocycles`,
   `admittedCocycles_le_cocycles` — the three submodules of the card and the inclusions between
   them; the middle one is where `d² = 0` is used.
10. `AdmissionCurvature` — **card `(3.2)`**: `E^k(R,S) = (dR^{k-1} ∩ S^k)/dS^{k-1}`.
11. `AdmittedCohomology`, `FormalCohomology`, `admittedToFormal` — `H^k(S)`, `H^k(R)` and the
    comparison.
12. `admissionToCohomology`, `admissionToCohomology_mk`,
    `admissionToCohomology_injective`, `range_admissionToCohomology`,
    `admissionCurvatureEquiv` — **`(3.3)` boxed**: the canonical isomorphism
    `E^k(R,S) ≅ ker(H^k(S) → H^k(R))`.  The second isomorphism of `(3.3)` — with the image of the
    connecting map `δ : H^{k-1}(Q) → H^k(S)` — is exactness of the long exact sequence at
    `H^k(S)`, and is exactly what `range_admissionToCohomology` proves in the concrete form
    "a source class dies formally iff it is a formal boundary": the image of `δ` *is* that kernel.
13. `escapeClass` — **`(3.4)`, `(3.5)`**: a formal primitive whose boundary is source-admitted
    determines the class `[ω] = δ[ℓ̄]`.
14. `escapeClass_eq_zero_iff` — **equivalences 1 ↔ 2 ↔ 3**: the class vanishes exactly when the
    boundary has a source-admitted primitive.
15. `exists_admitted_primitive_iff` — **equivalence 1 ↔ 4**: unfolded, `[ℓ̄]` lies in the image of
    `H^{k-1}(R) → H^{k-1}(Q)`, i.e. `ℓ` differs from a formal cocycle by a `Q`-boundary and a
    source-admitted cochain.  Only `d² = 0` in the previous degree is used.

### Countermodels, cards `(4.1)`, `(5.1)`

16. `algebraicAdmissionCurvatureEquiv` — **`(4.1)`**: for `S = (0 → k)` inside `R = (k →id→ k)` the
    admission-curvature group is the whole field.
17. `algebraicFormalCohomology_eq_bot` — the completed theory has vanishing `H^1`, so absolute
    cohomology after completion can be zero while the entire source obstruction survives.
18. `harmonicSeq`, `summable_harmonicSeq_sq`, `not_summable_harmonicSeq`,
    `harmonicSeq_memℓp_two`, `harmonicSeq_not_memℓp_one` — the harmonic sequence lies in `ℓ²` and
    not in `ℓ¹`.
19. `ellOneInsideEllTwo`, `harmonicEllTwo`, `harmonicEllTwo_notMem`,
    `harmonicAdmissionClass_ne_zero` — **`(5.1)`**: the harmonic sequence is a formal `ℓ²` boundary
    with no source-admitted `ℓ¹` primitive, so its class in `E^1 = ℓ²/ℓ¹` is nonzero.

## Scope

Section 6 (corpus consequences), section 7 (the failed universal conjecture, its six informal
countermodels, and the source-framed strict fracture conjecture `(7.1)`) and section 8 (novelty
boundary) are commentary and open programme; nothing there is formalized or claimed.  The card is
explicit that `(3.2)` classifies only formal-exact/source-nonexact primitive escape, and that even
the abstract synthesis is not new to the project.  The non-Hausdorff remark about the quotient
topology in section 5 is a topological aside; the formalized statement is the algebraic
nonvanishing of the class.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/ProvenanceAdmissionCube.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.ProvenanceAdmissionCube          # green
```

`#print axioms` on `closureCubeStage_mono`, `closureCubeVertex_mono`, `closureCubeVertex_closed`,
`provenanceEdge_trans`, `provenanceEdge_square`, `provenanceEdge_path`,
`admissionToCohomology_injective`, `range_admissionToCohomology`, `admissionCurvatureEquiv`,
`escapeClass_eq_zero_iff`, `exists_admitted_primitive_iff`, `algebraicAdmissionCurvatureEquiv`,
`algebraicFormalCohomology_eq_bot`, `harmonicSeq_memℓp_two`, `harmonicSeq_not_memℓp_one`,
`harmonicEllTwo_notMem` and `harmonicAdmissionClass_ne_zero` returns only
`[propext, Classical.choice, Quot.sound]` (the cube theorems need no `Classical.choice`).
