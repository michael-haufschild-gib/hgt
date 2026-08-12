# Residue-preserving law-promotion anomaly trilemma — formalized

- **ID:** `residue-preserving-law-promotion-anomaly-trilemma-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `residue-preserving-law-promotion-anomaly-trilemma.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintRelativity.ResiduePromotionAnomaly` | `formal/GaloisForLFunctions/HTGeometry/ConstraintRelativity/ResiduePromotionAnomaly.lean` |

Wired into `GaloisForLFunctions.HTGeometry`.  Declarations live in namespace
`HTGeometry.ConstraintRelativity`.

## Corpus reuse

Nothing below was rebuilt.

- `RHTower/MobiusThetaSourceDaggerMinimalBoundaryLaw.lean` —
  `ccmRationalAdelicTwoLegCyclicResidue` and the exact transgression formula
  `ccmMobiusThetaTwoLegParacyclicDefect_residue`, which **is** card `(25)`.
- `RHTower/MobiusThetaPhysicalParacyclicSourceNullHomology.lean` —
  `deningerHalfDensityMateGain_eq_one_iff_re_eq_half`: the mate gain is one exactly on the critical
  line.
- `RHTower/MobiusThetaInternalJetCompletedHellingerGammaIncidenceBridge.lean` —
  `thetaInternalJetLeadingSourceCoefficient_ne_zero` (`c_ρ ≠ 0`).
- `HTGeometry/CyclicParacyclicBoundaryDefectLaw.lean` — `cyclicParacyclicEquivarianceDefect`.
- `RHTower/SlabFullWidthAdmissibility.lean` — `XiC_ne_zero_of_half_le_abs_im`, the zero-free
  half-planes of the centered Xi function.
- From mathlib: `Polynomial.eq_zero_of_infinite_isRoot`,
  `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` (the identity theorem),
  `LinearIndependent.finite_of_isNoetherian`, `Complex.cpow_add`, `Complex.cpow_eq_zero_iff`.

## Formal theorem chain

### Theorem 1 — the no-surplus attachment criterion, card `(5)`

1. `attachedDifferential`, `attachedDifferential_apply` — the cell-attached differential
   `d'(x,v) = dx + Zv` of card `(4)`.
2. `attachedDifferential_residue_cocycle_iff` — **`(5)` boxed**: the residue extends unchanged
   exactly when `R Z = 0`.
3. `attachedDifferential_residue_cocycle_iff_range` — the second clause: equivalently, the residue
   vanishes on the whole defect subspace.

### Theorem 2 — the minimal compensator rank, cards `(6)`–`(9)`

4. `compensatedDifferential`, `compensatedDifferential_apply` — card `(6)`.
5. `compensatedDifferential_residue_cocycle_iff` — **`(7)` boxed**: `R Z + S q = 0`.
6. `rank_le_of_compensates` — **`(8)`**: `im (R Z) ⊆ im S`, hence `rank (R Z) ≤ rank S ≤ dim A`.
7. `exists_minimal_compensator` — **`(9)` boxed**: the bound is attained by `A = im (R Z)`,
   `q = R Z` corestricted (surjective), `S = −ι_A`.  So `anomrank_R(Z) = rank (R Z)`.

### Theorem 3 — minimal fitted compensation is derived-trivial, cards `(12)`–`(15)`

8. `fittedSplitting`, `fittedSplitting_apply`, `fittedSplitting_symm_apply` — card `(13)`.
9. `fittedSplitting_compensatedDifferential` — **`(14)`**: after the change of coordinates the
   compensated differential is `d ⊕ q`, so the extension is `C` plus the contractible two-term
   complex `V → A`.
10. `fittedSplitting_residue` — **`(15)`**: in the split coordinates the extended residue is `R` on
    `C` and zero on the contractible summand.

### Theorem 4 — presentation invariance, cards `(16)`, `(17)`

11. `anomalyMap_eq_of_comparison`, `anomalyRank_eq_of_comparison` — **`(17)`**: a comparison
    matching residues and carrying defect cycles to defect cycles gives literally the same anomaly
    map, hence the same rank.

### Theorem 5 — coordinate-stable compensators are infinite-dimensional, card `(18)`

12. `linearIndependent_coordinatePowers` — the coordinate powers `z^j f` of a function with
    infinitely many nonzero values are linearly independent: a vanishing finite combination gives a
    polynomial with infinitely many roots.
13. `not_finiteDimensional_of_coordinateStable` — **`(18)`**: any space of functions closed under
    multiplication by the coordinate and containing such an `f` is infinite-dimensional.
14. `infinite_xiC_nonvanishing`, `not_finiteDimensional_of_xiC_coordinateStable` — the literal
    instantiation: `XiC` is nonvanishing on `{ti : t ≥ 1}`, an infinite set (corpus
    `XiC_ne_zero_of_half_le_abs_im`), so every compensator realization containing the actual
    completed theta source and stable under the spectral-coordinate generator is
    infinite-dimensional.  This replaces the card's appeal to the parent card
    `hedenmalm-finite-source-port-obstruction` by a self-contained proof.

### Theorem 6 — holomorphic compensator no-go, cards `(19)`–`(21)`

15. `defectFactor`, `defectFactor_injective` — the real exponential factor `n^{2x−1} − 1` is
    injective for `n ≥ 2`.
16. `no_holomorphic_defectCompensator` — **`(20)`**: no function analytic on a connected open `Ω`
    where `c` is nonvanishing equals `−(n^{2Re s−1}−1)c(s)` there.  The Lean proof does not use
    Wirtinger derivatives: the charge depends on `s` only through `Re s`, so agreeing with it along
    one vertical sequence through a point forces (identity theorem) agreement with a *constant*
    multiple of `c` on all of `Ω`, whence `Re s` would be constant on `Ω` — false for an open set.
    Meromorphic candidates are covered: a meromorphic function is analytic on the complement of its
    poles, and the theorem applies to any connected open subset of that complement.

### Theorem 7 — exact mixed separation rank, cards `(22)`–`(24)`

17. `mixedCharge` — card `(22)`.
18. `mixedCharge_two_legs` — **`(23)`**: two separated legs suffice.
19. `mixedCharge_det` — the evaluation determinant equals
    `c(s₁)c(s₂)(X₁−X₂)(Y₂−Y₁)`, card `(24)`.
20. `mixedCharge_not_rankOne` — no factorization `f(s)g(t)` on four nondegenerate evaluation
    points, since a rank-one evaluation matrix has zero determinant.
21. `exists_separating_point`, `mixedCharge_not_rankOne_on_open` — the nondegenerate points exist
    inside any open set (`n^δ ≠ 1` for real `δ > 0`), so the separation rank is at least two on any
    product of open sets where `c` is nonvanishing, hence exactly two.

### Literal Riemann-source application, cards `(25)`, `(26)`

22. `anomaly_scalar_eq_zero_iff` — the scalar dichotomy: `(n^{2r−1} − 1)c = 0 ↔ r = 1/2` for
    `n ≥ 2`, `c ≠ 0`.
23. `literal_defect_anomaly_eq_zero_iff` — **`(26)` boxed, literal**: for the ordinary-prime
    trace-one cycle the anomaly map of the physical cyclic-to-paracyclic defect vanishes exactly on
    the critical line, using the corpus residue formula `(25)`, `c_ρ ≠ 0`, and the mate-gain
    criterion.  Hence `anomrank_R(Z_ρ) = 0` on the line and `1` off it.

## Scope

The "conservation interpretation" trilemma `(11)` is the conjunction of Theorems 1–3 and carries no
separate content.  The "new leverage" list, the "relation to unique Stokes port" section and the
hostile audit are commentary.  The card is explicit that it does **not** prove RH: `(26)` is an
exact dichotomy, and the nonexistence of a source-generated noncontractible opposite-residue sector
is stated as an open search target, not a theorem.  Nothing of that is formalized or claimed.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstraintRelativity/ResiduePromotionAnomaly.lean  # clean
lake build GaloisForLFunctions.HTGeometry.ConstraintRelativity.ResiduePromotionAnomaly          # green
```

`#print axioms` on `attachedDifferential_residue_cocycle_iff`,
`attachedDifferential_residue_cocycle_iff_range`, `compensatedDifferential_residue_cocycle_iff`,
`rank_le_of_compensates`, `exists_minimal_compensator`,
`fittedSplitting_compensatedDifferential`, `fittedSplitting_residue`,
`anomalyMap_eq_of_comparison`, `anomalyRank_eq_of_comparison`, `anomaly_scalar_eq_zero_iff`,
`linearIndependent_coordinatePowers`, `not_finiteDimensional_of_coordinateStable`,
`defectFactor_injective`, `no_holomorphic_defectCompensator`, `mixedCharge_two_legs`,
`mixedCharge_det`, `mixedCharge_not_rankOne`, `exists_separating_point`,
`mixedCharge_not_rankOne_on_open`, `infinite_xiC_nonvanishing`,
`not_finiteDimensional_of_xiC_coordinateStable` and `literal_defect_anomaly_eq_zero_iff` returns
only `[propext, Classical.choice, Quot.sound]` (several need no `Classical.choice` at all).
