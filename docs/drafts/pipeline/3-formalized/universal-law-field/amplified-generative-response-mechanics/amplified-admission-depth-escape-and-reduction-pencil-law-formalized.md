# Amplified admission depth escape and reduction pencil — Lean certification

- **ID:** `ulf-agrm-reduction-pencil-depth-escape`
- **Paper card:** `amplified-admission-depth-escape-and-reduction-pencil-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ReductionPencilKPositivity`,
  `GaloisForLFunctions.HTGeometry.AmplifiedAdmissionGauge`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## New reusable content

Mathlib has no `k`-positivity theory, no Schmidt decomposition and no reduction-map threshold.
`ReductionPencilKPositivity` supplies all of it from scratch, and does so **without** singular
values: the whole sufficiency argument is Cauchy–Schwarz for the positive semidefinite sesquilinear
form of `A`, applied to two different decompositions of the test vector.

* `matSesq` — the sesquilinear form of a matrix, with its bilinearity, conjugate symmetry,
  positivity and `matSesq_conjugate` (`matSesq (Bᴴ M B) x y = matSesq M (B *ᵥ x) (B *ᵥ y)`);
* `matSesq_norm_sq_le` — Cauchy–Schwarz, obtained from the corpus's own
  `HTGeometry.cauchy_schwarz_psd` rather than reproved;
* `matSesq_self_re_le_sq_sum_sqrt` — the **master estimate**: for any finite decomposition
  `x = ∑ f p` of the test vector,
  `Re ⟪x, A x⟫ ≤ (∑ p, √(Re ⟪f p, A (f p)⟫))²`,
  together with its cardinality form `matSesq_self_re_le_card_mul` and its majorant form
  `matSesq_self_re_le_sq_sum`;
* `matSesq_partialTraceRight` — the partial trace tested at `x` is the sum over the aperture of the
  tests of `A` at the lifted slices, hence `posSemidef_partialTraceRight`;
* `partialTraceRight_kron_conj` —
  `Tr_β ((V ⊗ 1) A (V' ⊗ 1)) = V (Tr_β A) V'`, the ancilla-rotation covariance of the partial
  trace.

`AmplifiedAdmissionGauge` supplies the amplification calculus:

* `ampMatMap`, `IsLevelPositive`, `IsCompletelyPositiveMap`, with additivity, homogeneity,
  composition and `ampMatMap_submatrix` (all definitional);
* `isLevelPositive_of_surjective` — positivity descends along *any* surjection of ancilla indices,
  proved purely with `Matrix.PosSemidef.submatrix` in both directions; hence
  `isLevelPositive_fin_antitone`, the card's "restrict to a matrix corner";
* `levelFeasible_eq_Ici` — the **attainment** theorem, proved by an elementary
  `ε`-perturbation argument (no topology, no closedness of the PSD cone): the Hermitian part is
  pinned by one positive `ε` and the quadratic form by letting `ε` shrink.

## Certified declarations

### Theorem 1.1 — amplified conservation and data processing

* `levelFeasible`, `levelGauge` — (AGR.1); `completeGauge` — (AGR.2).
* `levelFeasible_antitone`, `levelGauge_mono` — the sequence `κ_k` is nondecreasing.
* `levelFeasible_up` — with a completely positive comparison map the feasible set is an upper set.
* `levelFeasible_eq_Ici` — the feasible set is exactly `[κ_k, ∞)`; this is the finite-dimensional
  endpoint attainment the card records.
* `isCompletelyPositiveMap_iff_forall_levelGauge_le` — **(AGR.3)**:
  `η + cμ` is completely positive `↔` `c ≥ κ_k` for every `k`.
* `levelFeasible_subset_comp`, `levelGauge_comp_le` — **(AGR.4)**:
  `κ_k(BηA | BμA) ≤ κ_k(η | μ)`.  A completely positive observer may erase an amplified
  obstruction but cannot create one.

### Theorem 2.1 — the exact reduction-pencil threshold

`redPencil c A = c · (Tr_β A) ⊗ 1 − A` is `id_α ⊗ Φ_{n,c}` (`ampMatMap_reduction`).

* `redPencil_posSemidef_of_card_right_le` — the **aperture half**: `c ≥ card β` always works.
  Decompose the test vector into its `β`-slices; the trace term dominates the diagonal slice terms
  and the master estimate pays the factor `card β`.
* `redPencil_posSemidef_of_card_left_le_of_diagonal` — the **amplification half** when the partial
  trace is diagonal: decompose into `α`-slices, bound each slice by
  `(Tr_β A)_{aa} · ‖φ_a‖²` (master estimate again, with the Cauchy–Schwarz majorant), and pay the
  factor `card α`.
* `redPencil_posSemidef_of_card_left_le` — the general amplification half: conjugate by
  `U ⊗ 1` for the unitary `U` diagonalizing `Tr_β A` (`Matrix.IsHermitian.eigenvectorUnitary`),
  transport with `partialTraceRight_kron_conj`, and transport positivity back.
  *The rotation is essential*: without it the slice bound is false, as
  `Tr_β A = ½·(all ones)` shows.
* `entangledVec`, `entangledMat`, `entangledMat_posSemidef`,
  `exists_posSemidef_not_redPencil_posSemidef` — **necessity**: for any pair of orthonormal
  families `u : ι → α → ℂ`, `v : ι → β → ℂ` the maximally entangled vector rejects every
  `c < card ι`.  The proof needs no Schmidt theory: the partial trace acts as the identity on the
  entangled vector.
* `redPencil_posSemidef_forall_iff` — **(AGR.6)**, the capstone:
  `id_α ⊗ Φ_{n,c}` is positive `↔` `c ≥ min (card α) (card β)`.
* `isLevelPositive_reduction_iff`, `levelGauge_reduction` — **(AGR.7)**:
  `κ_k(η_n | T_n) = min k n`; `isGreatest_completeGauge_reduction` and
  `completeGauge_reduction`: `κ_cp(η_n | T_n) = n`.

### Theorem 3.1 and Section 4 — cofinal migration and false promotion

* `isGreatest_fixed_depth_reduction` — **(AGR.12)**: `sup_n κ_k(η_n | T_n) = k`, attained at
  `n = k`.
* `completeGauge_reduction_not_bddAbove` — **(AGR.13)**: `sup_n κ_cp(η_n | T_n) = +∞`.
* `reduction_false_promotion` — **(AGR.14)**: separate uniform bounds at every fixed amplification
  depth do not promote to one uniform complete bound.  The rejecting depth migrates along the
  diagonal `(n, k) = (n, n)`.

## Not claimed

Sections 5–7 of the card are grammar, frontier predictions and an explicit *negative*: §7 states
that no arithmetic operator system realizing (AGR.16) currently exists, and §8 disclaims any route
theorem.  Those two open gates are therefore future research, not unformalized proved theorems.
§9 attributes (AGR.1)–(AGR.7) to Hou–Li–Poon–Qi–Sze and Kian; the Lean development here is
independent and self-contained.

## Verification

```text
lean -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/ReductionPencilKPositivity.olean \
  GaloisForLFunctions/HTGeometry/ReductionPencilKPositivity.lean
lean -o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/AmplifiedAdmissionGauge.olean \
  GaloisForLFunctions/HTGeometry/AmplifiedAdmissionGauge.lean
```

Both compile with no errors.  `#print axioms` on
`redPencil_posSemidef_forall_iff`, `redPencil_posSemidef_of_min_le`,
`exists_posSemidef_not_redPencil_posSemidef`, `redPencil_posSemidef_of_card_left_le`,
`redPencil_posSemidef_of_card_right_le`, `levelGauge_mono`, `levelFeasible_eq_Ici`,
`isCompletelyPositiveMap_iff_forall_levelGauge_le`, `levelGauge_comp_le`, `levelGauge_reduction`,
`completeGauge_reduction`, `isGreatest_fixed_depth_reduction`, `reduction_false_promotion` and
`isLevelPositive_reduction_iff` reports only `propext`, `Classical.choice`, `Quot.sound`.
Both modules are imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Exact field consequence

Amplification depth and source aperture are genuinely independent admission axes.  The obstruction
of the reduction pencil is invisible at every fixed depth uniformly in the aperture, and only the
*joint* bound over the product-directed set `(aperture, depth)` sees it.  Any selector built from a
fixed-degree positivity theorem is therefore blind to the diagonal escape, whatever the degree.
