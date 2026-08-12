# nad card `hausdorff-positive-higher-spin-cdd-cone` — **Hausdorff's moment theorem is PROVED**

Mathlib has no Hausdorff moment theorem.  It is now in the tree, in five modules, all axiom-clean
(`propext`, `Classical.choice`, `Quot.sound`) and wired into `GaloisForLFunctions.HTGeometry`.
The card already had necessity (`hausdorffMoment_isCompletelyMonotone`) and determinacy
(`hausdorffSource_eq_of_moments_eq`) in `HausdorffCDDMeasureSource.lean`.

## `HTGeometry/HausdorffQuadratureWeights.lean` — the algebra

```text
hausdorffCoeff  b N k = (-1)^(N-k) * (fwdDiff 1)^[N-k] b k          -- T(N,k)
hausdorffWeight b N k = (N.choose k) * hausdorffCoeff b N k
```

- **`hausdorffCoeff_refine`** — `T(N,k) = T(N+1,k) + T(N+1,k+1)` for `k ≤ N`.  The whole trick: it
  turns the mass identity into a one-line induction (with Pascal, `Finset.sum_range_succ'`,
  `Nat.choose_succ_self`), so **no double sum and no triangle reindexing** — mathlib has no lemma
  for `∑_{k≤N} ∑_{i≤N-k} = ∑_{n≤N} ∑_{k≤n}` (`exact?` finds nothing).
- **`sum_hausdorffWeight`** — every level has total mass `b 0`.
- `hausdorffCoeff_shift` (via `fwdDiff_iter_comp_add`), `choose_mul_descFactorial_shift` (via
  `Nat.choose_mul` and `Nat.descFactorial_eq_factorial_mul_choose`), and
  **`sum_hausdorffWeight_descFactorial`** — `∑ₖ w(N,k)·(k)ₘ = (N)ₘ·b m` for `m ≤ N`, reduced to the
  mass identity for the shifted sequence.

## `HTGeometry/HausdorffQuadratureMeasure.lean`

`integral_finsetWeightedDirac_general`, `hausdorffNode` (`k/N` clamped into `[0,1]`, with
`hausdorffNode_coe`), `hausdorffQuadrature` + `IsFiniteMeasure` instance,
`integral_hausdorffQuadrature`, `hausdorffQuadrature_mass`, `hausdorffMoment_hausdorffQuadrature`.

## `HTGeometry/HausdorffNodeComparison.lean`

`pow_sub_pow_le_nsmul_sub` (`a^m − b^m ≤ m(a−b)` on `0 ≤ b ≤ a ≤ 1`), `cast_descFactorial_eq_prod`,
`descFactorial_ratio_eq_prod`, and **`abs_node_pow_sub_ratio_le`**:
`|(k/N)^m − (k)ₘ/(N)ₘ| ≤ m²/N` for `m ≤ N`, `k ≤ N`, `0 < N`.  Above the diagonal the ratio is
`∏ (k−i)/(N−i)`, each factor between `(k−m+1)/N` and `k/N`, so it is squeezed between the two
corresponding powers; below it the ratio vanishes and `x^m ≤ x = k/N < m/N`.

## `HTGeometry/HausdorffMomentTheorem.lean`

`sum_hausdorffWeight_ratio`, `abs_hausdorffMoment_hausdorffQuadrature_sub_le`,
`tendsto_hausdorffMoment_hausdorffQuadrature`, `hausdorffTest`, `eq_of_clusterPt_of_tendsto`,
`hausdorffCompletelyMonotone_antitone`, `hausdorffCompletelyMonotone_nonneg`, and

- **`exists_hausdorffSource_of_completelyMonotone`**
- **`hausdorffCompletelyMonotone_iff_exists_source`**
- **`existsUnique_hausdorffSource_of_completelyMonotone`**
- `hausdorffMoment_strict_completelyMonotone` (equation `(9)`).

**No metrizability is needed for the limit**: `CompactSpace (ProbabilityMeasure ↥(Icc 0 1))` is an
instance, `exists_clusterPt_of_compactSpace` gives a cluster point, and
`ProbabilityMeasure.continuous_integral_boundedContinuousFunction` + `ClusterPt.map` +
`eq_of_clusterPt_of_tendsto` pin its moments.  The case `b 0 = 0` forces `b = 0` by antitonicity and
nonnegativity; the zero measure serves.

## `HTGeometry/HausdorffStrictCddCone.lean`

`geometricCombination_strict_completelyMonotone`, `cddCoupling_strict_completelyMonotone` —
equation `(10)` in strict form for a nonempty positive shell configuration inside `(0,1)`.

## Card status — still NOT promotable

Theorem A is unconditional in both directions with uniqueness, and `(9)`/`(10)` strictness is done.
Still unformalized:

1. `(11) = (13)` — the sinh series equals the source transform.  Needs the arctan power series
   (`arctan t = ∑ (-1)^m t^{2m+1}/(2m+1)` for `|t| ≤ 1`; check whether mathlib has it), the pointwise
   kernel identity `K(y,θ) = 8 ∑ (-1)^m y^m sinh((2m+1)θ)/(2m+1)` valid when `√y·e^{|θ|} ≤ 1`, and a
   series/integral interchange with a geometric majorant.
2. the extreme-ray dictionary `(18)` as a classification statement (the atom laws
   `hausdorffCDDPhase_atom`, `_zero_atom`, `_shell_atom` already exist);
3. the geometric q-ladder instance `(19)`: needs the `arccosh` estimate `r_j ≍ q^j/(2C)` to see the
   atomic family is summable and lands strictly inside `(0,1)`; the strict inequalities then follow
   from the two theorems above.

The card's other open gates (global regularity for non-atomic measures, quasilocal density and
compact-local QFT flow, universality from locality/unitarity) are research items, not formalization
ones.
