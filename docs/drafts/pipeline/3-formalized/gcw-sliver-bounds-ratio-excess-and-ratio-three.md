# Sliver Green bounds, step excess as a function of the ratio, and the four-step ladder to ratio three

- **ID:** gcw-sliver-bounds-ratio-excess-and-ratio-three
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.21
- **Lean modules:**
  - `formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheSliverBlocksOfTheGreenMatrixHaveALogarithmicDiagonalAndBulkDipoleCoupling.lean`
  - `formal/GaloisForLFunctions/GreenCalculusOfThePrimeFreeWindow/TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree.lean`
- **Statement:** Both `greenMatrix D` and `greenPositive D` on the dyadic middle `(D, 2D]` satisfy universal two-sided `Θ(1 / log D)` diagonal bounds across the entire middle and both boundary slivers (`1 / (2 log(2D)) ≤ greenMatrix D i i ≤ greenPositive D i i ≤ 1500 / log(2D)` for `D ≥ 2^256`, refuting `O(1/D)` sliver decay), small blocks `1 ≤ R ≤ 33` satisfy the first-step Green inequality unconditionally, and any sign-symmetric sliver-plus-bulk majorant omitting the signed bulk-to-sliver dipole cross-term `2 (endJet e)ᵀ G₊ (endContact e)` fails on `(R, 3R]` at every block size `R ≥ 1` (by the Liouville sign-twin obstruction). As a function of `(ρ, C)`, both `schurStepExcess Q ρ C` and `couplingStepExcess Q ρ C` are uniformly bounded across all block sizes `R ≥ 1` below `-neutralBlock 1 1 1`. Refining by `m = 2 q²` propagates `hermNegIndex ≤ 1` along `ρ = p/q ↦ ρ²/2` with zero integer-rounding loss across `103/50 → 10609/5000 → (> 9/4) → (> 253/100) → (> 3209/1000 > 3) → (> 321/100)`. Prime `2` is exact iff `J ≤ 2R` (up to ratio `3`), fails with `2 ≤ hermNegIndex` for `J ≥ 3R + 4` (`R ≥ 2`), and along the infinite ratio-squaring tower `globalTowerLevel` stays uniformly below `-neutralBlock 1 1 1` iff `globalTowerLevel k = 0` for all `k`, iff `RiemannHypothesis` holds.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorems in `GreenCalculusOfThePrimeFreeWindow`, `lake --old env lean` green, `#print axioms` clean (`[propext, Classical.choice, Quot.sound]`)

## Formalized Results and Lean Declarations

### 1. Sliver Green bounds, small-block closure, and bulk-to-sliver dipole obstruction (`TheSliverBlocksOfTheGreenMatrixHaveALogarithmicDiagonalAndBulkDipoleCoupling.lean`)

- **`bindingEnergy_lt_three`**: For all `1 ≤ D`, `-neutralBlock 1 1 1 ≤ bindingEnergy D ∧ bindingEnergy D < 3`.
- **`primeFreeMiddle_diag_bounds` & `sum_erase_primeFreeMiddle_sq_le`**: For `1 ≤ D` and `i : Fin D`, `log D - 5/2 ≤ primeFreeMiddle D i i ≤ log(2D)` and `∑_{j ≠ i} (primeFreeMiddle D i j)² ≤ 16`.
- **`groundVector_le`**: For `5 ≤ D` and `i : Fin D`, `groundVector D i ≤ 4 / (log D - 3/2)`.
- **`positiveChannel_diag_ge` & `greenPositive_diag_le_of_pos`**: Variational lower bound `((1 - φ_i²)²) / (M_{ii} + μ φ_i²) ≤ positiveChannel M φ μ i i` and self-consistent row-inversion upper bound on `greenPositive D i i`.
- **`greenMatrix_diag_bounds` & `abs_greenMatrix_entry_le`**: For all `2^256 ≤ D` and `i, j : Fin D`,
  `1 / (2 * log(2D)) ≤ greenMatrix D i i ≤ greenPositive D i i ≤ 1500 / log(2D)` and `|greenMatrix D i j| ≤ 1501 / log(2D)`.
- **`sqrt_div_eight_le_mul_greenMatrix_diag` & `not_exists_sliver_inv_bound`**: `(D : ℝ) * greenMatrix D i i ≥ √(2D) / 8` for `2^256 ≤ D`, so no constant `K` satisfies `greenMatrix D i i ≤ K / D` on the boundary slivers across all `D`.
- **`greenForm_of_firstStep_small` & `hermNegIndex_neutralWindow_eq_one_of_firstStep_small`**: For `1 ≤ R ≤ 33`, `100a ≤ 3R`, `50b ≤ 3(R + a)`, and `2 ≤ Q`, the Green inequality `(endCoupling e)ᵀ G₊ (endCoupling e) ≤ eᵀ endForm e + (φ_D ⬝ᵥ endCoupling e)² / μ_D` holds unconditionally and `hermNegIndex (neutralWindow Q R (a + (R + a) + b)) = 1`.
- **`endCoupling_eq_neg_endJet_sub_endContact`, `endContact_eq_zero_of_bulk`, `endForm_eq_one_of_le_three_mul`**: Exact decomposition `endCoupling = -endJet - endContact` with `endJet > 0`, `endContact = 0` on the interior bulk `{m | b ≤ 2m ∧ R + a + m < 2R}`, and `endForm Q R a b = endForm 1 R a b` for `2(R + a) + b ≤ 3R`.
- **`pencilCoupling_greenPositive_add_neg`, `pencilCoupling_greenPositive_sub_neg`, `exists_pencil_greenForm_gt`, `exists_primeFree_greenForm_gt`, `exists_signTwin_greenForm_gt`, `signTwin_obstruction`**: Polarization of `P(t) = -endJet - t • endContact` and failure of the Green inequality for every `t ∈ [-4, 0]` (including prime-free `t = 0` and Liouville sign twin `t = -1`) on `(R, 3R]` at every block size `R ≥ 1`; no functional majorizing `(P e)ᵀ G_D (P e)` and symmetric under `endContact ↦ -endContact` can lie below `eᵀ endForm e`.

### 2. Step excess as a function of the ratio (`TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree.lean`)

- **`windowExcess`, `couplingNorm`, `windowExcess_le_couplingNorm`, `windowExcess_le_sub`, `windowExcess_zero_eq_zero_iff_greenForm`**: Exact Schur-complement excess and conditional-coupling norm on `(R, 2(R + a) + b]`, sublinear level decrease below `bindingEnergy (R + a)`, and characterization of level-`0` vanishing by the Green inequality.
- **`hilbert_sum_le_six`, `dotProduct_mulVec_sq_le_of_inv_add`, `dotProduct_endCoupling_mulVec_sq_le`**: Integral-free discrete Hilbert sum `∑_{s < N} √r / ((r + s + 1)√(s + 1)) ≤ 6` (`1 ≤ r`), operator-norm bound `‖A‖_{2→2} ≤ 6 B` for `|A i j| ≤ B / (r_i + s_j)`, and block-size-independent bound `(w ⬝ᵥ (endCoupling Q R a b *ᵥ e))² ≤ (34 + 2 * primeContactSum Q)² (w ⬝ᵥ w)(e ⬝ᵥ e)`.
- **`IsRatioStep`, `isRatioStep_103_div_50_iff`, `schurStepExcess`, `couplingStepExcess`**: Exact ratio-step predicate (`IsRatioStep (103/50) R a b ↔ 1 ≤ R ∧ 100a ≤ 3R ∧ 50b ≤ 3(R + a)`) and ratio-indexed step excess functions over all block sizes `R ≥ 1`.
- **`schurStepExcess_le_analyticEnvelope`, `couplingStepExcess_le_analyticEnvelope`, `schurStepExcess_mono_ratio`, `schurStepExcess_le_sub`, `schurStepExcess_le_couplingStepExcess`, `schurStepExcess_zero_eq_zero_iff_greenForm`**: Closed-form all-block-size upper envelopes `schurAnalyticEnvelope Q ρ C` and `couplingAnalyticEnvelope Q C` for `-(1/5000) < C < -neutralBlock 1 1 1`, ratio monotonicity, level contractivity, and comparison with the conditional-coupling norm.

### 3. Sharp prime-`2` cutoff, ratios `2.25, 2.53, 3.21`, `(R, 3R]`, and global quantization (`TheExcessOfAnOverlapStepAndTheFourStepLadderToRatioThree.lean`)

- **`neutralWindow_eq_two_iff_le_two_mul`**: For `1 ≤ R` and `3 ≤ Q`, `neutralWindow Q R J = neutralWindow 2 R J ↔ J ≤ 2 * R`.
- **`two_le_hermNegIndex_primeTwo_two_six`, `two_le_hermNegIndex_primeTwo`, `primeThree_restores_positivity_two_six`**: Prime `2` alone fails past ratio `3` (`2 ≤ hermNegIndex` on `(2, 8]` and for every `2 ≤ R`, `3R + 4 ≤ J`), while `Q ≥ 3` restores a positive direction on `span{e₀, e₄ + e₅}` via `x ↦ ⌊x/3⌋`.
- **`hermNegIndex_le_one_of_sq_div_two`**: Refining by `m = 2 q²` propagates `hermNegIndex ≤ 1` from `(p/q, C)` to `((p/q)² / 2, C + schurStepExcess Q (p/q) C)` with zero rounding loss at every block size `R ≥ 1`.
- **`iteratedRatio_eq`, `iteratedRatio_milestones`, `hermNegIndex_le_one_of_levelAt`, `hermNegIndex_firstStep_le_one`**: Exact rational ratio sequence `iteratedRatio k = 2 * (103/100)^(2^k)` surpassing `10609/5000 = 2.1218` (`k = 1`, unconditional bound `hermNegIndex_firstStep_le_one`), `9/4 = 2.25` (`k = 2`), `253/100 = 2.53` (`k = 3`), `3209/1000 > 3` (`k = 4`), and `321/100 = 3.21` (`k = 5`).
- **`hermNegIndex_ratio_three_le_one`, `hermNegIndex_ratio_three_eq_one_of_levelAt_zero`, `hermNegIndex_ratio_three_eq_one_of_groundEnergy_nonneg`**: Four-step propagation to `(R, 3R]` at every block size `R ≥ 1` whenever `levelAt 2 3 < -neutralBlock 1 1 1`; `hermNegIndex = 1` on `(R, 3R]` when `levelAt 2 4 = 0`, or when `0 ≤ ccmRestrictedWeilGroundEnergy A` at an aperture `2 A.1 > log 3`.
- **`riemannHypothesis_iff_exists_lt_dyadicDepth_globalTowerLevel` & `riemannHypothesis_iff_globalTowerLevel_zero`**: Global `0`-or-escape quantization law: `RiemannHypothesis ↔ (∃ C < -neutralBlock 1 1 1, ∀ k, globalTowerLevel k ≤ C) ↔ (∀ k, globalTowerLevel k = 0)`.

## No-go closure
- **Obstructions proved:** (1) `not_exists_sliver_inv_bound` refutes `O(1/D)` sliver-block decay (`G_D(i, i) = Θ(1 / log D)`). (2) `signTwin_obstruction` refutes any sliver-plus-bulk upper bound invariant under `endContact ↦ -endContact` on `(R, 3R]`. (3) `two_le_hermNegIndex_primeTwo` refutes prime-`2`-only binding past ratio `3`.
- **Positive survivors formalized:** Uniform `Θ(1 / log D)` sliver Green bounds, `-neutralBlock 1 1 1 ≤ μ_D < 3`, unconditional Step-1 small-block closure (`1 ≤ R ≤ 33`), discrete Hilbert operator-norm bound (`‖endCoupling‖ ≤ 34 + 2 primeContactSum Q`), closed-form all-block-size envelopes for `schurStepExcess` and `couplingStepExcess`, zero-rounding rational ratio squaring across `2.06 → 2.1218 → 2.25 → 2.53 → 3.209 → 3.21`, aperture theorem for `(R, 3R]` at `2A > log 3`, and global quantization equivalence with `RiemannHypothesis`.
