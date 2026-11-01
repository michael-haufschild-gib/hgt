# Nonzero proper subgroup carriers have a canonical relative split

- **ID:** NONZERO-PROPER-SUBGROUP-RELATIVE-SPLIT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-3110/route-obstacles.md` A14; [integer Haar split](finite-index-haar-carriers-split-modulo-polynomial-kernels.md); [proper-subgroup index law](proper-subgroup-carriers-preserve-polynomial-fibre-indices.md).
- **Statement:** For every nonzero proper additive subgroup `H < ℚ`, every Hermitian kernel `k` on `Aff(ℚ)` with finite negative index and translation reading `1_H` has a unique decomposition `k = p + ψ∘slope + q`: `p` positive definite with successor `1_H`, `ψ` Hermitian on `ℚˣ`, `q` Hermitian of finite column rank with polynomial translation fibres, vanishing on all translations and dilations. Moreover `κ(k) = κ(ψ∘slope + q) ≥ κ(ψ)`.

## Proof

**Normalization.** Pick `a ∈ H`, `a ≠ 0`, and conjugate by the dilation `d_a`. The pulled-back
kernel `k ∘ c_a` has translation reading `1_{H'}` with `H' = a⁻¹H ∋ 1`, `H' ≠ ℚ`, and index at most
`κ(k)`. Conjugation fixes dilations and the slope, sends `translation b` to `translation(ab)`, and
pulls back positivity, Hermitian symmetry, polynomial fibres (`P(b) ↦ P(b/a)`) and finite column
rank (columns of `q ∘ c` lie in the image of the column span of `q` under precomposition).

**Integer period defect.** Since `1 ∈ H'`, the reading is `1`-periodic. The zero-axis polynomial
correction gives `q` of finite rank, polynomial fibres, zero on both axes, with `k − q` integer
invariant, Hermitian, finite index, and still of successor `1_{H'}`.

**Positive part.** For the integer-invariant remainder `k₀`, the cyclic moving forms along the
factorial steps `1/n!` increase, and every column has moving norm `≤ 1`: the fixed projection of a
column `g` along step `b` has norm `1/ord_{H'}(b/slope g)` (reciprocal quotient order). The bounded
monotone forms converge to an affine-invariant nonnegative form; its coefficient `p` is positive
definite. The fixed projection of the identity along `1/n!` has norm `1/ord_{H'}(1/n!) → 0` because
factorial orders diverge modulo a proper subgroup containing `1`. Hence `p(1) = 1`. The discarded
form is invariant under every rational translation, so `k₀ − p` is a function `ψ` of the slope and
`p(translation b) = k₀(translation b) = 1_{H'}(b)`.

**Index and uniqueness.** `ψ∘slope + q` has polynomial translation fibres, so positive `1_H`
carriers preserve its index: `κ(k) = κ(ψ∘slope + q)`; restricting to dilations gives `κ(ψ)`. If two
splits agree, `p − p'` has polynomial fibres, and positive `1_H` carriers are polynomially rigid,
so `p = p'`; evaluation on dilations (where `q, q'` vanish) gives `ψ = ψ'`, then `q = q'`.

## Lean

- `AdelicKreinGeometry/Haar/SubgroupPositivePart.lean`: `subgroup_translationMovingForm_point_le_one`,
  `subgroup_tendsto_haarMovingLimit`, `subgroup_haarMovingLimit_invariant`,
  `subgroup_haarPositivePart_posDef`, `subgroup_haarPositivePart_one`,
  `subgroup_haarPositivePart_hasSubgroupSuccessor`, `subgroup_haarPositivePart_add_slope`,
  `negIndex_subgroup_haarSlopePart`, `negIndex_comp_slopeUnit`.
- `AdelicKreinGeometry/Haar/SubgroupRelativeSplit.lean`: `exists_subgroup_relative_split_of_one_mem`,
  `subgroup_relative_split_unique`, `negIndex_subgroup_relative_split`,
  `exists_unique_subgroup_relative_split`, `finite_kernelColumnSpan_comp`, `dilationConjugation`.

Both modules pass `lake --old env lean`; oleans built. `#print axioms` for the three capstones:
`propext`, `Classical.choice`, `Quot.sound`. Wired into `AdelicKreinGeometry.lean`.

## Gates

- [x] Normalization, finite-rank transport and limit dependencies proved.
- [x] Exact split, uniqueness and index law formalized.
- [x] Direct checks and standard axiom closures.
