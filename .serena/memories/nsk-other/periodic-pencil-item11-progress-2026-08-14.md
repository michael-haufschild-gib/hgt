# periodic-pencil-intrinsic-ht-dimension-two — item (11) progress (2026-08-14)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/periodic-pencil-intrinsic-ht-dimension-two.md`.
Only gate left is "complete unconditional Lean formalization", which reduces to the orbit lemma
`(11)`, hence to `(9)`.  Four-step programme: (i) assemble `famAevalWeight` at a square-free key,
(ii) multi-node separation, (iii) dominant profile, (iv) bridge to `DifferentialIndependent`.

## STEPS (i) AND (ii) ARE CLOSED (this session)

Capstone, axiom-clean, in `HTGeometry/FamilyKeySeparation.lean`:

> **`exists_key_famAevalWeight_ne_zero`** — for injective nonvanishing `q` and every nonzero
> `Q : MvPolynomial (Option (ι × Fin (n+1))) ℂ` there are `m₀` and an injective
> `k : Fin (∑ p, m₀ (some p)) → ℕ` with all `k s > n` such that
> `famAevalWeight q n (keyTrunc n m₀ k) Q (key k) ≠ 0`,
> where `keyTrunc n m₀ k = m₀ none + ∑ k − slotOrderSum n m₀`.

and its equivalent `coeff_eq_zero_of_famAevalWeight_key_vanishing`.

**The design point** (do not rederive): a split realizing key `k` has `∑ l = ∑ k − ord m`, while the
truncation forces `∑ l = N − m none`, so a *fixed* `N` exposes a different monomial family for each
key.  Letting `N` follow the key (`keyTrunc`) exposes the fixed class `keyClass` (same slot count as
`m₀`, same `m none − ord m`), over which the key weight is a sum of slot-sequence contributions
indexed by (monomial, ordering) — `k`-independent — so one separation sees every key at once.

New modules (all umbrella-wired, build green, axiom-clean):
- `DescPochhammerProductBasis` — `descProdSymbol`, `descProdSymbol_combination_eq_zero`
  (falling-factorial products linearly independent, via maximal total order), `eval_descProdSymbol_map`.
- `MultiNodePolynomialSeparation` — `mvPolynomial_nodeSeparation`.
- `MultiNodeInjectiveParameter` — `mvPolynomial_nodeSeparation_injective`; TRICK: the triangular
  substitution `k_s = K₀+1+∑_{t ≥ s} m_t` is injective for every positive `m`, sends node tuple `Z`
  to initial products `∏_{s ≤ t} Z_s` (injective), and composes polynomials with an invertible
  affine map.  **Note the floor `K₀` is a free parameter** — see the generalization below.
- `SlotSequenceSeparation` — `slotSequence_coeff_eq_zero` and the grouped
  `slotSequence_grouped_eq_zero`.
- `FamilySquareFreeNodeForm` — `sum_famWeight_squareFreeKey_node_form`.
- `FlatIndexFiber` — `card_filter_flatIndex` (fibres of the flattening = the exponents).
- `FamilySlotSequence` — `exists_slotSeq_of_key`, `slotLabel`, `slotCount_eq_of_key`.
- `FamilyKeyInnerSum` — `slotOrderSum`, `slotSeqOf`, `sum_famWeight_key_eq_slotSeq`.
- `FamilyKeySeparation` — `keyTrunc`, `keyClass`, `famAevalWeight_expand`,
  `mem_keyClass_of_contributes`, `famAevalWeight_key_eq_class_sum`, the two capstones.

## NEXT: the floor generalization, then step (iii)

**First, cheap and needed:** thread a floor `K₀ ≥ n` through
`slotSequence_coeff_eq_zero` / `FamilyKeySeparation` (replace `∀ s, n < k s` by `∀ s, K₀ < k s`).
`mvPolynomial_nodeSeparation_injective` already takes the floor, and `exists_slotSeq_of_key` only
needs `n < k s`, so it is pure plumbing.  It gives keys arbitrarily far out — which is what the
dominance step needs.

**Step (iii)** is the family analogue of the single-series dominance capstone
`BoundedRelationExponentialSurvival.exists_coeff_ne_zero_of_boundedRelation_exponential`
(~300 lines): a *single* profile `b`, independent of `Q`, making a far-out square-free key strictly
dominant.  The mechanism there is `BoundedRelationConfinement b` (every integer relation
`∑ d_n b_n = 0` with `|d_n| ≤ D` is supported below some `M = M(D)`) plus an "eventually balanced"
key; the source is `BoundedRelationProfileRealization.exists_privatePrime_superlinear_profile_…`
(entire, full support, hypertranscendental).  Target: feed
`FamilyDilatedMagnitude.famAeval_coeff_ne_zero_of_dominant` with `hw₀` from
`exists_key_famAevalWeight_ne_zero`, `hgap` from confinement, `hG` from the gap.

**Step (iv)** bridges the formal statement to `DifferentialIndependent` of the analytic orbit;
`FormalMahlerDescent.formalJets` already carries the base variable, only the family jet vector is
missing.

Lane otherwise dormant since 2026-07-31, so no concurrency risk.
See `mem:nsk-other/stage3-sweep-ledger-2026-08-13`.
