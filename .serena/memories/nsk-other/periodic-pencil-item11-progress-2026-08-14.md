# periodic-pencil-intrinsic-ht-dimension-two — item (11) progress (2026-08-14)

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/periodic-pencil-intrinsic-ht-dimension-two.md`.
Only gate left is "complete unconditional Lean formalization" ⇒ orbit lemma `(11)` ⇒ `(9)`.
Card's programme: (i) assemble `famAevalWeight` at a square-free key, (ii) multi-node separation,
(iii) dominance, (iv) bridge to `DifferentialIndependent`.

## STEPS (i), (ii), (iii) ARE CLOSED (2026-08-14)

**Capstone** `HTGeometry/FamilyBoundedRelationSurvival.lean`, axiom-clean:

> **`exists_coeff_ne_zero_famJets_of_boundedRelation`** — for a source `H` with
> `coeff i H = u i · exp(−b i)`, `b`,`u` algebraic, `BoundedRelationConfinement b`, `u i ≠ 0`, and
> algebraic injective nonvanishing dilations `q`, every nonzero
> `Q : MvPolynomial (Option (ι × Fin (n+1))) ℂ` **with algebraic coefficients** has
> `∃ N, coeff N (aeval (familyJets n (fun i => rescale (q i) H)) Q) ≠ 0`.

**Key insight for (iii):** no bespoke dominant profile is needed.  The corpus's single-series
capstone `BoundedRelationExponentialSurvival.exists_coeff_ne_zero_of_boundedRelation_exponential`
does NOT use magnitude dominance — it groups atom keys by valuation, uses
`BoundedRelationConfinement` to make the star key's valuation fibre a singleton
(`atom_eq_of_valuation_eq_of_full_tail`), and finishes with finite Lindemann–Weierstrass
(`RHTower.exp_algebraic_relation_eq_zero`).  That transfers verbatim to families because a dilation
contributes only `q_i^{index}`, which lands in the *weight*, not the atom
(`coeff_aeval_famJets_regrouped` has the same atoms as the single-series expansion).

**Prior steps (i)+(ii)**, `HTGeometry/FamilyKeySeparation.lean`:
`exists_key_famAevalWeight_ne_zero(_of_mem)` — for every nonzero `Q`, every floor `K₀ ≥ n`, and any
prescribed `m₀ ∈ Q.support`, there is an injective key `k` with all parts `> K₀` and
`famAevalWeight q n (keyTrunc n m₀ k) Q (key k) ≠ 0`, where
`keyTrunc n m₀ k = m₀ none + ∑ k − slotOrderSum n m₀`.  Design point: letting the truncation follow
the key exposes a *fixed* monomial class, so the slot-sequence index set is `k`-independent.

Supporting modules (all umbrella-wired, axiom-clean): `DescPochhammerProductBasis`,
`MultiNodePolynomialSeparation`, `MultiNodeInjectiveParameter` (triangular substitution
`k_s = K₀+1+∑_{t≥s} m_t` turns "injective keys only" into "all positive tuples"),
`SlotSequenceSeparation` (`slotSequence_coeff_eq_zero`, `slotSequence_grouped_eq_zero`),
`FamilySquareFreeNodeForm`, `FlatIndexFiber`, `FamilySlotSequence`, `FamilyKeyInnerSum`,
`FamilyKeySeparation`.

## WHAT REMAINS

1. **Family Mahler normalization** — analogue of
   `FormalMahlerIntegerNormalization.formal_mahler_integer_normalization`, to drop the
   algebraic-coefficient hypothesis on `Q`.  CAUTION: the naive descent is FALSE for families of
   values (`x₁`, `c·x₁` with `c` a transcendental constant are ℂ-dependent, ℚ̄-independent) but TRUE
   for families of *jets* — the Wronskian `x₂ x₁′ − x₂′ x₁ = 0` eliminates the constant.  Reuse
   `FormalMahlerDescent` + `DifferentialAdjoinFiniteTrdeg`; the single-series route is
   "relation ⇒ DA over ℚ in the Laurent field ⇒ descend through finite trdeg ⇒ clear denominators".
2. **Step (iv)** — bridge the formal statement to `DifferentialIndependent` of the analytic orbit.
   The card records that `FormalMahlerDescent.formalJets` already carries the base variable, so only
   the family jet vector `Fin 1 ⊕ (ι × Fin (n+1))` is missing; the source is
   `BoundedRelationProfileRealization.exists_privatePrime_superlinear_profile_entire_fullSupport_hypertranscendental`
   (entire, full support, all Taylor coefficients nonzero, hypertranscendental for every algebraic
   unit-modulus phase sequence), and the orbit substitution is `ξ = e^{2πi u(z)}`, `q_α = e^{2πiα}`.

Lane otherwise dormant since 2026-07-31, so no concurrency risk.
See `mem:nsk-other/stage3-sweep-ledger-2026-08-13`.
