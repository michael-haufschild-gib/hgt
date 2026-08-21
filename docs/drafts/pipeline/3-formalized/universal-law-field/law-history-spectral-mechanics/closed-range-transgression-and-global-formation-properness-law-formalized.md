# Closed-range transgression and global formation properness — Lean certification

- **ID:** ULF-LHSM-4
- **Paper card:** `closed-range-transgression-and-global-formation-properness-law.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.ClosedRangeTransgression`,
  `GaloisForLFunctions.HTGeometry.ClosedRangeTransgressionCountermodel`
- **Universal-law umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## Certified declarations

### Lemma 2.1 — quotient strictness (CRP.5)

`preimage_image_mkQ` identifies the saturation `π⁻¹(π(N)) = N + P` for the quotient map of any
submodule of a topological module, and `isClosed_image_mkQ_iff` turns it into the equivalence

```text
IsClosed (P.mkQ '' N)  ↔  IsClosed (N ⊔ P)
```

using that `mkQ` is an open quotient map.  No Hilbert structure and no completeness are needed:
the statement holds over an arbitrary topological ring acting on a topological module.

### Lemma 3.1 — product strictness (CRP.6)

The Hilbert half is `isClosed_map_iff_isClosed_sup_ker`:

```text
IsClosed (A.map g)  ↔  IsClosed (A ⊔ ker g)
```

for a bounded `g` of closed range.  The proof replaces `A` by its `ker g`-saturated form
(`map_eq_map_starProjection`, `sup_ker_eq_sup_ker_starProjection`) and then transports along
`isClosedEmbedding_on_ker_orthogonal` — the restriction of `g` to `(ker g)ᗮ` is a closed embedding,
because it is a continuous linear bijection onto the closed subspace `ran g` and hence has
continuous inverse by the open mapping theorem.  `isClosed_ker_coe`,
`apply_starProjection_ker` and `starProjection_ker_orthogonal_mem` are the supporting facts.

### Theorem 4.1 — closed-range transgression theorem (CRP.8)

`closedRange_transgression_tfae` proves the three-way equivalence for `X →f Y →g Z` with
`ran g` closed:

```text
IsClosed (ran (g ∘ f))  ↔  IsClosed (ran f ⊔ ker g)  ↔  IsClosed (mkQ (ran f) '' (ker g))
```

The last clause is exactly the card's transgression `δ_{f,g} : N → Y/M`, `n ↦ [n]`: its range is
`mkQ (ran f) '' (ker g)`, so the third clause says the transgression has closed range.

### Corollary 5.2 — Friedrichs-angle form (CRP.10)

`friedrichsCosine_lt_one_iff_isClosed_range_comp` combines Theorem 4.1 with the corpus's
`friedrichsCosine_lt_one_iff_isClosed_sup`, giving

```text
c(ran f, ker g) < 1  ↔  IsClosed (ran (g ∘ f))
```

whenever `ran f` and `ker g` are closed and `ran g` is closed.

### Section 6 — finite-history global properness (CRP.13)–(CRP.14)

`prefixMap V a n : V 0 →L V n` is the composite of the first `n` laws of a history
`a n : V n →L V (n+1)`, `prefixTransgressionRange n` is the range of the `n`-th prefix
transgression inside `V n ⧸ ran (prefixMap n)`, and

* `isClosed_range_prefixMap_succ_iff` is the one-step induction `(CRP.13)`;
* `globally_proper_iff_transgressions_closed` is Theorem 6.2 `(CRP.14)`: given that every single
  law has closed range, every prefix composite has closed range **iff** every prefix transgression
  has closed range.

### Theorem 7.1 — terminal closedness is not global properness (CRP.16)–(CRP.19)

Abstract form: `terminal_closedness_not_global_properness`.  For closed subspaces `M`, `N` of a
Hilbert space with `M + N` non-closed, the inclusion `M.subtypeL` and the orthogonal projection
`(Nᗮ).starProjection` have closed range (`isClosed_range_subtypeL`,
`ker_range_starProjection_orthogonal`), their composite has non-closed range, and post-composing
with the zero map gives range `⊥`, which is closed.  That is the card's `(CRP.19)`.

Explicit model, in `ClosedRangeTransgressionCountermodel`:

* `doubleFst`, `doubleSnd`, `doubleInr` are the coordinates and the second-summand section of the
  orthogonal double `E ⊕₂ E = WithLp 2 (E × E)`;
* `firstSummand` is `E ⊕ 0` (kernel of `doubleSnd`) and `graphSubmodule T` is the graph of a
  bounded `T` (kernel of `doubleSnd − T ∘ doubleFst`); both are closed as kernels of bounded maps
  (`isClosed_firstSummand`, `isClosed_graphSubmodule`);
* `firstSummand_sup_graphSubmodule` is `(CRP.18)`: the sum is the `doubleSnd`-preimage of `ran T`;
* `not_isClosed_firstSummand_sup_graphSubmodule` pulls non-closedness back along the continuous
  section `doubleInr`;
* `decayBlock`/`decayOperator` is the card's `(CRP.16)` operator
  `T(x₁, x₂, …) = (x₁, x₂/2, x₃/3, …)` on `ℓ²(ℕ; 𝕜)`, built with the corpus's
  `blockOperator`; `not_isClosed_range_decayOperator` is its dense-but-proper range, from
  `not_isClosed_range_blockOperator`;
* `counterFirst`, `counterGraph` are `(CRP.17)`, `not_isClosed_counterFirst_sup_counterGraph`
  is the non-closed sum, and `counter_terminal_closedness_not_global_properness` is the finished
  countermodel — non-closed middle prefix, closed terminal range.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ClosedRangeTransgression.lean
lake env lean GaloisForLFunctions/HTGeometry/ClosedRangeTransgressionCountermodel.lean
```

Both elaborate with no errors and no warnings.  `#print axioms` on all 18 + 22 public
declarations reports only `propext`, `Classical.choice`, `Quot.sound`.  Both modules are imported
by `GaloisForLFunctions.HTGeometry` and by
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Card Lean requirements (§11)

1. quotient-image closedness iff saturated sum closed — `isClosed_image_mkQ_iff`;
2. product closedness iff `ran f + ker g` closed — `isClosed_map_iff_isClosed_sup_ker`;
3. transgression closedness equivalence `(CRP.8)` — `closedRange_transgression_tfae`;
4. finite-history induction `(CRP.13)`–`(CRP.14)` — `isClosed_range_prefixMap_succ_iff`,
   `globally_proper_iff_transgressions_closed`;
5. explicit graph/projection countermodel `(CRP.16)`–`(CRP.19)` —
   `counter_terminal_closedness_not_global_properness` and its supporting chain;
6. no full umbrella build — only the two new oleans were compiled.
