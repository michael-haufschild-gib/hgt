# Marked minimal response realization and doctrine-memory conservation — formalized

- **Paper card:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/marked-response-realization-mechanics/marked-minimal-response-realization-doctrine-memory-conservation-and-tensor-composition-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveMarkedResponseRealization`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

Lean certifies:

1. equal complete separating responses force equality of synthesis kernels;
2. surjective marked presentations admit one unique response-preserving linear equivalence;
3. doctrine-memory loss is exactly unreachable dimension plus unobservable dimension;
4. tensor formation multiplies pure responses and bounds restricted minimal memory by the product
   carrier dimension.

Verification used scratch elaboration, direct leaf elaboration, one targeted leaf build, and a
scratch `#print axioms` audit. No umbrella, area, or full-project build was run. Audited capstones
depend only on `propext`, `Classical.choice`, and `Quot.sound`.

This certifies finite-linear marked-presentation invariance. It does not claim categorical Morita
invariance, a literal common HGT source response, global formation properness, or RH selection.

## 2026-08-21 — complete word-level certification

The abstract linear surrogate above is superseded by
`GaloisForLFunctions.HTGeometry.MarkedWordRealization`, which proves the card's statements at the
literal word level.

| Card | Statement | Lean |
|---|---|---|
| (MR.1) | word action and complete response | `MarkedPresentation`, `wordAction`, `wordAction_append`, `response` |
| (MR.2)–(MR.3) | reachability and observability | `reachableSpan`, `Reachable`, `unobservable`, `Observable`, `Minimal`, `mem_unobservable_iff` |
| (MR.6) | the synthesis map and its kernel | `synthesis`, `range_synthesis`, `out_wordAction_synthesis`, `ker_synthesis_eq_of_response_eq` |
| Thm 2.1, (MR.4)–(MR.5) | unique minimal marked realization | `markedEquiv`, `markedEquiv_spec`, `markedEquiv_unique`, `existsUnique_markedEquiv` |
| (MR.7)–(MR.9) | restricted reachable/invisible spaces and the quotient presentation | `restrict`, `restrictedReachable`, `restrictedInvisible`, `restrictedStep`, `restrictedMinimal` |
| Thm 3.1, (MR.10) | the quotient is minimal and realizes the restricted law | `restrictedMinimal_response`, `restrictedMinimal_minimal`, `finrank_restrictedCarrier` |
| Thm 3.2, (MR.11) | memory conservation | `memory_conservation` |
| Cor 3.3, (MR.12) | exact no-go classification | `finrank_restrictedCarrier_eq_iff` |
| (MR.13) | the tensor presentation | `tensor`, `tensor_wordAction` |
| Thm 4.1, (MR.14) | the pointwise product law | `tensor_response` |
| Thm 4.1, (MR.15) | the memory bound | `finrank_tensor_minimalCarrier_le` |
| §6 | the Hankel realization | `shiftResponse`, `shiftOp`, `hankelSpan`, `hankelPresentation`, `hankelPresentation_response`, `hankelPresentation_minimal` |
| (MR.18) | the cofinal rank law | `rank_hankelSpan_le_of_finset_le`, `exists_finset_rank_gt_of_not_rank_le` |
| (MR.16)–(MR.17) | the complete star response and its Gram radical | `wordStar`, `wordStar_involutive`, `gramMap`, `gramRadical`, `gramOut` |
| Thm 5.1 | the GNS realization is a minimal cyclic realization; its dimension is the Gram rank | `gnsPresentation`, `gnsPresentation_response`, `gnsPresentation_minimal`, `gnsCarrierEquivRange` |

Notes on conventions and strength.

* Observability of the Hankel realization is automatic from its construction, and the same holds
  for the GNS realization, so Theorem 5.1's minimality needs no positivity hypothesis: the Gram
  radical is taken as the kernel of the complete word-context pairing, which is a submodule
  whatever the sign behaviour of `r`.  Positivity is therefore not assumed, and the theorem proved
  is strictly stronger than the card's.
* With the card's word convention `T_w = T_{a_n}⋯T_{a_1}` and the left GNS action, the realized
  response is `w ↦ r(reverse w)`; this is recorded explicitly in `gnsPresentation_response` rather
  than hidden in a convention.
* (MR.18) is proved in the contrapositive engine form: uniformly bounded shift ranks over all
  finite word sets force the whole Hankel span to have that rank, so an unbounded response has
  finite word sets of arbitrarily large rank.

62 public declarations, all axiom-clean.
