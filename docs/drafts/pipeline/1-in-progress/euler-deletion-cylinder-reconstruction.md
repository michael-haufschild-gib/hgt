# Audit of finite-cylinder enrichment

- **Stage:** 1-in-progress
- **Type:** CONJECTURE under source audit
- **Question:** Does adjoining all finite coprime products create independent source data or only change coordinates?

The current corpus proves, for every nonempty finite pairwise-coprime set `B`,

`∏_{p∈B} a_p(n)=Σ_{∅≠S⊆B} (-1)^(|S|+1) a_{∏S}(n)`,

where `a_p(n)=1-p[p∣n]`. The converse candidate is

`a_{∏B}(n)=Σ_{∅≠S⊆B} (-1)^(|S|+1) ∏_{p∈S} a_p(n)`.

The proposed proof expands `1-∏_{p∈B}(1-a_p(n))` and uses coprimality only to identify the product divisibility indicator. This is finite inclusion–exclusion, with no analytic or zero input.

The audit must also cover higher chronological words. A finite linear change of source coordinates should act separately in every letter of every ordered word, preserving the entire strict time-ordering domain. Explicit finite sums will test this rather than infer it from level one or two.

If both directions and all-word transport hold, finite cylinder enrichment supplies no independent source condition beyond the original all-modulus path. This would retire the claim that cylinder closure is stronger input, while leaving open a genuinely additional law involving an infinite completion or new operation. Such a further law is not constructed here.

Source search used `scripts/formal_tools.py research` plus `rg`; relevant current sources are `EulerDeletionQuasiShuffleCylinderClosure`, `EulerDeletionQuasiShuffleOrderedDilation`, `EulerDeletionCompositeInterference`, and mathlib finite product-of-sums identities. The last source already proves that literal composite interleaving retains a nonzero overlap; replication cannot replace it.

No new RH mechanism or novelty is claimed. The strongest positive survivor sought is exact, invertible reconstruction of the arithmetic source and its complete family of finite ordered observables.
