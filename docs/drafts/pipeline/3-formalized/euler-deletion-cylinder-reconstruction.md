# Finite deletion cylinders and all ordered words reconstruct each other

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); finite-enrichment claim retired
- **Result:** Mutual reconstruction of the actual finite source families, every strict chronological word, and every choice of conjugated letters.

For `a_p(n)=1-p[p divides n]`, the corpus already proves, for every nonempty finite pairwise-coprime set `B`,

`∏_{p∈B} a_p(n)=Σ_{∅≠S⊆B} (-1)^(|S|+1) a_{∏S}(n)`,

The converse is now also proved:

`a_{∏B}(n)=Σ_{∅≠S⊆B} (-1)^(|S|+1) ∏_{p∈S} a_p(n)`.

Both identities hold before weights, cutoffs, or zero selection. The common weight `n^(-s)` is applied once after multiplying the coefficients. The same two reconstructions then hold for the weighted source families.

## Exact all-word statement

Fix a finite pairwise-coprime family `F`. Index both source descriptions by its nonempty subsets. For a subset `B`, let `A_B(n)=a_(prod B)(n)n^(-s)` and `C_B(n)=(prod_(p in B)a_p(n))n^(-s)`. Set

`M(B,D)=(-1)^(|D|+1)` when `empty≠D⊆B`, and `0` otherwise.

Then `C_B=Σ_D M(B,D)A_D` and `A_B=Σ_D M(B,D)C_D` at every integer. For every word `(B_1,...,B_k)`, every length `k`, and every finite cutoff `N`, the strict chronological observable

`Σ_(0≤n_1<...<n_k<N) C_(B_1)(n_1)...C_(B_k)(n_k)`

equals the sum over choices `(D_1,...,D_k)` of the corresponding `A` observable multiplied by `∏_j M(B_j,D_j)`. The reverse formula is identical with `A,C` exchanged. Each letter may independently be conjugated; real coefficients make both formulas hold with the same matrix. This includes the Hermitian words used in the proposed second-level argument.

Simultaneous zero endpoints of all these cylinder channels are equivalent to simultaneous zero endpoints of the product-modulus channels, under the same chronological cutoffs. No assumption about `Re(s)` or a zeta zero is needed for this equivalence.

## Paper proof

1. Since `1-a_p(n)=p[p divides n]`, pairwise coprimality gives `prod_(p in B)(1-a_p(n))=(prod B)[prod B divides n]`. Expanding its complement by finite inclusion–exclusion proves the reverse coefficient formula. This also covers the empty family: the modulus-one channel and the empty alternating sum are both zero.
2. Multiply both coefficient identities by the single common Dirichlet weight. Every subset of a positive pairwise-coprime family remains positive and pairwise coprime. Extending each subset sum by zeros to the fixed index set gives the matrix formulas above.
3. For a fixed strict schedule `(n_1,...,n_k)`, distribute the product of the `k` finite coordinate sums. The result is a sum over all label choices, with the coefficient product separated from the source product. Interchange the two finite sums. The strict schedule is preserved exactly. Conjugation commutes with the real coordinate coefficients, proving the decorated version.
4. Summing the source formulas through `N` gives finite combinations of the original prefixes. Finite sums and multiplication by constants preserve convergence to zero. Apply this in both directions for the endpoint equivalence.

These arguments are dependency-closed and symbolic; no numerical experiment is used.

## Exact finite expansion cost

For a row indexed by `B`, `Σ_D |M(B,D)|=2^|B|-1`, because each nonempty subset contributes exactly one. For a word, the absolute coefficient sum is

`∏_j (2^|B_j|-1)`.

Both formulas are Lean-proved. Consequently finite reconstruction alone does not establish bounds uniform in the number of generators or word length. The formulas quantify coefficient expansion; they do not assert that the actual arithmetic source attains a worst-case norm, or identify any infinite completion.

## No-go closure and survivor

- **Retired claim:** finite cylinder closure is independent, stronger data than the original all-modulus closure, or merely adjoining its higher finite ordered words supplies an independent source condition.
- **Exact certificate:** the two source reconstructions, endpoint equivalence, and both all-word reconstructions above.
- **Positive survivor:** the entire finite arithmetic source can be recovered in either presentation, with an explicit absolute coefficient budget at every word length.
- **Scope:** a coordinate presentation may still help prove a new theorem. This result does not rule out a new operation or an infinite completion with additional proved control. Neither is supplied here. It is not a no-go for every deletion-based RH argument.

Source search used `scripts/formal_tools.py research` plus `rg`; relevant current sources are `EulerDeletionQuasiShuffleCylinderClosure`, `EulerDeletionQuasiShuffleOrderedDilation`, `EulerDeletionCompositeInterference`, and mathlib finite product-of-sums identities. `EulerDeletionCompositeInterference` already proves that literal composite interleaving retains a nonzero overlap; replication cannot replace it.

Bounded query wording and requested retrieval caps are in [the search manifest](euler-deletion-reconstruction-periodicity-searches.tsv); these are not claims of exhaustive proof inspection.

The underlying iterated-sum machinery is published: Diehl–Ebrahimi-Fard–Tapia, [*Iterated-sums signature, quasi-symmetric functions and time series analysis*](https://diehlj.github.io/FPSAC2020.pdf), equation (1.4), and [*Generalized iterated-sums signatures*](https://arxiv.org/abs/2012.04597). These sources establish ancestry; no novelty claim is made for finite multilinearity or the present arithmetic specialization.

## Lean evidence

Module: `formal/GaloisForLFunctions/RHTower/EulerDeletionCylinderReconstruction.lean`, namespace `RHTower.DeletionCylinderReconstruction`.

- `blockDeletionCoefficient_product_eq_cylinders`: reverse coefficient reconstruction.
- `cylinderSource_eq_coordinates`, `baseSource_eq_coordinates`: actual weighted source formulas.
- `cylinder_orderedWord_eq_base`, `base_orderedWord_eq_cylinder`: all finite chronological words.
- `cylinder_orderedStarWord_eq_base`, `base_orderedStarWord_eq_cylinder`: arbitrary conjugation choices.
- `coordinate_norm_sum`, `orderedWord_coefficient_norm_sum`: exact coefficient budgets.
- `cylinder_zeroEndpoints_iff_base`: equivalence of all finite-channel zero-endpoint conditions.

Scratch compilation and targeted leaf build passed. The leaf is imported in `RHTower.lean`; no umbrella build ran. Scratch capstone audits report only `propext`, `Classical.choice`, and `Quot.sound`. No added axioms, computational proofs, or open mathematical input occur in these reconstruction theorems. The requested novel RH architecture and RH proof remain unestablished.

The final repository-wide `scripts/formal_tools.py lint` run passed with existing large-file warnings. The transient unrelated umbrella failure from the earlier scan was no longer present.
