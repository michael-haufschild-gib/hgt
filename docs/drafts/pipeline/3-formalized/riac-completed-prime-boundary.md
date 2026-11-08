# The domain of the completed prime boundary

- **ID:** RIAC-completed-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md), completed topology
- **Statement:** The actual weighted prime augmentation has a closed extension exactly when `2 Re(s)+δ>1`.

## Exact theorem

On finite prime coefficients, `d_s a=Σ_p p^(−s)a_p`. Normalize the conductor
norm `Σ_p p^δ |a_p|²` into ordinary prime `ℓ²`. This embedding is injective
and dense. For every complex `s` and real `δ`, the following are equivalent:

1. A bounded linear functional extends the original finite-chain boundary.
2. A linear functional on some subspace containing all finite chains extends
   that boundary and has closed graph in `ℓ²×ℂ`.
3. `2 Re(s)+δ>1`.

The bounded extension is unique and has squared norm
`Σ_p p^(−2 Re(s)−δ)`. In the complementary closed half-plane, the finite graph
has `(0,1)` in its closure: finite chains with boundary one have arbitrarily
small norm. Thus the original densely defined boundary is not closable there.

## Proof

The finite gauge `G_t a=(p^t a_p)_p` satisfies `d_s G_t=d_(s−t)` and
`G_t G_(−t)=id`. The weighted embedding is `J G_(δ/2)`; its graph equals the
ordinary finite graph at `s+δ/2`. Its squared norm is exactly the stated
weighted coefficient sum. The canonical Hilbert basis gives density and
linear independence, retained by the invertible finite gauge.

For the unweighted boundary put `b_p=p^(−s)`. A bounded extension exists
precisely when `(b_p)` is square summable: sufficiency is the Riesz functional
with vector `(conj b_p)`; necessity is Parseval applied to any proposed
functional. The coefficient identity `|p^(−s)|²=p^(−2 Re(s))` and divergence
of reciprocal primes give the exact threshold. Riesz isometry gives the norm;
density gives uniqueness.

When the coefficients are not square summable, choose finite `S` with
`A_S=Σ_(p∈S)|b_p|²>1/ε`. The finite packet `a_p=conj(b_p)/A_S` on `S`
has `d_s a=1` and norm squared `1/A_S<ε`. Hence `(0,1)` lies in graph closure.
Every closed graph containing the finite graph would contain `(0,1)`,
contradicting linearity at zero. The exact gauge transfers both directions
to every conductor weight.

## Lean realization

[CompletedPrimeBoundary.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/CompletedPrimeBoundary.lean):

- `primeWeightedChainEmbedding_norm_sq`, `_injective`, `_dense`.
- `primeWeightedBoundary_bounded_extension_iff`.
- `primeWeightedBoundary_closed_extension_iff`.
- `primeWeightedBoundaryExtension_finite`, `_norm_sq`, `_unique`.
- `primeBoundary_unit_response_small_norm`.
- `primeWeightedBoundaryGraph_eq_shift`, `primeWeightedBoundary_graph_closure_unit`.

Direct `lake --old env lean` production check passes. Twenty-one audited
declarations use only `[propext, Classical.choice, Quot.sound]`.

## Existing work and positive survivor

Riesz representation, Parseval, prime-power summability and the scalar
nonclosability mechanism are established tools. Corpus already contains the
scalar vertical-fibre classification and the dense graph of finite summation.
Its vector-valued prime co-shift row is a different operator. ESG supplies the
actual finite Dirichlet gauge. No priority claim is made for these mechanisms.

The arithmetic result retains the original weighted finite boundary and
classifies every closed partial extension, with faithful dense embedding,
explicit unique bounded extension and exact prime Dirichlet norm as positive
survivors. At `δ=0`, no such closed extension exists on or left of the critical
line. This excludes that augmented Hilbert model, not alternative norms,
modified boundaries or relative complexes. Higher-degree contraction and
zero detection remain open.
