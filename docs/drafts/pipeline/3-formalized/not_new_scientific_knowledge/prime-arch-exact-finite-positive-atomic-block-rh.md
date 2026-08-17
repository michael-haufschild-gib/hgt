# Prime--archimedean exact finite positive-atomic block law for RH

- **ID:** `prime-arch-exact-finite-positive-atomic-block-rh`
- **Stage:** 2-fully-proven
- **Type:** PROVED REDUCTION (not new scientific knowledge)
- **Formal status:** the approximate local-closure law is formalized; the exact cubature upgrade
  below is not yet formalized

## Theorem

Let

```text
m_n = normalizedPrimeArchMoment n.
```

The following are equivalent.

1. RH.
2. For every `N : ℕ`, there exist `d ≤ N + 1`, masses `w_i ≥ 0`, and nodes `x_i ≥ 0`
   (`i < d`) such that

   ```text
   m_n = sum_{i<d} w_i x_i^n                 for every n < N.
   ```

Consequently, for every admissible rectangular prime--polar source, the critical negative-source
abscissa bound is equivalent to exact finite positive-atomic representability of every finite
prime--Gamma moment block.

## Proof

### RH gives exact finite atomic blocks

Assume RH and write

```text
lambda_j = xiThermalNode (xiThermalEnumeration j).
```

The formal Xi thermal laws give `lambda_j > 0` and, for every `n`,

```text
sum_j lambda_j^(n+1) = m_n.
```

In particular, with `M = m_0`,

```text
M > 0,                 sum_j lambda_j = M.
```

Every `lambda_j` lies in `[0,M]`: all terms are nonnegative and no term exceeds their sum.
Fix `N` and define the compact moment curve

```text
v : [0,M] -> R^N,
v(x)_n = x^n.
```

For `J : ℕ`, put the unspent mass at the zero node and form

```text
b_J = sum_{j<J} (lambda_j/M) v(lambda_j)
      + (1 - sum_{j<J} lambda_j/M) v(0).
```

The coefficients are nonnegative and sum to one, so `b_J` belongs to
`conv(v([0,M]))`.  Coordinatewise power-sum convergence gives

```text
b_J -> (m_n/M)_{n<N}.
```

The convex hull `conv(v([0,M]))` is compact.  Indeed, Caratheodory's theorem represents every
point of this convex hull using at most `N+1` points.  After padding with zero coefficients, the
convex hull is the image of

```text
Delta_N x [0,M]^(N+1)
```

under the continuous map

```text
((a_i),(x_i)) |-> sum_i a_i v(x_i),
```

where `Delta_N` is the compact standard simplex.  Hence the convex hull is closed.  The limit of
the `b_J` therefore remains in the convex hull.  Thus there are `d ≤ N+1`, coefficients
`a_i ≥ 0` summing to one, and nodes `x_i in [0,M]` with

```text
(m_n/M)_{n<N} = sum_{i<d} a_i v(x_i).
```

Taking `w_i = M a_i` gives the required exact moment identities.

### Exact finite atomic blocks give RH

Assume the exact finite-block property.  For every cutoff `N` and tolerance `epsilon > 0`, use
the exact witness for that `N` and let

```text
m'_n = sum_{i<d} w_i x_i^n.
```

Then `m'_n = m_n` for `n<N`, so the coordinatewise error is zero and hence is less than
`epsilon`.  Therefore the normalized prime--Gamma source satisfies
`PrimeArchFinitePositiveAtomicLocalMomentClosure`.  The formal theorem

```text
primeArchFinitePositiveAtomicLocalMomentClosure_iff_riemannHypothesis
```

implies RH.

This also proves the prime--polar abscissa formulation by the formal theorem

```text
rectangularPrimePolarSource_negativeAbscissa_le_one_iff_primeArchFinitePositiveAtomicLocalClosure.
```

## Impact on the proof burden

The approximation tolerance can be removed on paper.  It is enough to solve one exact finite
nonnegative algebraic moment problem at every cutoff, and at most `N+1` atoms are required for an
`N`-coordinate block.  No thermodynamic limit, compatibility between cutoffs, infinite-dimensional
observable, or global representing measure is part of the hypothesis.

The remaining formal task was a finite-dimensional compact-convex cubature lemma specialized to
the moment curve, followed by its application to the Xi thermal power sums.  **Both are now
formalized** — see the Lean section below — so the card is Lean-proven.


## Lean formalization — 2026-08-17

Two new modules, both axiom-clean and wired into their umbrellas.

**`formal/GaloisForLFunctions/HTGeometry/FiniteAtomicCubature.lean`** — the cubature lemma, stated
for a general compact set so it is reusable:

| Statement | Lean name |
|---|---|
| convex combinations of exactly `n` points of `K` form a compact, hence closed, set | `atomicSpan`, `atomicSpan_eq_image`, `isCompact_atomicSpan`, `isClosed_atomicSpan` |
| Carathéodory in coordinates: `convexHull ℝ K ⊆ atomicSpan (N+1) K` | `convexHull_subset_atomicSpan` |
| **the cubature lemma**: a limit of convex combinations of points of a compact `K ⊆ ℝ^N` is a convex combination of at most `N+1` of them | `exists_atomic_of_mem_closure_convexHull` |
| padding an affinely independent family out to `N+1` atoms | `sum_extend_embedding` |

The card's proof sketch argues that `conv(v([0,M]))` is closed *because* it is compact, via
Carathéodory plus continuity of `((a_i),(x_i)) ↦ Σ a_i v(x_i)`.  The Lean proof inverts this:
mathlib has no "convex hull of a compact set is compact" (only `Set.Finite.isCompact_convexHull`),
so `atomicSpan (N+1) K` — the image of the compact `Δ_N × K^{N+1}` — is shown closed *directly*,
and Carathéodory is used only for the inclusion `convexHull ℝ K ⊆ atomicSpan (N+1) K`.  A closed
superset of the hull contains its closure, which is exactly what the limit step needs.  The atom
bound comes from `AffineIndependent.card_le_finrank_succ` together with
`Module.finrank_fin_fun`.

**`formal/GaloisForLFunctions/RHTower/PrimeArchExactAtomicBlock.lean`** — the application:

| Card step | Lean name |
|---|---|
| the moment curve `v(x) = (1, x, …, x^{N-1})` and its compact arc over `[0,M]` | `momentCurve`, `momentArc`, `isCompact_momentArc`, `momentArc_nonempty` |
| exact finite positive-atomic blocks, `d ≤ N+1` | `FinitePositiveAtomicExactBlock`, `PrimeArchExactFiniteAtomicBlock` |
| exact blocks give the approximate local closure (zero error) | `finitePositiveAtomicLocalMomentClosure_of_exactBlock` |
| `λ_j > 0`, `Σ_j λ_j = M`, hence `λ_j ∈ [0,M]` and the partial sums are `≤ M` | inside `primeArchExactFiniteAtomicBlock_of_riemannHypothesis` (from `xiThermalNode_pos`, `hasSum_xiThermalEnumeration_pow_of_rh`) |
| the truncations `b_J` are convex combinations of arc points converging to `(m_n/M)_{n<N}` | same proof, via `Convex.sum_mem` and `mem_closure_of_tendsto` |
| **the exact block law** | `primeArchExactFiniteAtomicBlock_iff_riemannHypothesis` |
| exact and approximate laws agree at this source | `primeArchExactFiniteAtomicBlock_iff_localMomentClosure` |

Two remarks on the formalization.

* **The atom count is stated as exactly `N+1`, not `d ≤ N+1`.**  These are equivalent — surplus
  atoms carry zero mass — and the fixed-arity form composes directly with
  `FinitePositiveAtomicMomentSequence`, which is what the existing RH consumer expects.
* **Where the unspent mass goes matters.**  Parking `1 - Σ_{j<J} λ_j/M` at the node `0` is what
  makes each `b_J` a genuine convex combination rather than a sub-probability combination; the
  node `0` contributes to the zeroth coordinate only (`0^0 = 1`, `0^{n+1} = 0`), so it fixes the
  normalization without disturbing any higher moment.  The Lean proof splits on `n = 0` for exactly
  this reason.

Verification: `lake build GaloisForLFunctions.RHTower.PrimeArchExactAtomicBlock` — PASS;
`#print axioms` on all named results in both modules reports only
`[propext, Classical.choice, Quot.sound]`.

## Gates

- [x] 0 -> 1 candidate isolated
- [x] 1 -> 2 complete paper proof
- [x] 2 -> 3 Lean formalization and axiom audit
- [ ] 3 -> 4 publication-ready integration
