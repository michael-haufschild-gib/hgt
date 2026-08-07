# Exterior elimination forces a positive Feshbach self-energy on Suzuki's pruned seam

- **ID:** `suzuki-exterior-feshbach-pruning-law`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-exterior-feshbach-pruning-law.md`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/ExteriorFeshbachBlocks.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ExteriorFeshbachPruning.lean`

## Formal content

The card's whole content is formalized: the two exact block equations, the three norm bounds, and
the C*-positivity of the self-energy.

```text
exteriorBlock alpha Q T   = alpha • 1 + Q * T * Q                       (D_alpha, lifted)
exteriorInverse hQ hT     = shiftInverse (norm_exteriorPart_lt hQ hT)   (D_alpha^{-1})
selfEnergy P hQ hT        = P * T * Q * exteriorInverse hQ hT * (Q * T * P)   (Sigma_alpha)
```

| Card | Lean |
|---|---|
| `(3)` `(alpha I + T) c = f` | hypothesis `heq : α • c + T * c = f` |
| `(4)` `[alpha P + P T P - Sigma] P c = -P T Q D^{-1} f` | `interior_equation` |
| `(5)` `Q c = D^{-1}[f - Q T P c]` | `exterior_solve` |
| `(6a)` `‖D^{-1}‖ <= 1/(alpha - ‖T‖)` | `norm_exteriorInverse_le` |
| `(6b)` `‖Sigma‖ <= ‖T‖²/(alpha - ‖T‖)` | `norm_selfEnergy_le` |
| `(7)` `‖P T Q D^{-1} f‖ <= ‖T‖/(alpha - ‖T‖) ‖f‖` | `norm_source_le` |
| `(8)` `Sigma = Sigma^*` | `isSelfAdjoint_selfEnergy` |
| `(8)` `Sigma >= 0` | `nonneg_selfEnergy` |

Supporting declarations: `norm_inverse_oneSub_le`, `shiftInverse`, `shiftInverse_mul_left`,
`shiftInverse_mul_right`, `norm_shiftInverse_le`, `smul_one_central`, `norm_compress_le`,
`norm_exteriorPart_lt`, `exteriorBlock_mul_inverse`, `inverse_mul_exteriorBlock`,
`comm_of_comm_inverse`, `exteriorBlock_comm`, `exteriorInverse_comm`, `feshbach_exterior`,
`feshbach_interior`, `isSelfAdjoint_inverse`, `isSelfAdjoint_exteriorBlock`,
`isSelfAdjoint_exteriorInverse`, `nonneg_exteriorBlock`, `nonneg_exteriorInverse`,
`selfEnergy_eq_conjugate`.

## Three things the formalization sharpens

**The block equations need no analysis at all.**  `feshbach_exterior` and `feshbach_interior` are
proved in a bare `Ring`: only `P + Q = 1`, idempotence of the relevant projection, and centrality
of the spectral shift enter.  No invertibility, norm, or completeness hypothesis appears.  This is
why the card's correction is exact rather than perturbative — the deleted returning words are
restored identically, not to leading order.

**The compressed inverse is realized as an ambient element.**  The card's `D_alpha^{-1}` lives on
`Q X_p`.  Formalizing it as the restriction of an operator on a subspace would require carrying a
subspace-valued algebra; instead the lift `alpha • 1 + Q T Q` is inverted in the ambient algebra by
a Neumann series, and `exteriorInverse_comm` proves the lift commutes with `Q`.  Commuting with `Q`
is exactly the statement that the ambient inverse restricts to the true inverse on `Q X_p`, so the
lift is faithful and nothing is lost.

**Positivity is a conjugation, not a spectral computation.**  `selfEnergy_eq_conjugate` rewrites
`Sigma = star X * D^{-1} * X` with `X = Q T P`.  Then `nonneg_exteriorBlock` gets `0 <= D` from
`IsSelfAdjoint.neg_algebraMap_norm_le_self` together with `‖Q T Q‖ < alpha`, `nonneg_exteriorInverse`
gets `0 <= D^{-1}` from the identity `D^{-1} = star (D^{-1}) * D * D^{-1}`, and
`star_left_conjugate_nonneg` finishes.  No spectral mapping and no continuous functional calculus is
invoked.

## Hypotheses

`P`, `Q`, `T` are elements of a normed algebra (a C*-algebra for `(8)`).  The hypotheses are the
defining properties of the objects the card quantifies over: `P + Q = 1`, `P * P = P`, `Q * Q = Q`,
`‖P‖ ≤ 1`, `‖Q‖ ≤ 1`, `‖T‖ < alpha`, `Q * f = f` (the source lies in the exterior), and — for
`(8)` — self-adjointness of `P`, `Q`, `T`.  Every one of these is stated in the card, and none is a
theorem proved elsewhere in the corpus.  Coordinate projections on `l^1` and `l^2` satisfy the
projection and contraction conditions, which is the card's `## 2` observation.

No `sorry`, `axiom`, `opaque`, `unsafe`, RH premise, or numerical computation occurs.
`feshbach_exterior` and `feshbach_interior` audit to `[propext]` alone; every other cited
declaration audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

That the correction is *strictly* nonzero for Suzuki's visible-prime adjacency is a statement about
that particular adjacency matrix, not about the Feshbach mechanism; it follows from `(8)` together
with a single nonzero visible prime power and is not restated here.  What is formalized is the
mechanism: the compression is wrong, the exact repair is `Sigma_alpha`, and `Sigma_alpha` is a
positive operator bounded by `‖T‖²/(alpha - ‖T‖)`.
