# The observer-metric space is a MetricSpace in Lean (card gap closed)

Card `projective-ht-horizon-symmetric-space-boundary`: its "only missing analytic input" (the
triangle inequality of `observerDist`, i.e. the CAT(0)/nonpositive-curvature theorem for
`SL_N(C)/SU(N)`) is **closed**, together with symmetry, and packaged as a mathlib `MetricSpace`.

Six modules under `formal/GaloisForLFunctions/HTGeometry/`, all in the `HTGeometry` umbrella,
axioms `[propext, Classical.choice, Quot.sound]`:

| module | content |
|-|-|
| `MatrixCompound.lean` | `compound k A` = matrix of `exteriorPower.map`; **Cauchy–Binet is a corollary of functoriality**; minor formula ⇒ `C_k(Aᴴ) = C_k(A)ᴴ`; diagonal, unitary, invertible |
| `TopSumMajorization.lean` | `firstIdx`, `sortDesc`, `topSum`; `sum_le_topSum`; Karamata for the square by one `Finset.sum_range_by_parts`; `sqrt_sum_sq_le_of_topSum_le` |
| `CompoundKyFan.lean` | `matQuadForm`, `rdiag`; `prod_le_mul_of_compound` — multiplicative Ky Fan for a pencil |
| `ObserverTriangleInequality.lean` | `distId_eq_sqrt`, `obsMat`, `invSqrtMat`, **`observerDist_triangle`** |
| `ObserverDistanceSymmetry.lean` | `orthonormalBasisOfCard`, `distId_eq_sqrt_of_diagonal`, `distId_congr`, `distId_swap`, `relOp_swap_eq_invOp`, **`observerDist_comm`** |
| `ObserverMetricSpaceStructure.lean` | `ObserverMetric` + `instance : MetricSpace (ObserverMetric E)` |

## The two mathematical moves worth remembering

1. **Triangle inequality without calculus.** `d(P,Q) = ‖log λ(P,Q)‖₂` for the pencil spectrum.
   Comparison of quadratic forms `x*Qx ≤ a·x*Px` composes with multiplicative constants; run that
   on the `k`-th compound, where a product of `k` eigenvalues is a single eigenvalue, to get
   `∏_{i<k} λ↓(P,R) ≤ ∏_{i<k} λ↓(P,Q)·∏_{i<k} λ↓(Q,R)`; equality at `k = N` is the determinant.
   That is majorization, and Karamata for the square is one Abel summation.
   **Do not** try Bhatia's Riemannian route (needs the Fréchet derivative of `exp`, absent from
   mathlib) and note that Golden–Thompson/Araki log-majorization runs the *other* way.
2. **Symmetry without a polar decomposition.** `X*X` and `XX*` have the same weights: if `X*X u_i =
   g_i u_i` with `u` orthonormal then `g_i^{-1/2} • X u_i` is an orthonormal eigenframe of `XX*`
   with the same weights — orthonormality is just the polarisation identity. Combine with
   `relOp_swap_eq_invOp` and the corpus's `distId_invOp`.

## Reusable, and mathlib does not have them
Cauchy–Binet / compound matrices; majorization and Karamata; "sum over a `k`-subset ≤ sum of the
`k` largest"; `MetricSpace` on positive-definite Hermitian forms.

## Traps hit
- All pencil statements are phrased with **explicit unitary diagonalisations as hypotheses**
  (`A = Vᴴ * rdiag α * V`), never `Matrix.IsHermitian.eigenvalues`; that avoids eigenvalue-multiset
  uniqueness entirely and makes the operator→matrix bridge mechanical.
- `Mathlib.Analysis.RCLike.Basic` does **not** bring `ℂ`'s ring instances — import
  `Mathlib.Analysis.Complex.Basic` (+ `Mathlib.Data.Complex.BigOperators` for `Complex.re_sum`).
- `Matrix.one` needs `DecidableEq` on the index; `Set.powersetCard ι k` has `Fintype`/`DecidableEq`.
- `omit [inst] in` must come **before** the docstring, not between docstring and `theorem`.
- Never sort the `HTGeometry.lean` umbrella wholesale: insert single lines in alphabetical position
  (a full sort produced a 2500-line diff that had to be undone by hand).

Next on the card: geodesic asymptote classes and the Tits metric on them.
