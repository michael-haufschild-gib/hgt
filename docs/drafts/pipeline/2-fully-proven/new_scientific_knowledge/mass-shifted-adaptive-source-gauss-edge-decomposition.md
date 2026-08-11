# Adaptive Source Gauss-Edge Decomposition

- **ID:** mass-shifted-adaptive-source-gauss-edge-decomposition
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3; exact adaptive
  Jacobi-energy and Christoffel-scale laws
- **Statement:** The admission-first adaptive mixed source splits exactly into one Gaussian-visible
  positive aggregate and one universal next-edge Christoffel remainder; after current-scale
  completion the hidden edge is exactly `(n+1)/16`.

## Goal

Replace fixed linear reporting by a source-dependent observation law. Nodes, weights, amplitude,
and completion scale are all selected from the current admitted moment form before aggregation.
The theorem localizes finite-observer loss exactly and leaves no orientation choice.

## Theorem

Let `L` be a real moment functional positive on nonzero squares through degree `n+1`, with `n>0`.
Let `P_j` be its monic orthogonal polynomials, `h_j=L(P_j^2)`,
`beta_j=h_j/h_(j-1)`, and let

`S_n=(X P_n) X (X P_n' + P_n)`

be the literal adaptive source polynomial. Let `xi` range over roots of `P_(n+1)` and let
`lambda_n(xi)` be current Christoffel weights. Write `E_n` for adaptive Jacobi energy. Then

`L(S_n) - sum_xi lambda_n(xi) S_n(xi) = (n+1) h_(n+1)`,

and hence

`sum_xi lambda_n(xi) S_n(xi)
  = h_n (E_n - (n+1) beta_(n+1)) > 0`.

For shifted-Xi normalized admission, whose current Christoffel scale is
`kappa_n=16 beta_(n+1)`, define source-selected visible bulk

`G_n = [sum_xi lambda_n(xi) S_n(xi)] / [16 h_n beta_(n+1)]`.

Then the literal scale-completed source satisfies

`C_n = E_n/[16 beta_(n+1)] = (n+1)/16 + G_n`,

with `G_n>0` in every finite positive current chamber.

## Proof [PROVED HERE]

Gaussian quadrature with the `n+1` roots of `P_(n+1)` is exact through degree `2n+1`.
For any polynomial `f` of degree at most `2n+2`, subtract

`f_(2n+2) P_(n+1)^2`.

Both polynomials have the same top coefficient, so the difference has degree at most `2n+1`.
Quadrature is exact on that difference. At every Gaussian node `P_(n+1)^2` vanishes, while
its moment is `h_(n+1)`. Therefore the first Gaussian defect is exactly

`f_(2n+2) h_(n+1)`.

Now `P_n` is monic of degree `n`, while

`X^2 P_n + X^3 P_n'`

has degree `n+2` and top coefficient `n+1`. Their product is `S_n`, so the top coefficient of
`S_n` is `n+1`. This proves the first identity. The already-proved arithmetic source law gives
`L(S_n)=h_n E_n`; the norm ratio gives `h_(n+1)=h_n beta_(n+1)`. Subtraction proves the second
identity.

Finally, the completed-square formula for `E_n` contains the boundary contribution

`(n+1)(beta_n+beta_(n+1))`

plus nonnegative square and interior terms. Since `beta_n>0`,
`E_n>(n+1)beta_(n+1)`, so the Gaussian-visible aggregate is strictly positive. Dividing by the
positive current scale `16 beta_(n+1)` proves the completed decomposition and `G_n>0`.

## Conjecture / proof-or-fail loop

1. **Conjecture:** Gaussian observation loses an uncontrolled degree-`2n+2` shape functional.
   **Failed.** First-defect division proves loss is one-dimensional and exactly
   `(n+1)h_(n+1)`.
2. **Conjecture:** Christoffel completion merely rescales the old source and adds no structure.
   **Failed.** It converts the entire invisible Gaussian remainder into universal `(n+1)/16`.
3. **Conjecture:** Remaining visible node aggregate may have indefinite total sign because
   `S_n(xi)` is not pointwise positive.
   **Failed at aggregate level, survives pointwise.** Exact Jacobi decomposition proves its
   positive weighted sum; individual node signs remain unconstrained.
4. **Survivor:** Shape holonomy cannot hide throughout the finite face. It has exactly two
   channels: universal next-edge defect and strictly positive adaptive Gaussian bulk. Any
   frozen/current obstruction must now enter through transport of the source-selected bulk, not
   through arbitrary finite observer loss.

## Novelty and theatre audit

- General first Gaussian error formula is classical.
- New corpus knowledge is exact identification of adaptive `P^sharp` arithmetic source's top
  defect with its next Jacobi edge, and universalization of that defect by current Christoffel
  completion.
- Wide arXiv search on varying orthogonal polynomials, Christoffel transforms, Hankel/Toda flows,
  and current Gaussian quadrature found transformation/compatibility theories but no occurrence
  of this adaptive source or completed decomposition.
- This does not prove RH. It strictly reduces open core: observer loss is no longer an unspecified
  kernel-pair or topology issue; only transport of positive source-dependent bulk remains.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement and hostile tests isolated.
- [x] 1 -> 2 fully-proven: complete dependency-closed paper proof above.
- [ ] 2 -> 3 formalized: finite-block Gauss theorem and shifted-Xi completed capstone.
- [ ] 3 -> 4 publication-ready.

## Log

- 2026-08-11 — Paper theorem proved after Christoffel-scale completion; formalization started.
