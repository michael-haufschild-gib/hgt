# Finite-window seam sinc universality

- **ID:** finite-window-seam-sinc-universality
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** whole-corpus closure of `DirichletPolynomialSincEnergy` and `SeamMoments`
- **Statement:** Every mixed second moment of two finite Dirichlet carriers has an exact shifted-window convolution-kernel law and symmetric sinc law, with deviation from its independent Steinhaus seam moment bounded by the corresponding explicit convolution near-collision energy.

## Goal

Upgrade the corpus's infinite-time seam limit to exact and quantitative laws on every finite
observation window.

## Gates

- [x] 0 → 1  in-progress: exact finite-window residue identified from Lean theorem statements
- [x] 1 → 2  fully-proven: complete convolution-reduction proof below
- [ ] 2 → 3  formalized: exact Lean theorem and final gates pending
- [ ] 3 → 4  publication-ready: novelty and exposition audit pending

## Approach

For positive finite supports, `dpoly_mul` identifies the pointwise product of the two deterministic
carriers with the Dirichlet polynomial having coefficients `dpolyConv a b s t` on `prodSupport s t`.
`model_mul` gives the identical reduction for the Steinhaus product.  Every member of the product
support is at least one.  Apply `secondMoment_window_kernel` and
`secondMoment_window_independence_error_le` to the convolution carrier for an arbitrary positive
window; apply `secondMoment_symmetric_sinc` and `secondMoment_symmetric_sinc_error_le` on `[-T,T]`.
Finally `integral_normSq_dpoly` identifies the independent convolution diagonal with the mixed
Steinhaus second moment.  These are exact rewrites followed by the existing inequalities, so no
limit exchange or new analytic hypothesis remains.

## Audit

- **[CORPUS]:** finite-window and symmetric sinc laws exist only for a single coefficient vector
- **[CORPUS]:** `tendsto_mixedSecondMoment_average_steinhaus` supplies only the seam limit
- **Hostile verdict:** `SURVIVES PRELIMINARY ATTACK`; the exact finite-window mixed law and explicit seam error are absent
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED]`

## Log

- 2026-07-22 — theorem-statement closure found; exact paper proof closed before Lean work
