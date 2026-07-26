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
- [x] 2 → 3  formalized: exact Lean theorems compiled, axiom-clean
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

## Formalization

`formal/GaloisForLFunctions/RHTower/FiniteWindowSeamSincUniversalityLaw.lean` — builds clean, no
warnings, `#print axioms` gives exactly `propext, Classical.choice, Quot.sound` on every theorem.

| Card claim | Lean name |
|---|---|
| independent seam moment = convolution diagonal | `RHTower.mixedSteinhausSecondMoment_eq_convolutionDiagonal` |
| **exact shifted-window convolution-kernel law** | `RHTower.mixedSecondMoment_window_kernel` |
| **finite-window seam error bound** | `RHTower.mixedSecondMoment_window_independence_error_le` |
| **exact symmetric sinc law** | `RHTower.mixedSecondMoment_symmetric_sinc` |
| **symmetric seam error bound** | `RHTower.mixedSecondMoment_symmetric_sinc_error_le` |

These are exactly the reductions of the Approach section: `dpoly_mul` and `model_mul` turn both the
deterministic product and its Steinhaus model into the single convolution carrier
`dpolyConv a b s t` on `prodSupport s t`, after which `secondMoment_window_kernel`,
`secondMoment_window_independence_error_le`, `secondMoment_symmetric_sinc`,
`secondMoment_symmetric_sinc_error_le` and `integral_normSq_dpoly` apply verbatim.  No limit
exchange and no new analytic hypothesis enters.

### The infinite-time seam limit is now discharged by the finite-window law

The corpus previously proved the seam limit `tendsto_mixedSecondMoment_average_steinhaus`
independently.  It is now a corollary of the exact finite-window law, because the explicit error
envelopes vanish:

| Content | Lean name |
|---|---|
| the windowed near-collision energy vanishes | `RHTower.tendsto_dpolyWindowOffDiagonalEnergy` |
| the sinc near-collision energy vanishes | `RHTower.tendsto_dpolySincOffDiagonalEnergy` |
| **shifted-window seam limit, every window location** | `RHTower.tendsto_mixedSecondMoment_window_steinhaus` |
| **symmetric seam limit** | `RHTower.tendsto_mixedSecondMoment_symmetric_steinhaus` |
| the corpus seam limit as the window limit at the origin | `RHTower.tendsto_mixedSecondMoment_average_steinhaus_of_window` |

Both energies are finite sums of terms `|a_m a_n| · min(1, c/(U|log n − log m|))` with `log n ≠ log m`
off the diagonal, so each term is squeezed to zero and the sum with it.  The window seam limit is
therefore strictly stronger than the corpus statement: it holds for **every fixed window location**
`A`, not only `A = 0`, and the symmetric version is new.

### Remaining

Nothing in the formalisation.  Gate `3 → 4` (novelty and exposition audit) is open editorial work.
