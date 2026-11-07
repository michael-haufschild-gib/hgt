# BHR — the cusp spectrum of the modular horizon is discrete

- **ID:** bhr-cusp-spectrum-discrete
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** A26 (Weyl law) of review-0711; continues `bhr-the-cusp-forms-of-the-modular-horizon-exist.md`.
- **Statement:** Finitely many level-one cuspidal eigenvalues (with multiplicity) lie below every bound; the
  counting function `N(Λ)` is finite and tends to infinity; the eigenvalues are unbounded.

## Paper proof
1. Let `φ ≥ 0` be a unit kernel supported in `u ≤ R`. If `u(i, w) ≤ R ≤ 1/32` then `(y-1)² ≤ 4Ry`, so
   `½ < y < 2` and `(y-1)² ≤ 8R`, where `y = Im w`.
2. For `y > ½`, `|log y| ≤ 2|y-1|` (from `1 - 1/y ≤ log y ≤ y - 1`). With `|s|² ≤ Λ` and
   `512 R (Λ+1) ≤ 1`, `|s log y| ≤ ¼`, hence `|y^s - 1| = |e^{s log y} - 1| ≤ 2|s log y| ≤ ½`.
3. So `|h_φ(s) - 1| = |∫φ(u)(y^s - 1)| ≤ ½`.
4. A cusp eigenvalue `λ ≥ ¼` has `s = ½ + i√(λ-¼)` with `|s|² = λ`. Its basis vectors are eigenvectors of
   the compact symmetric operator `L_φ` with eigenvalue `h_φ(s)`, `|h_φ(s)| ≥ ½`. Such eigenvalues are
   finitely many (corpus), each eigenspace is finite-dimensional, and the basis vectors with `λ ≤ Λ` are
   orthonormal in their sum. Hence finitely many.
5. With infinitude of the basis, `N(Λ) → ∞` and the eigenvalues are unbounded.

## Lean certificate
Module `formal/GaloisForLFunctions/BlackHoleRingdown/TheCuspSpectrumIsDiscrete.lean`, wired into
`BlackHoleRingdown.lean`, checked with `lake --old env lean`, no messages; axioms of `tendsto_cuspCount`,
`not_bddAbove_cuspEigenvalues`: `propext`, `Classical.choice`, `Quot.sound`.

| Claim | Theorems |
|---|---|
| Narrow kernels | `CuspSpectrum.height_bounds`, `CuspSpectrum.norm_cpow_sub_one_le`, `CuspSpectrum.norm_selbergTransform_sub_one_le` |
| Discreteness | `finite_cuspEigenIndex_le`, `finite_cuspEigenvalues_le` |
| Counting function | `cuspCount`, `tendsto_cuspCount`, `not_bddAbove_cuspEigenvalues` |

## Not formalized
- The Weyl asymptotic `N(Λ) ~ Λ/12`, and any rate of growth of `N`.

## Log
- 2026-11-07 — created and formalized.
