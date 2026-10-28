# Hecke-covariant Krein–Toeplitz theory (HKT)

- **ID:** hecke-krein-toeplitz-theory
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2810/fable.md §8 (M2, M3, Q-II)
- **Statement:** Hermitian kernels on the Hecke lattice `ℚ_{>0}` with finitely many negative squares:
  structure (Krein–Langer), exact index formula, aliasing/local-to-global law, closedness under
  pointwise limits, `𝔽_q` calibration, arithmetic instance (Weil orbit kernel of ζ), selectivity.

## Goal
Turn Walls 1/3/14 into structure theorems about one kernel: finite off-line support = Krein–Langer
class; transfer = closedness of bounded index; local-to-global = aliasing law on sublattices.

## Lean home
`formal/GaloisForLFunctions/HeckeKreinToeplitz/`, umbrella `HeckeKreinToeplitz.lean`,
namespace `GaloisForLFunctions.HeckeKreinToeplitz`. README there is the foundational document.

## Work items (state)
1. Kernels on a group, Gram, negative index `κ(k) : ℕ∞`, restriction, covariance — TODO
2. Reflected pair kernels; exact index formula `κ(p + Σ ω_j h_{χ_j}) = J` under separation — TODO
3. Closedness of `{κ ≤ n}` under pointwise convergence (transfer) — TODO
4. Aliasing law on subgroups; two primes never alias arithmetic pairs — TODO
5. `𝔽_q` calibration: curve kernel on `ℤ`, index = outer eigenvalue pairs; golden datum κ = 1 — TODO
6. Arithmetic instance: Weil orbit kernel on `ℚ_{>0}`, KL class ⇔ finitely many right zeros — TODO
7. Self-upgrade inside KL class (bounded ⇒ PD), growth exponent = deepest pair — TODO
8. Selectivity battery, deformation, inertia, Stepanov no-go — TODO

## Log
- 2026-10-28 — created; README first draft.
