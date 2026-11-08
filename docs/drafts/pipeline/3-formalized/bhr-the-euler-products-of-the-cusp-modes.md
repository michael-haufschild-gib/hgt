# BHR — the Euler products of the cusp modes

- **ID:** bhr-cusp-euler-products
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** "Not formalized" item of `bhr-the-l-functions-of-the-cusp-modes.md`.
- **Statement:** Let `g ∈ S(λ)` with `T_p g = c_p g` for every prime `p`, Whittaker coefficients `ρ(n)` and
  `λ_p = c_p/√p`.
  1. `c_p ρ(n) = √p ([p ∣ n] ρ(n/p) + ρ(pn))` for `n ≠ 0`.
  2. `ρ(1) ρ(mn) = ρ(m) ρ(n)` for coprime `m, n ≥ 1`; `ρ(p^{k+2}) = λ_p ρ(p^{k+1}) − ρ(p^k)`.
  3. For `Re s > 3/2`: `Σ_{n≠0} ρ(n)|n|^{−s} = (ρ(1) + ρ(−1)) Π_p (1 − λ_p p^{−s} + p^{−2s})⁻¹`.

## Paper proof
1. In the Hecke recursion `c a_n(y) = [p∣n] a_{n/p}(py) + p a_{pn}(y/p)` all three modes carry
   `K_ν(2π|n|y)`: `a_{n/p}(py) = ρ(n/p)√p√y K`, `a_{pn}(y/p) = ρ(pn)(√y/√p) K`. At a `y` with `K ≠ 0`, cancel `√y K`.
2. *Hecke sequences* `σ(pn) = λ_p σ(n) − [p∣n] σ(n/p)` (`n ≥ 1`): both `n ↦ ρ(n)` and `n ↦ ρ(−n)` are such.
   A Hecke sequence with `σ(1) = 0` vanishes (strong induction, `n = pm` with `m < n`), so any two are
   proportional. For `σ(1) = 1`: `σ(p) = λ_p`, `σ(p^{k+2}) = λ_pσ(p^{k+1}) − σ(p^k)`; by two-step induction
   `σ(p^k m) = σ(p^k)σ(m)` for `p ∤ m`; by strong induction on `n = p^k n'` (`p ∤ n'`, `p ∤ m`),
   `σ(mn) = σ(m)σ(n)` for coprime `m, n`.
3. *Local factor.* With `S = Σ_k σ(p^k)x^k` (absolutely convergent), shifting twice and the recursion give
   `S = 1 + λx + λx(S − 1) − x²S`, i.e. `(1 − λx + x²)S = 1`.
4. *Euler product.* `f(n) = σ(n)n^{−s}` is multiplicative with `f(1) = 1`, `f(0) = 0`; Mathlib's
   `eulerProduct_tprod` gives `Π_p Σ_k f(p^k) = Σ_n f(n)`, and `f(p^k) = σ(p^k)(p^{−s})^k`.
5. *Assembly.* If `ρ(±1) = 0` both sequences vanish and both sides are `0`. Otherwise normalize a nonzero one
   to `τ`; `ρ(n) = ρ(1)τ(n)`, `ρ(−n) = ρ(−1)τ(n)`. `|ρ(n)| ≤ C√|n|` gives absolute convergence for `Re s > 3/2`;
   fold the `ℤ`-series to `Σ_{n≥1}(ρ(n) + ρ(−n))n^{−s}`.

## Lean certificate
`formal/GaloisForLFunctions/BlackHoleRingdown/TheEulerProductOfTheCuspModes.lean`, wired into `BlackHoleRingdown.lean`,
checked with `lake --old env lean`, no messages. Axioms of `cusp_euler_product`, `rho_mul`: `propext`,
`Classical.choice`, `Quot.sound`.

| Claim | Theorems (namespace `BlackHoleRingdown.CuspEuler`) |
|---|---|
| (1) | `exists_K_ne_zero`, `rho_hecke`, `heckeRec_rho` |
| (2) | `HeckeRec`, `HeckeRec.eq_zero`, `HeckeRec.proportional`, `HeckeRec.pow_mul`, `HeckeRec.mul`, `rho_mul` |
| (3) | `HeckeRec.local_factor`, `HeckeRec.euler`, `cusp_euler_product` |

## Scope
With C12 the cusp modes carry degree-two L-functions: entire, `s ↦ 1 − s` symmetric, Euler product with local
factors `1 − λ_p p^{−s} + p^{−2s}`. The Ramanujan bound `|λ_p| ≤ 2` (equivalently that the local roots lie on the
unit circle) is open; here only `|c_p| ≤ p + 1` is proved (`norm_heckeEigenvalue_le`).

## Log
- 2026-11-08 — created and formalized.
