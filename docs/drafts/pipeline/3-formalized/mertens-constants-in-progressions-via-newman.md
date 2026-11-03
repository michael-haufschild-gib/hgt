# Mertens constants in progressions via Newman's analytic theorem

- **ID:** MCAP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** AHD README §9 item 2 (bulk second order needs Mertens constants in progressions)
- **Statement:** for `a` a unit mod `q`, `Σ_{n ≤ x, n ≡ a} Λ(n)/n = log x/φ(q) + C(q, a) + o(1)`,
  `C(q, a) = φ(q)⁻¹(−γ − Σ_{(n,q)>1} Λ(n)/n + Re Σ_{χ≠1} χ(a⁻¹)(−L'(1,χ)/L(1,χ)))`.

## Goal
The constant term of prime sums in residue classes, the arithmetic input of the bulk second order
of fixed conductor packets (AHD).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized: `GaloisForLFunctions.ArtinMertens.tendsto_sum_residueClass_div_sub_log`

## Proof
1. **Newman's analytic theorem** (`newman_analytic_theorem`, `ArtinMertens/NewmansAnalyticTheorem`).
   `f` measurable, `|f| ≤ B` on `(0, ∞)`, `g` analytic at every point of `Re z ≥ 0`,
   `g(z) = ∫_0^∞ f e^{−zt}` for `Re z > 0` ⟹ `∫_0^T f → g(0)`. Zagier's proof on rectangles: with
   `g_T` the truncated transform (entire) and the kernel `(1 + z²/R²)e^{zT}`, Cauchy on
   `[−δ, R] × [−R, R]` for `g` and on `[−R, R] × [−R, R]` for `g_T` gives
   `2πi(g(0) − g_T(0)) = ∮_right (g − g_T)k e^{zT}/z + ∮_{left,δ} g k e^{zT}/z − ∮_{left,R} g_T k e^{zT}/z`.
   On horizontal edges `|1 + z²/R²| ≤ 3|x|/R` cancels the `1/|x|` of `|g − g_T| ≤ Be^{−xT}/x` and of
   `|g_T| ≤ Be^{−xT}/|x|`; vertical edges carry `|k| ≤ 5`; the two parts are `≤ 16B/R` each
   (`norm_rightPart_le`, `norm_leftPart_le`). The small left edges vanish as `T → ∞`
   (`tendsto_leftPart_zero`, dominated convergence; `k(±iR) = 0`).
2. **The twisted series** (`tendsto_sum_twist_vonMangoldt_div`). For `χ ≠ 1`, `f(u) = ψ(e^u, χ)e^{−u}`
   is bounded by `log 4 + 4` (Chebyshev), its Laplace transform is `L(χΛ, z+1)/(z+1)`
   (`LSeries_eq_mul_integral`, substitution `x = e^u`), and `−L'/L(z + 1, χ)/(z + 1)` is analytic on
   `Re z ≥ 0` (`L(s, χ)` entire, `L(s, χ) ≠ 0` on `Re s ≥ 1`). Newman: `∫_1^x ψ(t,χ)/t² dt →
   −L'(1,χ)/L(1,χ)`. Abel summation and `ψ(x, χ) = o(x)` (prime number theorem in progressions,
   `Σ_{r<q} χ(r) = 0`) give `Σ_{n≤x} χ(n)Λ(n)/n → −L'(1,χ)/L(1,χ)`.
3. **The residue class** (`tendsto_sum_residueClass_div_sub_log`). Character expansion of the class
   indicator; the principal character contributes `Σ_{n≤x} Λ(n)/n − log x → −γ` minus the summable
   defect `Σ_{(n,q)>1} Λ(n)/n` over the powers of the primes dividing `q` (`summable_principalDefect`).

## Log
- 2026-11-03 — proved and formalized (three modules in `ArtinMertens/`).
