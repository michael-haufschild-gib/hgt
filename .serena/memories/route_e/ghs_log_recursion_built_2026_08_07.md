# The prime-only form of Halász's recursion (2026-08-07)

## The corpus already owned more than expected — check these before writing anything log-weighted

- `RHTower.Sieve.sum_mul_log_eq_vonMangoldt` (Sieve/DivisorSwap.lean) — **Halász's recursion**
  `∑_{m≤N} f(m) log m = ∑_{d≤N} Λ(d) f(d) S_f(⌊N/d⌋)` for completely multiplicative `f : ℕ → ℂ`.
  Do not restate it over ℝ; ℂ is more general.
- `RHTower.Sieve.sum_divisors_swap` — the divisor swap it rests on.
- `RHTower.pmul_log_mul` (RHTower/DirichletLogDerivation.lean) — the **real** Leibniz rule for pointwise
  `log`; `HTGeometry.logWeight_leibniz` is the complex one. Selberg's identity is already derived there
  as `vonMangoldt_pmul_log_add_mul_self`.
- `RHTower.Sieve.moebius_pmul_log`, `RHTower.Sieve.sum_moebius_mul_log_eq`,
  `RHTower.Sieve.one_pmul_log` (Sieve/MoebiusLogRecursion.lean) — the Möbius instance, already done.
- `RHTower.Mertens.tail_bounded` (RHTower/MertensFirst.lean, a *different* module from
  Sieve/MertensFirst.lean) — `∑_{d≤N, ¬prime} Λ(d)/d ≤ 8 + mertensTail`.
- `RHTower.Sieve.le_log_factorial` (Sieve/MertensFirst.lean) — `N log N − N ≤ log N!`.

I wrote duplicates of the first four before finding them and had to delete them. The search that finds
them is `formal_tools.py research "divisor swap log recursion"` plus `ls GaloisForLFunctions/RHTower/Sieve`
— not a `research` query about the *application* (Halász, Selberg, prime-power tail).

## What was actually missing, and is now built

`RHTower/Sieve/MultiplicativeLogRecursion.lean` (ℂ-valued, green, axiom-clean):
entry point `norm_sum_Icc_mul_log_sub_sum_primes_le'` —
`‖S_f(N) log N − ∑_{p≤N} f(p) log p S_f(⌊N/p⌋)‖ ≤ (9 + RHTower.Mertens.mertensTail) · N`,
hypotheses only `f (a*b) = f a * f b` and `‖f n‖ ≤ 1`. Steps: log-shift via `le_log_factorial`
(cost ≤ N), prime-power excess via `tail_bounded` (cost ≤ (8+mertensTail)N).

`HTGeometry/GeneralisedVonMangoldt.lean` + `RHTower/Sieve/VonMangoldtWeightAdditive.lean`:
the weight `Λ_f = f⁻¹ * (f·log)` with `f·log = f * Λ_f`, uniqueness, `Λ_ζ = Λ`, `Λ_f = f·Λ` for
completely multiplicative `f`, `|Λ_f| ≤ Λ`, and the universal law **`Λ_{f*g} = Λ_f + Λ_g`, `Λ_1 = 0`**
(from the existing Leibniz rule). So `Λ`, `−Λ` and `f·Λ` are one law's values at `ζ`, `μ`, `f`.

Claims no decay, and cannot: the identity is tight for `f = 1`. Its value is that the remaining gate has
no Dirichlet polynomial of length `x` and no short-height mean-value theorem — so the contour-route
no-gos do not apply — and the prime sum is *signed*. Absolute-value forms were deleted: they are
saturated by `f = 1`. Premises about `S_f` itself (ε-small at smaller scales) were deleted too: such a
premise cannot be discharged, so the theorem would be conditional.
