# Weil-cone uniqueness in the absolutely convergent finite-type class; Möbius de-tilting of the |ζ|² functional

- **ID:** weil-cone-absolute-finite-type-uniqueness
- **Stage:** 3-formalized (Lean, unconditional, standard axioms)
- **Type:** THEOREM (Lean)
- **Parents:**
  - MUST-806 (`a = δ₁`, `|ζ|²`-weighted boundary inequality);
  - MUST-807 (sign rigidity of `F` against `ζ`);
  - `WeilZetaSquareMoments` (`(hk)^{−½}W(L)` main terms).
- **Closes:** the last natural-class gap of the `|ζ|²` method. The regular part `v` may now coexist with an infinite Möbius part.

## Statements
1. **De-tilting.** For a finite set `P` of primes, put `|M_P(t)|² = Π_{p∈P}(1 + 1/p − 2p^{−½}cos(t log p))` and `ρ(u,w) = (lcm(u,w)/gcd(u,w))^{−½}`. Then
   `∫ω_L|ζ(½+it)|²|M_P(t)|²cos((log u − log w)t)dt = T_P(u,w)·W(L) + O_P(uwL)`,
   with `T_P(u,w) = Π_{p∈P}(1 − 1/p)·[v_p(u) = v_p(w) ∀p∈P]·ρ(u,w)`.
   - Reading: the main-term functional of `|ζ|²` is the product of Poisson kernels `⊗_p P_{p^{−½}}` on the Bohr torus. Multiplying by `|M_P|²` replaces the Poisson kernel at each `p ∈ P` by `(1 − 1/p)·Haar`.
2. **Regular-part rigidity.** Suppose `Re V(½+it)|ζ|² + Re(F conj ζ) ≤ 0` for `t ≥ 8`, with `v, f` absolutely convergent past `½` and `v(1) = 0`. Then `v = 0`.
3. **Uniqueness.** If `Λ⋆a + μ⋆f + v` (all absolutely convergent past ½, `f(1) = v(0) = v(1) = 0`) is full-cone Weil-positive, then `a = δ₁` and `f = v = 0`.
4. **Equivalence.** Within this class, a Weil-positive system exists iff RH.

## Paper proof
1. **De-tilting, by induction on `P`.**
   - Base: `exists_abs_momentRe_sub_le` applied to the reduced pair `u/g`, `w/g`, using `(u/g)(w/g) = lcm/gcd`.
   - Step `P → P ∪ {q}`: `|1 − q^{−½−it}|²cos(ξt) = (1+1/q)cos ξt − q^{−½}(cos(ξ+log q)t + cos(ξ−log q)t)`. On the main-term side, `ρ(uq,w) = ρ(u,w)·q^{∓½}` according to `v_q(w) ≤ v_q(u)` or not (gcd/lcm factorizations). Hence `(1+1/q)ρ − q^{−½}(ρ(uq,w) + ρ(u,wq)) = (1 − 1/q)[v_q u = v_q w]ρ`. Errors grow by a factor `2 + 2q` per step.
2. **Averaging.** Fix `a ≥ 2` and assume `v(n) = 0` for `n < a`. Put `c = v(a)` and `P = {p ≤ K}`, and average the inequality against `ω_L|M_P|²|1 + c a^{−it}|²`.
   - The `V`-term equals `Σ_n v(n)n^{−½}·mval_n(L)`, by Fubini with an `ℓ¹` majorant.
   - The `F`-term is `O(L√log L)`: `|ζ| ≤ (λ + |ζ|²/λ)/2` with `λ = √log L`.
   - Dominated convergence on `mval_n/W(L) → gval_n`, with `W(L) ≥ L log L`, gives `Σ_n v(n)n^{−½}gval_n ≤ 0`.
3. **Evaluation.** `gval_n = (1+c²)T(n,1) + c(T(na,1) + T(n,a))`.
   - `gval_a = c·Π(1 − 1/p)`.
   - `gval_n = 0` for `a < n ≤ K`, since integers `≤ K` agreeing at all primes `≤ K` are equal.
   - `|gval_n| ≤ Π(1 − 1/p)(1 + c² + |c|(1+√a))n^{−½}` for all `n`.
   - Hence `v(a)²a^{−½} ≤ C·Σ_{n>K}|v(n)|/n → 0`.
4. **Uniqueness.** MUST-806 gives `a = δ₁`, step 3 gives `v = 0`, and MUST-807 then gives `f = 0`.

## Lean map
| Claim | Declaration |
|-|-|
| `ρ`, symmetry, bounds, reduction to coprime | `kpCorr`, `kpCorr_symm`, `kpCorr_le`, `kpCorr_reduce`, `kpCorr_self`, `kpCorr_one_right` |
| gcd/lcm under `·q`; `ρ(uq,w)`, `ρ(u,wq)` | `gcd_lcm_mul_prime`, `kpCorr_mul_prime_left/right` |
| `T_P`, recursion | `kpMass`, `closedT`, `closedT_insert` |
| weight `|M_P|²`, bounds, recursion | `mollWeight`, `mollWeight_nonneg/le`, `mollWeight_insert_mul_cos` |
| **De-tilting** | `momentP`, `momentP_insert`, `exists_abs_momentP_sub_le` |
| evaluation at primes ≤ K | `primesUpTo`, `gval`, `gval_self`, `gval_eq_zero`, `abs_gval_le`, `eq_of_factorization_primesUpTo` |
| averaging | `rotWeight`, `mval`, `integral_weighted_cos_eq`, `abs_mval_le`, `integral_win_norm_zeta_le`, `tsum_gval_nonpos` |
| **Regular-part rigidity** | `eq_zero_of_re_regular_le` |
| **Uniqueness; RH equivalence** | `regularPart_of_lSeriesSummable`, `eq_delta_and_eq_zero_of_weilPositiveFull_abs`, `exists_weilPositive_abs_iff` |

- Modules (wired in `RHTower.lean` after `WeilZetaSquareMobiusRigidity`):
  - `RHTower/ZetaSquareMobiusDetilting`;
  - `RHTower/WeilZetaSquareRegularPartRigidity`.
- Audit: `lake --old build` green, zero messages, axioms `[propext, Classical.choice, Quot.sound]`.

## Scope
- U-side (RH-blind). The `|ζ|²`-weighted boundary method is now complete for every absolutely convergent finite-type system.
- Left in U:
  - non-absolutely-convergent regular parts (e.g. `v` with `V` bounded on the line only);
  - the boundary class `δ = 0`, being worked on in a parallel session (C539);
  - non-multiplicative full-scale deviations;
  - atomic producers and twins (the C329 / L405 crystalline core).
- Existence (PBAP) is untouched.

## Log
- 2026-10-07 (loop row 540): proved and formalized.
- 2026-10-07 (rediscovery audit): the `v`-only case of statement 2 is MUST-502/556 (`vonMangoldt_add_summable_not_weilPositive`, `WeilRegular.eq_zero_of_weilPositive_add`). Statement 2's new content is `v` together with an infinite `F` (the `Re(Fζ̄)` term). Statement 1 (de-tilting) is new.
