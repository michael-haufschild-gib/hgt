# Weil-cone uniqueness with an infinite Möbius part: sign rigidity of critical Dirichlet series against ζ

- **ID:** weil-cone-infinite-mobius-part-rigidity
- **Stage:** 3-formalized (Lean, unconditional, standard axioms)
- **Type:** THEOREM (Lean)
- **Parents:**
  - L82 `CriticalPolynomialZetaSignRigidity` (Dirichlet polynomials);
  - MUST-806 `WeilZetaSquareDilationRigidity` (`a = δ₁` for `Λ⋆a + μ⋆f + v`).
- **Answers:** the open core (Step 5) of `1-in-progress/weil-cone-boundary-mobius-part-twisted-moments` (C539, row 538).

## Statements
1. **Sign rigidity.** Let `f : ℕ → ℝ` satisfy the log moment `Σ |f(n)| n^{−½}(1 + log n) < ∞` and `f(1) = 0`, and let `F(s) = Σ f(n)n^{−s}`. If `Re(F(½+iy)·conj ζ(½+iy)) ≤ 0` for all `y ≥ 8`, then `f(n) = 0` for every `n ≥ 1`.
2. **Uniform twisted first moment.** For positive integers `p, q` and `T ≥ 8`: `‖∫_8^T ζ(½+iy)(p/q)^{iy}dy‖ ≤ C·T·√(1 + log pq)`, with `C` absolute.
3. **Uniqueness.** If `Λ⋆a + μ⋆f` is full-cone Weil-positive, with `Σ(|a(n)| + |f(n)|)n^{−½+δ} < ∞` for some `δ > 0` and `f(1) = 0`, then `a = δ₁` and `f = 0`.
4. **Equivalence.** Within this class, a Weil-positive system exists iff RH.

## Paper proof
1. **Weight.** Strong induction on `a ≥ 2`; `f(1) = 0` is the base. Put `D = K!` with `K ≥ a`, `c = f(a)` and `W = |M_D(y)(1 + c a^{−iy})|² ≥ 0`, where `M_D(y) = Σ_{d∣D} μ(d)d^{−½−iy}`. By hypothesis `Re(F ζ̄)·W ≤ 0`. The pointwise identity `conj(F ζ̄)·W = Σ_n Σ_{d∣D} β(n,d)·[(1+c²)ζM_D e^{iy log(nd)} + c ζM_D e^{iy log(nda)} + c ζM_D e^{iy log(nd/a)}]` holds, with `β(n,d) = f(n)n^{−½}μ(d)d^{−½}`.
2. **Möbius collapse, all integers.** The Cesàro limit of `ζM_D` at the frequency `log u − log w` is `(u/w)^{−½}` if `w ∣ u` and `gcd(D, u/w) = 1`, and `0` otherwise. Proof: `Σ_{d∣D, wd∣u} μ(d) = [gcd(D, u/w) = 1]`.
3. **Evaluation.** Let `L_K` be the limit and `n` the term index.
   - `n = a`: exactly `c f(a)a^{−½}`, coming from `d = 1` in the third term.
   - `1 ≤ n < a`: `0`, by induction.
   - `a < n ≤ K`: `0`. Here `n ∣ K!`, so the first term dies. In the third term, `g = nd/a` coprime to `D` forces `g ∣ n`, hence `g ≤ K`, a contradiction.
   - `n > K`: at most `(1 + c² + |c|√a)|f(n)|/n`. At most one `d` survives in the third term, since `g₁d₂ = g₂d₁` together with coprimality gives `g₁ = g₂`. Also `n^{−½}d^{−½}(nd/a)^{−½} = √a/(nd)`.
   - Hence `|L_K − f(a)²a^{−½}| ≤ C_a·Σ_{n>K}|f(n)|/n`.
4. **Exchange of limit and sum.** For `T ≥ (pq)⁴`, move the segment to `σ = 3/2`. The right-edge terms are `T` for the resonant `m` and `≤ 4p²m^{−3/2}` otherwise, because `|log p − log r| ≥ 1/(2p)` for `r ≠ p`. The horizontal edges are `O(pq·T^{½})` by convexity. For `8 ≤ T < (pq)⁴`, use `∫_8^T |ζ| ≤ C T√(1+log T)`, from the mean square (dyadic induction on window mean squares) and `2λ|ζ| ≤ λ² + |ζ|²`. So every Cesàro mean of the `n`-th term is at most `C'|f(n)|n^{−½}√(1 + log(nQ))`, which is summable under the log moment. Dominated convergence applies.
5. **Conclusion.** `Re L_K ≤ 0` for every `K ≥ a`, so `f(a)²a^{−½} ≤ C_a·tail(K) → 0`, and `f(a) = 0`.
6. **Uniqueness.** MUST-806 gives `a = δ₁`. Then the `|ζ|²`-weighted boundary inequality reads `Re(F ζ̄) ≤ 0` on the line, and statement 1 gives `f = 0`.

## Why the case `F(1) < 0` is free
`M_{K!}` removes the diagonal: `ζM_{K!}` is the series of `K`-rough integers, so `F(1)` never enters the limit. The two-point weights `|1 + c m^{iy}|²` alone give only `F(1) ≤ 0` and Gram-type inequalities. The parallel route (row 538) therefore asked for a CLT of `arg ζ_{B,P}`, which is unnecessary.

## Lean map
| Claim | Declaration |
|-|-|
| Mean square `∫_8^T|ζ|² ≤ CT(1+log T)` | `ZetaUniformMoment.exists_integral_zsq_le` |
| First absolute moment | `exists_integral_norm_zeta_le` |
| Log separation `1/(2p) ≤ |log p − log r|` | `inv_two_mul_le_abs_log_sub` |
| Right edge, horizontal edges, rectangle | `norm_rightEdge_le`, `exists_norm_horizontal_le`, `integral_line_eq` |
| Uniform twisted first moment | `exists_norm_integral_zeta_twist_le` |
| General Möbius collapse | `zetaMobiusLimit_log_sub_eq` |
| Line series = Σ singleton polynomials; continuity | `LSeries_line_eq_tsum`, `continuous_LSeries_line` |
| Log moment; majorant summability | `LogMomentSummable`, `summable_majorant`, `logMomentSummable_of_lSeriesSummable` |
| Pointwise identity; integral hasSum; Cesàro limit | `integrand_eq_tsum`, `hasSum_integral_weightTerm`, `tendsto_mean_integrand` |
| Uniform mean bound | `norm_mean_weightTerm_le` |
| Evaluation at `a`, middle range, tail; unique divisor | `weightLimit_self`, `weightLimit_eq_zero_of_le`, `norm_weightLimit_le_of_lt`, `eq_of_coprime_div` |
| Limit up to tail; tail → 0 | `norm_tsum_weightLimit_sub_le`, `tendsto_tailSum` |
| **Sign rigidity** | `eq_zero_of_re_mul_conj_zeta_nonpos`, `…_of_lSeriesSummable` |
| **Uniqueness; RH equivalence** | `WeilZetaSquare.eq_delta_and_eq_zero_of_weilPositiveFull_mobius`, `exists_weilPositive_mobius_iff` |

- Modules (all wired in `RHTower.lean` after `WeilZetaSquareDilationRigidity`):
  - `RHTower/ZetaTwistedFirstMomentUniform`;
  - `RHTower/AbsolutelyConvergentZetaSignRigidity`;
  - `RHTower/WeilZetaSquareMobiusRigidity`.
- Audit: `lake --old build` green, zero messages under `lake env lean --json`, axioms `[propext, Classical.choice, Quot.sound]`.

## Novelty and scope
- External search (Oct 2026): nothing on sign rigidity of Dirichlet series against `ζ` on the line, nor on uniqueness of Weil-positive weights.
- This is the uniqueness half (U) of template (d). It is RH-blind: under ¬RH the class is empty. Its content is detection. The natural "meromorphic repairs" of `Λ` are `μ⋆f` parts whose `F/ζ` cancels the off-line poles, and no such repair can be Weil-positive.
- Still open in U:
  - `Λ⋆a + μ⋆f + v` with infinite `f` and regular `v ≠ 0`. With `A = 1` the term `Re V·|ζ|²` is of order `T log T`, against `O(T)` for `Re(Fζ̄)`; Step 4 of row 538's card handles `v` once `f` is known.
  - Non-multiplicative, full-scale deviations.

## Log
- 2026-10-07 (loop row 539): proved and formalized.
