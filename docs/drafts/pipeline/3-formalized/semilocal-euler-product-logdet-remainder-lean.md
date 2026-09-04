# The determinant-level Taylor remainder for the true finite-`S` Euler product

**Stage:** 3 (formalized), 2026-09-04.  Closes MUST-180.  Two new modules
(`MatrixEntryNormLogDetRemainder`, `SemilocalEulerProductLogDetRemainder`), wired into `RHTower.lean`,
axioms `[propext, Classical.choice, Quot.sound]`.  Completes the second-order theory of the semilocal
Jacobi data (`semilocal-finite-prime-second-order-lean.md`) into a **theorem with explicit remainder for
the true Euler product** rather than for its quadratic truncation.

## Generic engine (`RHTower.MatrixLogDet`)

With the `ℓ¹` entry norm `‖N‖₁ = Σ_{i,j} |N i j|` (`entryNorm`; submultiplicative,
`|tr A| ≤ ‖A‖₁`, `‖1‖₁ = d`):

* `det_one_add_ne_zero`, `det_one_add_pos`: `‖N‖₁ < 1 ⇒ det(1+N) > 0` (kernel argument + IVT along
  `1 + tN`); `entryNorm_inv_one_add_le`: `‖(1+N)⁻¹‖₁ ≤ d/(1 − ‖N‖₁)` (Neumann identity
  `R = 1 − NR`, no series);
* the path `f(t) = log det(1 + tN)`: `f' = tr((1+tN)⁻¹N)`, `f'' = −tr((1+tN)⁻¹N(1+tN)⁻¹N)`
  (`hasDerivAt_logDetPath`, `hasDerivAt_logDetSlope`), `|f''(t) − f''(0)| ≤ t·d(d+1)‖N‖₁³/(1−‖N‖₁)²`;
* **`abs_log_det_one_add_sub_jet_le`**: `|log det(1+N) − tr N + ½ tr N²| ≤ d(d+1)‖N‖₁³/(1−‖N‖₁)²`
  (two mean-value estimates, `norm_image_sub_le_of_norm_deriv_le_segment'`);
* **`abs_log_det_sub_secondOrderJet_le`**: for `N = M₁ + M₂ + E`,
  `|log det(1+N) − (tr M₁ + tr M₂ − ½ tr M₁²)| ≤ [above] + ‖E‖₁ + ½(2‖M₁‖₁‖M₂+E‖₁ + ‖M₂+E‖₁²)`.

## The Euler product (`RHTower.CosineModeResponse`)

`W(s) = ∏_a (1 − 2ε_a cos(δ_a s) + ε_a²)⁻¹`, `ε_a ∈ [0, 1/6]`, `V = Σ ε_a ≤ 1/4`.

* **Weight level** (`abs_eulerProductWeight_sub_rayWeight_le`):
  `|W − (1 + A + B)| ≤ ρ := (3/2)^k·60 Σ ε_a³ + 12800 V³`, from the one-factor `60ε³` bound, the
  telescoping estimate `|∏f − ∏g| ≤ C^{|s|} Σ|f_a − g_a|` (`abs_finset_prod_sub_prod_le`), and the
  **cubic form** of the quadratic-truncation lemma (`abs_prod_sub_quadratic_le_cubic`):
  `|∏(1 + x_a + y_a) − (1 + Σx + Σy + ½((Σx)² − Σx²))| ≤ 200 L³`, `L = Σ(|x_a| + √|y_a|) ≤ 1`
  (scaling `t = L` in the ray lemma, `∏(1+u) ≤ e^{Σu}`);
  the truncation is exactly the ray weight `1 + rayFirst + raySecond` (`rayTruncation_eq`).
* **Gram entries**: `|∫ p_i p_j f| ≤ sup|f|` from `|p_ip_j| ≤ ½(p_i² + p_j²)` and orthonormality
  (`integral_abs_eval_mul_eval_le_one`, `abs_integral_eval_mul_eval_mul_le`), so
  `|T(δ)_{ij}| ≤ 2`, `‖M₁‖₁ ≤ 2(n+1)²V`, `‖M₂‖₁ ≤ 3(n+1)²V²`, `‖E‖₁ ≤ (n+1)²ρ`.
* **Main theorem** (`abs_log_det_eulerProductGram_sub_jet_le`): with
  `entrySize = (n+1)²(2V + 3V² + ρ) < 1`,

      |log det G_n(W) − (tr M₁ + tr M₂ − ½ tr M₁²)| ≤ logDetRemainderBound ε n   (explicit, O(V³)),

  and the jet is the corpus jet `Σ ε_a J_{δ_a} + ½(Σ_{a,b} ε_aε_b B_{ab} + Σ ε_a² J_{2δ_a})`
  (`secondOrderLogDetJet_eq`); `det G_n(W) > 0` (`eulerProductGram_det_pos`).
* **Radius level** (`abs_log_eulerProductSquaredRadius_sub_jet_le`): for the Hankel quotient
  `a²_{n+1} = r²_{n+1} Δ_n Δ_{n+2}/Δ_{n+1}²` of the true Euler product,
  `|log(a²_{n+1}/r²_{n+1}) − ΔΔ(second-order jet)| ≤ K_n + K_{n+2} + 2K_{n+1}`.

So the finite-`S` semilocal Jacobi radii of the **true** Euler product are the archimedean radii times
`exp` of the second difference of the second-order jet, up to an explicit third-order error — the
first-order (`O(q)`) and second-order (one-prime `O(q²)`, pairwise beat `O(√(q_aq_b))`) laws of the
earlier cycles are now unconditional statements about the actual measure, not about a truncation.

## Numerics (`computations/routej-semilocal-scale/logdet_remainder_check.py`, `.log`)

`S = {101, 211, 307}`: the remainder `log det G_W − jet` scales as `λ³` under `ε → λε` (ratios
`8.2, 8.2, 8.1` at `n = 2`; `8.5, 8.3, 8.2` at `n = 5`; `7.4, 7.8, 7.9` at `n = 10`), the trace form of
the jet equals the corpus-jet form to machine precision, and at the radius level the remainder of
`ΔΔ` is `2·10⁻⁵` (n = 5) against a signal `2.3·10⁻²`.  The entry-norm constants are crude: at
`n = 10` the true `‖N‖_op ≈ 0.16` while `‖N‖₁ ≈ 1.1`, so the theorem's smallness condition is far
from the numerically visible regime — the operator-norm refinement is the next step.

| module | content |
|---|---|
| `MatrixEntryNormLogDetRemainder` | `entryNorm` calculus, `det_one_add_ne_zero/pos`, `entryNorm_inv_one_add_le`, `logDetPath/Slope/Curv` with derivatives, `abs_logDetCurv_sub_zero_le`, **`abs_log_det_one_add_sub_jet_le`**, **`abs_log_det_sub_secondOrderJet_le`** |
| `SemilocalEulerProductLogDetRemainder` | `abs_finset_prod_sub_prod_le`, **`abs_prod_sub_quadratic_le_cubic`**, `semilocalEulerFactor`, `semilocalQuadraticFactor`, `rayTruncation_eq`, `eulerProductWeight`, `weightRemainder`, **`abs_eulerProductWeight_sub_rayWeight_le`**, `integral_abs_eval_mul_eval_le_one`, `abs_integral_eval_mul_eval_mul_le`, `entryNorm_cosineModeTangent_le`, `entryNorm_rayM₁_le`, `entryNorm_rayM₂_le`, `eulerProductGram`, `secondOrderLogDetJet(_eq)`, `entrySize`, `logDetRemainderBound`, `eulerProductGram_det_pos`, **`abs_log_det_eulerProductGram_sub_jet_le`**, `eulerProductSquaredRadius`, **`abs_log_eulerProductSquaredRadius_sub_jet_le`** |

**Next:** the `n`-uniform version through the operator norm (`‖G_W − 1‖_op ≤ sup|W − 1| ≤ 3V` by the
quadratic form in the orthonormal basis), which makes the smallness condition independent of `n`
and the remainder `(n+1)·O(V³)`; then the order-one threshold `n ~ p^{4/3}` as the failure of the
remainder bound.
