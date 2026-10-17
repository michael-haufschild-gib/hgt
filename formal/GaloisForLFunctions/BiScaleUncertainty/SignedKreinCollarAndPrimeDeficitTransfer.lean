import GaloisForLFunctions.BiScaleUncertainty.MultiCosetGramPackingAndNyquistDensity

/-!
# Pillar XIV: Signed Krein Collar Transfer & Prime-Deficit Coercivity

This module develops **Pillar XIV** of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`), resolving **Trap 9 (The Homogeneous Blind-Subspace
Trap)**.

In Pillars I–XIII, lower bounds on the archimedean Lévy energy `biScaleLevyEnergy f` were proved on
the **grid-blind subspace** `h_f(t_i) = 0`. However, restricting to `h_f(log n) = 0` multiplies the
arithmetic von Mangoldt weights `Λ(n) / √n` by zero, erasing the prime distribution and leaving the
general **signed prime quadratic form** `∑_{n ≥ 2} (Λ(n) / √n) h_f(log n)` in `EWU` and `HF`
uncontrolled when `h_f(log n) < 0`.

This module drops the blindness hypothesis `h_f(t_i) = 0` completely and proves that every
single-node Krein collar bound, multi-node Origin-Singularity Leverage bound, and Selberg–Bombieri
multi-coset Gram bound lifts unconditionally to the **combined signed archimedean-plus-arithmetic
functional**
$$\mathcal{J}_{\mathrm{arch}}(f) + \sum_{i \in s} M_i\, h_f(t_i).$$
Crucially, at each logarithmic grid node `t_n = log n` (`n ≥ 2`), the archimedean Lévy weight is
$$\operatorname{archLevySinhWeight}(\log n) = \frac{2}{\sqrt{n}(1 - n^{-2})} = \frac{2}{\sqrt{n}} + \frac{2}{\sqrt{n}(n^2 - 1)},$$
which matches the critical-line exponent `n^{-1/2}` of the Weil explicit formula prime weight
`2 Λ(n) / √n` up to an explicit `O(n^{-5/2})` hyperbolic remainder.

## Main Results

### §1. Exact Signed Collar-Increment Identities & Pointwise Krein Coercivity
1. **`autocorr_signed_collar_add_eq` & `autocorr_signed_collar_sub_eq`**:
   Exact ring decomposition valid for arbitrary signed `h_f(t) ∈ ℝ`:
   `(h_f(0) - h_f(t ± y)) + h_f(t) = h_f(0) - (h_f(t ± y) - h_f(t))`.
2. **`autocorr_signed_collar_add_ge_krein` & `autocorr_signed_collar_sub_ge_krein`**:
   Unconditional lower bound without any blindness assumption:
   `h_f(0) - √(2 h_f(0) (h_f(0) - h_f(y))) ≤ (h_f(0) - h_f(t ± y)) + h_f(t)`.
3. **`autocorr_signed_collar_origin_leverage_add` & `autocorr_signed_collar_origin_leverage_sub`**:
   Two-point origin-to-collar leverage for arbitrary signed node values `h_f(t) ∈ ℝ`:
   `(w - w² / (2 W₀)) h_f(0) ≤ W₀ (h_f(0) - h_f(y)) + w (h_f(0) - h_f(t ± y)) + w h_f(t)`.

### §2. Abstract Hilbert-Space Multi-Node Signed Collar Completion of Squares
4. **`abstract_signed_collar_gram_identity` & `abstract_signed_collar_gram_ge`**:
   In any real inner product space `E`, for any `x, x_y ∈ E` with `‖x‖² = ‖x_y‖² = R` and any
   family `e : ι → E`:
   $$W_0(R - \langle x, x_y\rangle) + \sum_{i \in s} w_i(R - \langle e_i, x_y\rangle) + \sum_{i \in s} w_i\langle e_i, x\rangle
     = \left(\sum_{i \in s} w_i\right) R - \frac{1}{2 W_0}\sum_{i, j \in s} w_i w_j \langle e_i, e_j\rangle
       + \frac{1}{2 W_0}\left\|\sum_{i \in s} w_i e_i - W_0(x_y - x)\right\|^2.$$
5. **`abstract_signed_clique_origin_leverage_ge` & `abstract_signed_almost_orthogonal_origin_leverage_ge`**:
   Specializations to orthogonal cliques (`⟪e_i, e_j⟫ = 0` for `i ≠ j`) and Selberg–Bombieri
   almost-orthogonal families (`∑_{j ∈ s} |⟪e_i, e_j⟫| ≤ (1 + Δ) R`).

### §3. Concrete Autocorrelation Multi-Node Signed Collar & Nyquist Window Bounds
6. **`sum_integral_signed_nyquist_collar_ge`**:
   Integrates the signed collar bound across the `N` Nyquist cells `[log(N+k), log(N+k+1)]` tiling
   `[log N, log(2N)]` without assuming `h_f(log(N+k)) = 0`.
7. **`archLevySinhWeight_log_nat_eq`, `archLevySinhWeight_log_nat_ge_two_div_sqrt`, &
   `archLevySinhWeight_log_nat_sub_two_div_sqrt_le`**:
   Exact critical-line `2 / √n` scaling law and `O(n^{-5/2})` remainder bound for
   `archLevySinhWeight (log n)` at every integer `n ≥ 2`.
-/

namespace GaloisForLFunctions.BiScaleUncertainty

open MeasureTheory Set Filter
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open scoped RealInnerProductSpace BigOperators

noncomputable section

/-! ## §1. Exact Signed Collar-Increment Identities & Pointwise Krein Coercivity -/

/-- **Right Signed Collar-Increment Identity:**
For any `f : ℝ → ℝ`, node `t ∈ ℝ`, and collar offset `y ∈ ℝ`, the sum of the archimedean collar
defect `h_f(0) - h_f(t + y)` and the signed node correlation `h_f(t)` equals `h_f(0)` minus the
local increment `h_f(t + y) - h_f(t)`. -/
theorem autocorr_signed_collar_add_eq (f : ℝ → ℝ) (t y : ℝ) :
    (autocorr f 0 - autocorr f (t + y)) + autocorr f t =
      autocorr f 0 - (autocorr f (t + y) - autocorr f t) := by
  ring

/-- **Left Signed Collar-Increment Identity:**
For any `f : ℝ → ℝ`, node `t ∈ ℝ`, and collar offset `y ∈ ℝ`,
`(h_f(0) - h_f(t - y)) + h_f(t) = h_f(0) - (h_f(t - y) - h_f(t))`. -/
theorem autocorr_signed_collar_sub_eq (f : ℝ → ℝ) (t y : ℝ) :
    (autocorr f 0 - autocorr f (t - y)) + autocorr f t =
      autocorr f 0 - (autocorr f (t - y) - autocorr f t) := by
  ring

/-- **Krein Increment Bound for `|h_f(t + y) - h_f(t)|`:**
For any continuous compactly supported `f`, `|h_f(t + y) - h_f(t)| ≤ √(2 h_f(0) (h_f(0) - h_f(y)))`. -/
theorem abs_autocorr_add_sub_le_sqrt {f : ℝ → ℝ} (hfc : HasCompactSupport f) (hf : Continuous f)
    (t y : ℝ) :
    |autocorr f (t + y) - autocorr f t| ≤
      Real.sqrt (2 * autocorr f 0 * (autocorr f 0 - autocorr f y)) := by
  have hkrein := autocorr_krein_increment_sq_le hfc hf (t + y) t
  have hdiff : t + y - t = y := by ring
  rw [hdiff] at hkrein
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hkrein

/-- **Krein Increment Bound for `|h_f(t - y) - h_f(t)|`:**
For any continuous compactly supported `f`, `|h_f(t - y) - h_f(t)| ≤ √(2 h_f(0) (h_f(0) - h_f(y)))`. -/
theorem abs_autocorr_sub_sub_le_sqrt {f : ℝ → ℝ} (hfc : HasCompactSupport f) (hf : Continuous f)
    (t y : ℝ) :
    |autocorr f (t - y) - autocorr f t| ≤
      Real.sqrt (2 * autocorr f 0 * (autocorr f 0 - autocorr f y)) := by
  have hkrein := autocorr_krein_increment_sq_le hfc hf t (t - y)
  have hdiff : t - (t - y) = y := by ring
  rw [hdiff] at hkrein
  have habs : |autocorr f (t - y) - autocorr f t| = |autocorr f t - autocorr f (t - y)| :=
    abs_sub_comm _ _
  rw [habs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hkrein

/-- **Pointwise Right Signed Krein Collar Coercivity (No Blindness Assumption):**
For any continuous compactly supported `f` and any `t, y ∈ ℝ`,
`h_f(0) - √(2 h_f(0) (h_f(0) - h_f(y))) ≤ (h_f(0) - h_f(t + y)) + h_f(t)`. -/
theorem autocorr_signed_collar_add_ge_krein {f : ℝ → ℝ} (hfc : HasCompactSupport f)
    (hf : Continuous f) (t y : ℝ) :
    autocorr f 0 - Real.sqrt (2 * autocorr f 0 * (autocorr f 0 - autocorr f y)) ≤
      (autocorr f 0 - autocorr f (t + y)) + autocorr f t := by
  rw [autocorr_signed_collar_add_eq]
  have h1 : autocorr f (t + y) - autocorr f t ≤ |autocorr f (t + y) - autocorr f t| :=
    le_abs_self _
  have h2 := abs_autocorr_add_sub_le_sqrt hfc hf t y
  linarith

/-- **Pointwise Left Signed Krein Collar Coercivity (No Blindness Assumption):**
For any continuous compactly supported `f` and any `t, y ∈ ℝ`,
`h_f(0) - √(2 h_f(0) (h_f(0) - h_f(y))) ≤ (h_f(0) - h_f(t - y)) + h_f(t)`. -/
theorem autocorr_signed_collar_sub_ge_krein {f : ℝ → ℝ} (hfc : HasCompactSupport f)
    (hf : Continuous f) (t y : ℝ) :
    autocorr f 0 - Real.sqrt (2 * autocorr f 0 * (autocorr f 0 - autocorr f y)) ≤
      (autocorr f 0 - autocorr f (t - y)) + autocorr f t := by
  rw [autocorr_signed_collar_sub_eq]
  have h1 : autocorr f (t - y) - autocorr f t ≤ |autocorr f (t - y) - autocorr f t| :=
    le_abs_self _
  have h2 := abs_autocorr_sub_sub_le_sqrt hfc hf t y
  linarith

/-- **Scalar Completion-of-Squares Lemma for Signed Origin-Collar Leverage:**
For any `W₀ > 0`, `w ∈ ℝ`, `R ≥ 0`, and `D ≥ 0`,
`w * √(2 R D) ≤ W₀ * D + (w² / (2 W₀)) * R`. -/
theorem signed_collar_young_bound {W₀ w R D : ℝ} (hW₀ : 0 < W₀)
    (hR : 0 ≤ R) (hD : 0 ≤ D) :
    w * Real.sqrt (2 * R * D) ≤ W₀ * D + w ^ 2 / (2 * W₀) * R := by
  have h2R : 0 ≤ 2 * R := by linarith
  have hsqrt_split : Real.sqrt (2 * R * D) = Real.sqrt (2 * R) * Real.sqrt D :=
    Real.sqrt_mul h2R D
  rw [hsqrt_split]
  have hsq : 0 ≤ (Real.sqrt W₀ * Real.sqrt D - w / (2 * Real.sqrt W₀) * Real.sqrt (2 * R)) ^ 2 :=
    sq_nonneg _
  have hW₀_nn : 0 ≤ W₀ := le_of_lt hW₀
  have hsqrtW₀_ne : Real.sqrt W₀ ≠ 0 := Real.sqrt_ne_zero'.mpr hW₀
  have hexp :
      (Real.sqrt W₀ * Real.sqrt D - w / (2 * Real.sqrt W₀) * Real.sqrt (2 * R)) ^ 2 =
        W₀ * D - w * (Real.sqrt (2 * R) * Real.sqrt D) + w ^ 2 / (2 * W₀) * R := by
    calc
      (Real.sqrt W₀ * Real.sqrt D - w / (2 * Real.sqrt W₀) * Real.sqrt (2 * R)) ^ 2
          = (Real.sqrt W₀) ^ 2 * (Real.sqrt D) ^ 2 -
              2 * (Real.sqrt W₀ * Real.sqrt D) * (w / (2 * Real.sqrt W₀) * Real.sqrt (2 * R)) +
              w ^ 2 / (4 * (Real.sqrt W₀) ^ 2) * (Real.sqrt (2 * R)) ^ 2 := by
            ring
      _ = W₀ * D -
              2 * (Real.sqrt W₀ * Real.sqrt D) * (w / (2 * Real.sqrt W₀) * Real.sqrt (2 * R)) +
              w ^ 2 / (4 * W₀) * (2 * R) := by
            rw [Real.sq_sqrt hW₀_nn, Real.sq_sqrt hD, Real.sq_sqrt h2R]
      _ = W₀ * D - w * (Real.sqrt (2 * R) * Real.sqrt D) + w ^ 2 / (2 * W₀) * R := by
            field_simp [hsqrtW₀_ne, ne_of_gt hW₀]
            ring
  linarith

/-- **Single-Node Right Signed Origin-Singularity Leverage (No Blindness Assumption):**
For any continuous compactly supported `f`, any origin weight `W₀ > 0`, and any collar weight
`w ≥ 0`,
`(w - w² / (2 W₀)) h_f(0) ≤ W₀ (h_f(0) - h_f(y)) + w (h_f(0) - h_f(t + y)) + w h_f(t)`. -/
theorem autocorr_signed_collar_origin_leverage_add {f : ℝ → ℝ} (hfc : HasCompactSupport f)
    (hf : Continuous f) {W₀ w : ℝ} (hW₀ : 0 < W₀) (hw : 0 ≤ w) (t y : ℝ) :
    (w - w ^ 2 / (2 * W₀)) * autocorr f 0 ≤
      W₀ * (autocorr f 0 - autocorr f y) +
        w * (autocorr f 0 - autocorr f (t + y)) + w * autocorr f t := by
  have hR : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have hD : 0 ≤ autocorr f 0 - autocorr f y := autocorr_sub_nonneg hfc hf y
  have hkrein := mul_le_mul_of_nonneg_left (autocorr_signed_collar_add_ge_krein hfc hf t y) hw
  have hyoung := signed_collar_young_bound (w := w) hW₀ hR hD
  linarith

/-- **Single-Node Left Signed Origin-Singularity Leverage (No Blindness Assumption):**
For any continuous compactly supported `f`, any origin weight `W₀ > 0`, and any collar weight
`w ≥ 0`,
`(w - w² / (2 W₀)) h_f(0) ≤ W₀ (h_f(0) - h_f(y)) + w (h_f(0) - h_f(t - y)) + w h_f(t)`. -/
theorem autocorr_signed_collar_origin_leverage_sub {f : ℝ → ℝ} (hfc : HasCompactSupport f)
    (hf : Continuous f) {W₀ w : ℝ} (hW₀ : 0 < W₀) (hw : 0 ≤ w) (t y : ℝ) :
    (w - w ^ 2 / (2 * W₀)) * autocorr f 0 ≤
      W₀ * (autocorr f 0 - autocorr f y) +
        w * (autocorr f 0 - autocorr f (t - y)) + w * autocorr f t := by
  have hR : 0 ≤ autocorr f 0 := autocorr_zero_nonneg f
  have hD : 0 ≤ autocorr f 0 - autocorr f y := autocorr_sub_nonneg hfc hf y
  have hkrein := mul_le_mul_of_nonneg_left (autocorr_signed_collar_sub_ge_krein hfc hf t y) hw
  have hyoung := signed_collar_young_bound (w := w) hW₀ hR hD
  linarith

/-! ## §2. Abstract Hilbert-Space Multi-Node Signed Collar Completion of Squares -/

section AbstractHilbertSignedCollar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*}

/-- **Exact Abstract Hilbert-Space Signed Collar Completion-of-Squares Identity:**
For any origin state `x ∈ E` and shifted state `x_y ∈ E` with `‖x‖² = R` and `‖x_y‖² = R`, any
node family `e : ι → E`, any weights `w : ι → ℝ`, and any `W₀ ≠ 0`:
$$W_0(R - \langle x, x_y\rangle) + \sum_{i \in s} w_i(R - \langle e_i, x_y\rangle) + \sum_{i \in s} w_i\langle e_i, x\rangle
  = \left(\sum_{i \in s} w_i\right) R - \frac{1}{2 W_0}\sum_{i \in s}\sum_{j \in s} w_i w_j \langle e_i, e_j\rangle
    + \frac{1}{2 W_0}\left\|\sum_{i \in s} w_i e_i - W_0(x_y - x)\right\|^2.$$ -/
theorem abstract_signed_collar_gram_identity (s : Finset ι) (e : ι → E) (w : ι → ℝ)
    {x x_y : E} {R W₀ : ℝ} (hx : ‖x‖ ^ 2 = R) (hxy : ‖x_y‖ ^ 2 = R) (hW₀ : W₀ ≠ 0) :
    W₀ * (R - ⟪x, x_y⟫) + ∑ i ∈ s, w i * (R - ⟪e i, x_y⟫) + ∑ i ∈ s, w i * ⟪e i, x⟫ =
      (∑ i ∈ s, w i) * R -
        (1 / (2 * W₀)) * ∑ i ∈ s, ∑ j ∈ s, w i * w j * ⟪e i, e j⟫ +
        (1 / (2 * W₀)) * ‖∑ i ∈ s, w i • e i - W₀ • (x_y - x)‖ ^ 2 := by
  set S_quad : ℝ := ∑ i ∈ s, ∑ j ∈ s, w i * w j * ⟪e i, e j⟫
  set S_diff : ℝ := ∑ i ∈ s, (w i * ⟪e i, x_y⟫ - w i * ⟪e i, x⟫)
  have hnorm_diff : ‖x_y - x‖ ^ 2 = 2 * (R - ⟪x, x_y⟫) := by
    rw [norm_sub_sq_real, hxy, hx, real_inner_comm x_y x]
    ring
  have hnorm_smul : ‖W₀ • (x_y - x)‖ ^ 2 = W₀ ^ 2 * (2 * (R - ⟪x, x_y⟫)) := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hnorm_diff]
  have hnorm_sum : ‖∑ i ∈ s, w i • e i‖ ^ 2 = S_quad := by
    dsimp [S_quad]
    rw [sq, ← real_inner_self_eq_norm_mul_norm]
    exact inner_sum_self_eq_double_sum s e w
  have hinner_cross : ⟪∑ i ∈ s, w i • e i, W₀ • (x_y - x)⟫ = W₀ * S_diff := by
    dsimp [S_diff]
    rw [real_inner_smul_right, sum_inner]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, inner_sub_right]
    ring
  have hexp :
      ‖∑ i ∈ s, w i • e i - W₀ • (x_y - x)‖ ^ 2 =
        S_quad - 2 * W₀ * S_diff + 2 * W₀ ^ 2 * (R - ⟪x, x_y⟫) := by
    rw [norm_sub_sq_real, hnorm_sum, hinner_cross, hnorm_smul]
    ring
  have hsum_R :
      (∑ i ∈ s, w i * (R - ⟪e i, x_y⟫)) + (∑ i ∈ s, w i * ⟪e i, x⟫) =
        (∑ i ∈ s, w i) * R - S_diff := by
    dsimp [S_diff]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hexp, show W₀ * (R - ⟪x, x_y⟫) + ∑ i ∈ s, w i * (R - ⟪e i, x_y⟫) + ∑ i ∈ s, w i * ⟪e i, x⟫ =
      W₀ * (R - ⟪x, x_y⟫) + ((∑ i ∈ s, w i * (R - ⟪e i, x_y⟫)) + ∑ i ∈ s, w i * ⟪e i, x⟫) by ring,
    hsum_R]
  have h2W₀ : 2 * W₀ ≠ 0 := mul_ne_zero two_ne_zero hW₀
  field_simp [h2W₀, hW₀]
  ring

/-- **Universal Abstract Multi-Node Signed Collar Gram Inequality (No Blindness Assumption):**
For any `W₀ > 0`, dropping the nonnegative squared norm in `abstract_signed_collar_gram_identity`
yields:
$$W_0(R - \langle x, x_y\rangle) + \sum_{i \in s} w_i(R - \langle e_i, x_y\rangle) + \sum_{i \in s} w_i\langle e_i, x\rangle
  \;\ge\; \left(\sum_{i \in s} w_i\right) R - \frac{1}{2 W_0}\sum_{i \in s}\sum_{j \in s} w_i w_j \langle e_i, e_j\rangle.$$ -/
theorem abstract_signed_collar_gram_ge (s : Finset ι) (e : ι → E) (w : ι → ℝ)
    {x x_y : E} {R W₀ : ℝ} (hx : ‖x‖ ^ 2 = R) (hxy : ‖x_y‖ ^ 2 = R) (hW₀ : 0 < W₀) :
    (∑ i ∈ s, w i) * R -
        (1 / (2 * W₀)) * ∑ i ∈ s, ∑ j ∈ s, w i * w j * ⟪e i, e j⟫ ≤
      W₀ * (R - ⟪x, x_y⟫) + ∑ i ∈ s, w i * (R - ⟪e i, x_y⟫) + ∑ i ∈ s, w i * ⟪e i, x⟫ := by
  rw [abstract_signed_collar_gram_identity s e w hx hxy (ne_of_gt hW₀)]
  have hpos : 0 ≤ (1 / (2 * W₀)) * ‖∑ i ∈ s, w i • e i - W₀ • (x_y - x)‖ ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  linarith

/-- **Signed Multi-Node Clique Origin-Singularity Leverage in Abstract Hilbert Space:**
If `{e_i}_{i ∈ s}` is an orthogonal clique with `⟪e_i, e_i⟫ = R` and `⟪e_i, e_j⟫ = 0` (`i ≠ j`),
then for any signed values `⟪e_i, x⟫ ∈ ℝ` (no blindness required!) and any `W₀ > 0`:
$$\left(\sum_{i \in s} w_i - \frac{\sum_{i \in s} w_i^2}{2 W_0}\right) R
  \;\le\; W_0(R - \langle x, x_y\rangle) + \sum_{i \in s} w_i(R - \langle e_i, x_y\rangle) + \sum_{i \in s} w_i\langle e_i, x\rangle.$$ -/
theorem abstract_signed_clique_origin_leverage_ge (s : Finset ι) (e : ι → E) (w : ι → ℝ)
    {x x_y : E} {R W₀ : ℝ} (hx : ‖x‖ ^ 2 = R) (hxy : ‖x_y‖ ^ 2 = R)
    (hdiag : ∀ i ∈ s, ⟪e i, e i⟫ = R)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪e i, e j⟫ = 0)
    (hW₀ : 0 < W₀) :
    (∑ i ∈ s, w i - (∑ i ∈ s, w i ^ 2) / (2 * W₀)) * R ≤
      W₀ * (R - ⟪x, x_y⟫) + ∑ i ∈ s, w i * (R - ⟪e i, x_y⟫) + ∑ i ∈ s, w i * ⟪e i, x⟫ := by
  have hgram : ∑ i ∈ s, ∑ j ∈ s, w i * w j * ⟪e i, e j⟫ = (∑ i ∈ s, w i ^ 2) * R := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i]
    · rw [hdiag i hi]
      ring
    · intro j hj hji
      rw [horth i hi j hj (Ne.symm hji), mul_zero]
    · intro hi_not
      exact (hi_not hi).elim
  have hbase := abstract_signed_collar_gram_ge s e w hx hxy hW₀
  rw [hgram] at hbase
  have hring :
      (∑ i ∈ s, w i - (∑ i ∈ s, w i ^ 2) / (2 * W₀)) * R =
        (∑ i ∈ s, w i) * R - 1 / (2 * W₀) * ((∑ i ∈ s, w i ^ 2) * R) := by
    ring
  linarith

/-- **Signed Selberg–Bombieri Multi-Coset Origin-Singularity Leverage in Abstract Hilbert Space:**
If the Gram matrix `{⟪e_i, e_j⟫}_{i, j ∈ s}` satisfies the Selberg–Bombieri row-sum bound
`∑_{j ∈ s} |⟪e_i, e_j⟫| ≤ (1 + Δ) R`, then for any signed values `⟪e_i, x⟫ ∈ ℝ` and any `W₀ > 0`:
$$\left(\sum_{i \in s} w_i - \frac{1 + \Delta}{2 W_0}\sum_{i \in s} w_i^2\right) R
  \;\le\; W_0(R - \langle x, x_y\rangle) + \sum_{i \in s} w_i(R - \langle e_i, x_y\rangle) + \sum_{i \in s} w_i\langle e_i, x\rangle.$$ -/
theorem abstract_signed_almost_orthogonal_origin_leverage_ge (s : Finset ι) (e : ι → E) (w : ι → ℝ)
    {x x_y : E} {R W₀ Δ : ℝ} (hx : ‖x‖ ^ 2 = R) (hxy : ‖x_y‖ ^ 2 = R)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, |⟪e i, e j⟫| ≤ (1 + Δ) * R)
    (hW₀ : 0 < W₀) :
    (∑ i ∈ s, w i - (1 + Δ) * (∑ i ∈ s, w i ^ 2) / (2 * W₀)) * R ≤
      W₀ * (R - ⟪x, x_y⟫) + ∑ i ∈ s, w i * (R - ⟪e i, x_y⟫) + ∑ i ∈ s, w i * ⟪e i, x⟫ := by
  have hquad := gram_quad_le_of_row_sum_bound s e w hrow
  have hdiv :
      (1 / (2 * W₀)) * ∑ i ∈ s, ∑ j ∈ s, w i * w j * ⟪e i, e j⟫ ≤
        (1 / (2 * W₀)) * ((1 + Δ) * R * ∑ i ∈ s, w i ^ 2) :=
    mul_le_mul_of_nonneg_left hquad (by positivity)
  have hbase := abstract_signed_collar_gram_ge s e w hx hxy hW₀
  have hring :
      (∑ i ∈ s, w i - (1 + Δ) * (∑ i ∈ s, w i ^ 2) / (2 * W₀)) * R =
        (∑ i ∈ s, w i) * R - 1 / (2 * W₀) * ((1 + Δ) * R * ∑ i ∈ s, w i ^ 2) := by
    ring
  linarith

end AbstractHilbertSignedCollar

/-! ## §3. Concrete Autocorrelation Multi-Node Signed Collar & Nyquist Window Bounds -/

section ConcreteSignedAutocorr

variable {ι : Type*}

/-- Translation-invariance identity for shifted autocorrelation products:
`∫ u, f(u - a) f(u - b) = autocorr f (a - b)`. -/
theorem integral_shift_sub_mul_shift_sub_eq_autocorr (f : ℝ → ℝ) (a b : ℝ) :
    (∫ u : ℝ, f (u - a) * f (u - b)) = autocorr f (a - b) := by
  unfold autocorr
  have hchg := MeasureTheory.integral_add_right_eq_self (μ := volume)
    (fun u : ℝ => f (u - a) * f (u - b)) a
  rw [← hchg]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only
  have h1 : u + a - a = u := by ring
  have h2 : u + a - b = u + (a - b) := by ring
  rw [h1, h2]

/-- Translation-invariance identity for shifted autocorrelation increments:
`∫ u, f(u - t) (f(u + y) - f(u)) = autocorr f (t + y) - autocorr f t`. -/
theorem integral_shift_sub_mul_diff_eq_autocorr_sub {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (hf : Continuous f) (t y : ℝ) :
    (∫ u : ℝ, f (u - t) * (f (u + y) - f u)) = autocorr f (t + y) - autocorr f t := by
  have hint1 : Integrable (fun u : ℝ => f (u - t) * f (u + y)) volume := by
    have hcont : Continuous (fun u : ℝ => f (u - t) * f (u + y)) :=
      (hf.comp (continuous_id.sub continuous_const)).mul
        (hf.comp (continuous_id.add continuous_const))
    have hsupp : HasCompactSupport (fun u : ℝ => f (u - t) * f (u + y)) :=
      (hfc.comp_homeomorph (Homeomorph.subRight t)).mul_right
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hint2 : Integrable (fun u : ℝ => f (u - t) * f u) volume := by
    have hcont : Continuous (fun u : ℝ => f (u - t) * f u) :=
      (hf.comp (continuous_id.sub continuous_const)).mul hf
    have hsupp : HasCompactSupport (fun u : ℝ => f (u - t) * f u) :=
      (hfc.comp_homeomorph (Homeomorph.subRight t)).mul_right
    exact hcont.integrable_of_hasCompactSupport hsupp
  have hsub :
      (fun u : ℝ => f (u - t) * (f (u + y) - f u)) =
        (fun u : ℝ => f (u - t) * f (u + y) - f (u - t) * f u) := by
    funext u; ring
  rw [hsub, MeasureTheory.integral_sub hint1 hint2]
  have h1 := integral_shift_sub_mul_shift_sub_eq_autocorr f t (-y)
  have h1' : (fun u : ℝ => f (u - t) * f (u - -y)) = (fun u : ℝ => f (u - t) * f (u + y)) := by
    funext u; rw [sub_neg_eq_add]
  have h2 := integral_shift_sub_mul_shift_sub_eq_autocorr f t 0
  have h2' : (fun u : ℝ => f (u - t) * f (u - 0)) = (fun u : ℝ => f (u - t) * f u) := by
    funext u; rw [sub_zero]
  rw [h1', sub_neg_eq_add] at h1
  rw [h2', sub_zero] at h2
  rw [h1, h2]

/-- **Signed Dyadic-Window Nyquist Sum-to-Integral Collar Bound:**
Across the `N` Nyquist cells `[log(N+k), log(N+k+1)]` (`0 ≤ k < N`) tiling `[log N, log(2N)]`,
for ANY `f ∈ C²_c(ℝ)` with **arbitrary signed node values** `h_f(log(N+k)) ∈ ℝ` (no grid-blindness
required!) and any origin weight `W₀ > 0`:
$$\sum_{k=0}^{N-1} \int_{\log(N+k)}^{\log(N+k+1)} \Bigl(\bigl(h_f(0) - h_f(x)\bigr) + h_f(\log(N+k))\Bigr)\,dx
  \;\ge\; \sum_{k=0}^{N-1} \int_0^{\log(N+k+1) - \log(N+k)} \left(\Bigl(1 - \frac{1}{2 W_0}\Bigr) h_f(0) - W_0\bigl(h_f(0) - h_f(y)\bigr)\right) dy.$$ -/
theorem sum_integral_signed_nyquist_collar_ge {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {W₀ : ℝ} (hW₀ : 0 < W₀) (N : ℕ) :
    ∑ k ∈ Finset.range N,
        (∫ y in (0 : ℝ)..(Real.log ((N + k + 1 : ℕ) : ℝ) - Real.log ((N + k : ℕ) : ℝ)),
          ((1 - 1 / (2 * W₀)) * autocorr f 0 - W₀ * (autocorr f 0 - autocorr f y))) ≤
      ∑ k ∈ Finset.range N,
        (∫ x in Real.log ((N + k : ℕ) : ℝ)..Real.log ((N + k + 1 : ℕ) : ℝ),
          ((autocorr f 0 - autocorr f x) + autocorr f (Real.log ((N + k : ℕ) : ℝ)))) := by
  have hcont_ac : Continuous (autocorr f) := continuous_autocorr hf hfc
  refine Finset.sum_le_sum fun k _ => ?_
  set tk : ℝ := Real.log ((N + k : ℕ) : ℝ)
  set δk : ℝ := Real.log ((N + k + 1 : ℕ) : ℝ) - tk
  have hshift :
      (∫ x in tk..Real.log ((N + k + 1 : ℕ) : ℝ),
          ((autocorr f 0 - autocorr f x) + autocorr f tk)) =
        ∫ y in (0 : ℝ)..δk,
          ((autocorr f 0 - autocorr f (tk + y)) + autocorr f tk) := by
    have hcomp := intervalIntegral_collar_shift
      (fun x : ℝ => (autocorr f 0 - autocorr f x) + autocorr f tk) tk δk
    have h1 : tk + δk = Real.log ((N + k + 1 : ℕ) : ℝ) := add_sub_cancel _ _
    rw [h1] at hcomp
    exact hcomp.symm
  rw [hshift]
  have hδk_nn : 0 ≤ δk := by
    dsimp [δk, tk]
    by_cases hNk : 1 ≤ N + k
    · exact le_of_lt (log_succ_sub_log_pos hNk)
    · have h0 : N + k = 0 := by omega
      simp [h0]
  have hint_lhs : IntervalIntegrable
      (fun y : ℝ => (1 - 1 / (2 * W₀)) * autocorr f 0 - W₀ * (autocorr f 0 - autocorr f y))
      volume 0 δk :=
    (continuous_const.sub (continuous_const.mul (continuous_const.sub hcont_ac))).intervalIntegrable 0 δk
  have hint_rhs : IntervalIntegrable
      (fun y : ℝ => (autocorr f 0 - autocorr f (tk + y)) + autocorr f tk)
      volume 0 δk :=
    ((continuous_const.sub (hcont_ac.comp (continuous_const.add continuous_id))).add
      continuous_const).intervalIntegrable 0 δk
  refine intervalIntegral.integral_mono_on hδk_nn hint_lhs hint_rhs fun y _ => ?_
  have hlev := autocorr_signed_collar_origin_leverage_add hfc hf.continuous hW₀ zero_le_one tk y
  linarith

/-! ## §4. Exact Critical-Line `2 / √n` Scaling Law of `archLevySinhWeight (log n)` -/

/-- For any positive real `x > 0`, `sinh(log x) = (x - x⁻¹) / 2 = (x² - 1) / (2 x)`. -/
theorem sinh_log_eq {x : ℝ} (hx : 0 < x) :
    Real.sinh (Real.log x) = (x ^ 2 - 1) / (2 * x) := by
  rw [Real.sinh_eq, Real.exp_log hx, Real.exp_neg, Real.exp_log hx]
  have hx_ne : x ≠ 0 := ne_of_gt hx
  field_simp [hx_ne]

/-- For any positive real `x > 0`, `exp((log x) / 2) = √x`. -/
theorem exp_half_log_eq_sqrt {x : ℝ} (hx : 0 < x) :
    Real.exp (Real.log x / 2) = Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  ring_nf

/-- **Exact Algebraic Formula for `archLevySinhWeight (log n)` (`n ≥ 2`):**
At every logarithmic grid node `log n` (`n ≥ 2`), the archimedean Lévy weight is
$$\operatorname{archLevySinhWeight}(\log n) = \frac{2\sqrt{n}\, n}{n^2 - 1} = \frac{2}{\sqrt{n}} + \frac{2}{\sqrt{n}(n^2 - 1)}.$$ -/
theorem archLevySinhWeight_log_nat_eq {n : ℕ} (hn : 2 ≤ n) :
    archLevySinhWeight (Real.log (n : ℝ)) =
      2 / Real.sqrt (n : ℝ) + 2 / (Real.sqrt (n : ℝ) * ((n : ℝ) ^ 2 - 1)) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  unfold archLevySinhWeight
  rw [exp_half_log_eq_sqrt hn_pos, sinh_log_eq hn_pos]
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hsqrt_ne : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt hsqrt_pos
  have hn_sq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn_pos)
  have hn2_sub_pos : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hn2_sub_ne : (n : ℝ) ^ 2 - 1 ≠ 0 := ne_of_gt hn2_sub_pos
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  field_simp [hsqrt_ne, hn2_sub_ne, hn_ne]
  nlinarith [hn_sq]

/-- **Critical-Line Lower Bound for `archLevySinhWeight (log n)` (`n ≥ 2`):**
At every logarithmic grid node `log n` (`n ≥ 2`),
$$\frac{2}{\sqrt{n}} \;\le\; \operatorname{archLevySinhWeight}(\log n).$$ -/
theorem archLevySinhWeight_log_nat_ge_two_div_sqrt {n : ℕ} (hn : 2 ≤ n) :
    2 / Real.sqrt (n : ℝ) ≤ archLevySinhWeight (Real.log (n : ℝ)) := by
  rw [archLevySinhWeight_log_nat_eq hn]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hn_gt_one : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hn2_sub_pos : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hrem_pos : 0 ≤ 2 / (Real.sqrt (n : ℝ) * ((n : ℝ) ^ 2 - 1)) := by positivity
  linarith

/-- **Subleading `O(n^{-5/2})` Remainder Bound for `archLevySinhWeight (log n) - 2 / √n`:**
For every integer `n ≥ 2`, since `n² - 1 ≥ (3/4) n²`,
$$\operatorname{archLevySinhWeight}(\log n) - \frac{2}{\sqrt{n}} \;\le\; \frac{8}{3\,\sqrt{n}\,n^2}.$$ -/
theorem archLevySinhWeight_log_nat_sub_two_div_sqrt_le {n : ℕ} (hn : 2 ≤ n) :
    archLevySinhWeight (Real.log (n : ℝ)) - 2 / Real.sqrt (n : ℝ) ≤
      8 / (3 * Real.sqrt (n : ℝ) * (n : ℝ) ^ 2) := by
  have heq := archLevySinhWeight_log_nat_eq hn
  have hn_ge2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by linarith
  have hsqrt_pos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn_pos
  have hn2_bound : 3 / 4 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 - 1 := by nlinarith
  have hdenom_pos : 0 < Real.sqrt (n : ℝ) * (3 / 4 * (n : ℝ) ^ 2) := by positivity
  have hdenom_le :
      Real.sqrt (n : ℝ) * (3 / 4 * (n : ℝ) ^ 2) ≤ Real.sqrt (n : ℝ) * ((n : ℝ) ^ 2 - 1) :=
    mul_le_mul_of_nonneg_left hn2_bound (le_of_lt hsqrt_pos)
  have hdiv :
      2 / (Real.sqrt (n : ℝ) * ((n : ℝ) ^ 2 - 1)) ≤
        2 / (Real.sqrt (n : ℝ) * (3 / 4 * (n : ℝ) ^ 2)) :=
    div_le_div_of_nonneg_left (by positivity) hdenom_pos hdenom_le
  have hsimp :
      2 / (Real.sqrt (n : ℝ) * (3 / 4 * (n : ℝ) ^ 2)) =
        8 / (3 * Real.sqrt (n : ℝ) * (n : ℝ) ^ 2) := by
    ring
  linarith

end ConcreteSignedAutocorr

end

end GaloisForLFunctions.BiScaleUncertainty
