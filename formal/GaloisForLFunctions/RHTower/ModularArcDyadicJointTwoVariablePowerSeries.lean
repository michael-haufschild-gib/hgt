import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import GaloisForLFunctions.RHTower.ModularArcDyadicOscillatoryMellinPowerSeries

/-!
# Joint Two-Variable `(l, τ)` Power Series, Vertical Taylor Curvature, and Fourth-Order Cauchy–Riemann Saddle-Point Cancellation

In `ModularArcDyadicOscillatoryMellinPowerSeries` (Cycle 48), we established the horizontal
(`l`-direction, around `l = 0`) Taylor expansion and power-series convergence of the two-variable
oscillatory Mellin transform
$$M_k(l, \tau) = \int_0^\infty x^{l - 1/2} \cos(\tau \log x)\,V_k(x)\,dx
  = \int_{\mathbb{R}} \cosh(lv) \cos(\tau v)\,\Phi_k(v)\,dv$$
and its origin–infinity imbalance
$$\Delta_k^{\mathrm{Mellin}}(l, \tau)
  = \int_1^\infty x^{l - 1/2} \cos(\tau \log x)\,V_k(x)\,dx
    - \int_0^1 x^{l - 1/2} \cos(\tau \log x)\,V_k(x)\,dx
  = \int_0^\infty 2\sinh(lv) \cos(\tau v)\,\Phi_k(v)\,dv.$$

In this module we complete the **vertical (`τ`-direction) and joint two-variable `(l, τ)`
real-analytic power-series theory** around the central symmetry point `(l, τ) = (0, 0)` (`s = 1/2`):

1. **Elementary Alternating Taylor Remainder Bounds & Joint Two-Variable Kernel Envelopes (`Section 1`):**
   - Modulus domination of the alternating `cos` and `sin` Taylor remainders by the positive `cosh`
     and `sinh` Taylor remainders (`abs_cos_sub_sum_range_le_cosh_sub_sum`,
     `abs_sin_sub_sum_range_le_sinh_abs_sub_sum`) and explicit factorial-exponential bounds
     (`abs_cos_sub_sum_range_even_pow_div_factorial_le`,
     `abs_sin_sub_sum_range_odd_pow_div_factorial_le`).
   - Pointwise additive decomposition of the joint two-variable `(M, J)` Taylor remainder for
     `cosh(lv) cos(τv)` and `sinh(lv) cos(τv)` (`abs_cosh_mul_cos_sub_double_sum_range_le`,
     `abs_sinh_mul_cos_sub_double_sum_range_le`) and joint profile remainder envelope
     (`joint_taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le`).

2. **Vertical (`τ`-Direction) Taylor Expansion, Stationarity, and Curvature (`Section 2`):**
   - Scale-independent geometric `O((8|τ|)^{2J} / (1/8 − |l| − |τ|))` vertical Taylor remainder
     bound and `J → ∞` power-series convergence across `|l| + |τ| < 1/8`
     (`abs_oscillatoryMellin_sub_sum_range_vertical_even_le`,
     `tendsto_sum_range_vertical_even_pow_div_factorial_atTop`).
   - Quadratic `O(τ²)` vertical stationary bound (`abs_oscillatoryMellin_sub_realAxis_le_sq`),
     vanishing first-order vertical derivative `(M_k(l, τ) − M_k(l, 0)) / τ → 0` as `τ → 0`
     (`tendsto_div_oscillatoryMellin_sub_realAxis_nhds_zero`), quartic `O(τ⁴)` second-order
     vertical Taylor remainder (`abs_oscillatoryMellin_sub_realAxis_add_quadratic_le_pow_four`),
     and exact second-order vertical curvature limit
     `(M_k(l, τ) − M_k(l, 0)) / τ² → −(1/2) ∫_ℝ v² cosh(lv) Φ_k(v) dv` as `τ → 0` (`τ ≠ 0`)
     (`tendsto_div_sq_oscillatoryMellin_sub_realAxis_nhds_zero`).

3. **Fourth-Order `O(h⁴)` Cauchy–Riemann Harmonic Saddle-Point Cancellation at `s = 1/2` (`Section 3`):**
   - At the central point `(l, τ) = (0, 0)` (`s = 1/2`), the positive horizontal curvature
     `+(1/2) ∫_ℝ v² Φ_k(v) dv` and negative vertical curvature `−(1/2) ∫_ℝ v² Φ_k(v) dv` cancel
     to **fourth order `O(h⁴)`**:
     `|(M_k(h, 0) − M_k(0, 0)) + (M_k(0, h) − M_k(0, 0))| ≤ (13516800 · ν.real univ / (1/8 − |h|)) · h⁴`
     (`abs_oscillatoryMellin_harmonic_laplacian_defect_le_pow_four`), and
     `((M_k(h, 0) − M_k(0, 0)) + (M_k(0, h) − M_k(0, 0))) / h² → 0` as `h → 0`
     (`tendsto_div_sq_oscillatoryMellin_harmonic_laplacian_defect_nhds_zero`).

4. **Joint Two-Variable `(l, τ)` Taylor Polynomials & Diagonal Power-Series Convergence (`Section 4`):**
   - Every joint `(l, τ)` Taylor coefficient of `M_k(l, τ)` around `(0, 0)` reduces to the pure
     critical-line zero-frequency even logarithmic moments `∫_ℝ v^{2m+2j} Φ_k(v) dv`, with
     scale-independent additive remainder bound
     `|M_k(l, τ) − P_{M, J}(l, τ)| ≤ (1650 · ν.real univ / (1/8 − |l| − |τ|)) · ((8|l|)^{2M} + (8|τ|)^{2J})`
     (`abs_oscillatoryMellin_sub_double_sum_range_even_le`) and unconditional `N → ∞` diagonal
     power-series convergence (`tendsto_double_sum_range_even_pow_div_factorial_atTop`).
   - Every joint `(l, τ)` Taylor coefficient of `Δ_k^{\mathrm{Mellin}}(l, τ)` around `(0, 0)`
     reduces to the half-line odd real logarithmic moments `2 ∫_{v > 0} v^{2m+1+2j} Φ_k(v) dv`,
     with scale-independent additive remainder bound
     `|Δ_k^{\mathrm{Mellin}}(l, τ) − Q_{M, J}(l, τ)| ≤ (3300 · ν.real univ / (1/8 − |l| − |τ|)) · ((8|l|)^{2M+1} + (8|τ|)^{2J})`
     (`abs_oscillatoryMellin_imbalance_sub_two_mul_double_sum_range_odd_even_le`), unconditional
     `N → ∞` diagonal power-series convergence
     (`tendsto_two_mul_double_sum_range_odd_even_pow_div_factorial_atTop`), and master witness
     theorem (`exists_dyadic_jointTwoVariable_powerSeries_arcWitness`).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ## Section 1: Alternating Taylor Remainder Bounds & Joint Two-Variable Kernel Envelopes -/

/-- **Modulus domination of the alternating `Real.cos` Taylor remainder by the `Real.cosh`
Taylor remainder:**
For every `J ∈ ℕ` and `u ∈ ℝ`,
`|cos u − ∑_{j < J} (−1)^j u^{2j} / (2j)!| ≤ cosh u − ∑_{j < J} u^{2j} / (2j)!`. -/
theorem abs_cos_sub_sum_range_le_cosh_sub_sum (J : ℕ) (u : ℝ) :
    |Real.cos u -
        ∑ j ∈ Finset.range J, (-1 : ℝ) ^ j * u ^ (2 * j) / ((2 * j).factorial : ℝ)| ≤
      Real.cosh u -
        ∑ j ∈ Finset.range J, u ^ (2 * j) / ((2 * j).factorial : ℝ) := by
  have hs_cos : Summable (fun j : ℕ => (-1 : ℝ) ^ j * u ^ (2 * j) / ((2 * j).factorial : ℝ)) :=
    (Real.hasSum_cos u).summable
  have hsum_cos :
      (∑' j : ℕ, (-1 : ℝ) ^ j * u ^ (2 * j) / ((2 * j).factorial : ℝ)) = Real.cos u :=
    (Real.hasSum_cos u).tsum_eq
  have hsplit_cos := hs_cos.sum_add_tsum_nat_add J
  have htail_cos :
      Real.cos u -
          ∑ j ∈ Finset.range J, (-1 : ℝ) ^ j * u ^ (2 * j) / ((2 * j).factorial : ℝ) =
        ∑' k : ℕ,
          (-1 : ℝ) ^ (k + J) * u ^ (2 * (k + J)) / ((2 * (k + J)).factorial : ℝ) := by
    rw [← hsum_cos]; linarith
  have hs_cosh : Summable (fun j : ℕ => u ^ (2 * j) / ((2 * j).factorial : ℝ)) :=
    (Real.hasSum_cosh u).summable
  have hsum_cosh :
      (∑' j : ℕ, u ^ (2 * j) / ((2 * j).factorial : ℝ)) = Real.cosh u :=
    (Real.hasSum_cosh u).tsum_eq
  have hsplit_cosh := hs_cosh.sum_add_tsum_nat_add J
  have htail_cosh :
      Real.cosh u - ∑ j ∈ Finset.range J, u ^ (2 * j) / ((2 * j).factorial : ℝ) =
        ∑' k : ℕ, u ^ (2 * (k + J)) / ((2 * (k + J)).factorial : ℝ) := by
    rw [← hsum_cosh]; linarith
  rw [htail_cos, htail_cosh, ← Real.norm_eq_abs]
  have hnorm_eq : ∀ k : ℕ,
      ‖(-1 : ℝ) ^ (k + J) * u ^ (2 * (k + J)) / ((2 * (k + J)).factorial : ℝ)‖ =
        u ^ (2 * (k + J)) / ((2 * (k + J)).factorial : ℝ) := by
    intro k
    have hfac0 : (0 : ℝ) ≤ ((2 * (k + J)).factorial : ℝ) := Nat.cast_nonneg _
    have hev : |u| ^ (2 * (k + J)) = u ^ (2 * (k + J)) := by
      rw [pow_mul, pow_mul, sq_abs]
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_pow, hev, abs_of_nonneg hfac0]
  have hnorm_sum : Summable (fun k : ℕ =>
      ‖(-1 : ℝ) ^ (k + J) * u ^ (2 * (k + J)) / ((2 * (k + J)).factorial : ℝ)‖) :=
    ((summable_nat_add_iff J).2 hs_cosh).congr (fun k => (hnorm_eq k).symm)
  exact (norm_tsum_le_tsum_norm hnorm_sum).trans_eq (tsum_congr hnorm_eq)

/-- **Factorial-exponential Taylor remainder bound for `Real.cos`:**
For every `J ∈ ℕ` and `u ∈ ℝ`,
`|cos u − ∑_{j < J} (−1)^j u^{2j} / (2j)!| ≤ (u^{2J} / (2J)!) · exp |u|`. -/
theorem abs_cos_sub_sum_range_even_pow_div_factorial_le (J : ℕ) (u : ℝ) :
    |Real.cos u -
        ∑ j ∈ Finset.range J, (-1 : ℝ) ^ j * u ^ (2 * j) / ((2 * j).factorial : ℝ)| ≤
      (u ^ (2 * J) / ((2 * J).factorial : ℝ)) * Real.exp |u| :=
  (abs_cos_sub_sum_range_le_cosh_sub_sum J u).trans
    (cosh_sub_sum_range_even_pow_div_factorial_le J u)

/-- **Modulus domination of the alternating `Real.sin` Taylor remainder by the `Real.sinh |u|`
Taylor remainder:**
For every `J ∈ ℕ` and `u ∈ ℝ`,
`|sin u − ∑_{j < J} (−1)^j u^{2j+1} / (2j+1)!| ≤ sinh |u| − ∑_{j < J} |u|^{2j+1} / (2j+1)!`. -/
theorem abs_sin_sub_sum_range_le_sinh_abs_sub_sum (J : ℕ) (u : ℝ) :
    |Real.sin u -
        ∑ j ∈ Finset.range J,
          (-1 : ℝ) ^ j * u ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)| ≤
      Real.sinh |u| -
        ∑ j ∈ Finset.range J, |u| ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) := by
  have hs_sin : Summable (fun j : ℕ =>
      (-1 : ℝ) ^ j * u ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) :=
    (Real.hasSum_sin u).summable
  have hsum_sin :
      (∑' j : ℕ, (-1 : ℝ) ^ j * u ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) = Real.sin u :=
    (Real.hasSum_sin u).tsum_eq
  have hsplit_sin := hs_sin.sum_add_tsum_nat_add J
  have htail_sin :
      Real.sin u -
          ∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * u ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) =
        ∑' k : ℕ,
          (-1 : ℝ) ^ (k + J) * u ^ (2 * (k + J) + 1) /
            ((2 * (k + J) + 1).factorial : ℝ) := by
    rw [← hsum_sin]; linarith
  have hs_sinh : Summable (fun j : ℕ => |u| ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) :=
    (Real.hasSum_sinh |u|).summable
  have hsum_sinh :
      (∑' j : ℕ, |u| ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) = Real.sinh |u| :=
    (Real.hasSum_sinh |u|).tsum_eq
  have hsplit_sinh := hs_sinh.sum_add_tsum_nat_add J
  have htail_sinh :
      Real.sinh |u| -
          ∑ j ∈ Finset.range J, |u| ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) =
        ∑' k : ℕ, |u| ^ (2 * (k + J) + 1) / ((2 * (k + J) + 1).factorial : ℝ) := by
    rw [← hsum_sinh]; linarith
  rw [htail_sin, htail_sinh, ← Real.norm_eq_abs]
  have hnorm_eq : ∀ k : ℕ,
      ‖(-1 : ℝ) ^ (k + J) * u ^ (2 * (k + J) + 1) /
          ((2 * (k + J) + 1).factorial : ℝ)‖ =
        |u| ^ (2 * (k + J) + 1) / ((2 * (k + J) + 1).factorial : ℝ) := by
    intro k
    have hfac0 : (0 : ℝ) ≤ ((2 * (k + J) + 1).factorial : ℝ) := Nat.cast_nonneg _
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_pow, abs_of_nonneg hfac0]
  have hnorm_sum : Summable (fun k : ℕ =>
      ‖(-1 : ℝ) ^ (k + J) * u ^ (2 * (k + J) + 1) /
          ((2 * (k + J) + 1).factorial : ℝ)‖) :=
    ((summable_nat_add_iff J).2 hs_sinh).congr (fun k => (hnorm_eq k).symm)
  exact (norm_tsum_le_tsum_norm hnorm_sum).trans_eq (tsum_congr hnorm_eq)

/-- **Factorial-exponential Taylor remainder bound for `Real.sin`:**
For every `J ∈ ℕ` and `u ∈ ℝ`,
`|sin u − ∑_{j < J} (−1)^j u^{2j+1} / (2j+1)!| ≤ (|u|^{2J+1} / (2J+1)!) · exp |u|`. -/
theorem abs_sin_sub_sum_range_odd_pow_div_factorial_le (J : ℕ) (u : ℝ) :
    |Real.sin u -
        ∑ j ∈ Finset.range J,
          (-1 : ℝ) ^ j * u ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)| ≤
      (|u| ^ (2 * J + 1) / ((2 * J + 1).factorial : ℝ)) * Real.exp |u| := by
  have h1 := abs_sin_sub_sum_range_le_sinh_abs_sub_sum J u
  have hnonneg :
      0 ≤ Real.sinh |u| -
        ∑ j ∈ Finset.range J, |u| ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ) :=
    sub_nonneg.mpr (sum_range_odd_pow_div_factorial_le_sinh_nonneg J (abs_nonneg u))
  have h2 := abs_sinh_sub_sum_range_odd_pow_div_factorial_le J |u|
  rw [abs_of_nonneg hnonneg, abs_abs] at h2
  exact h1.trans h2

/-- Elementary hyperbolic cosine envelope `cosh u ≤ exp |u|` for all `u ∈ ℝ`. -/
theorem cosh_le_exp_abs (u : ℝ) : Real.cosh u ≤ Real.exp |u| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have h1 : Real.exp (-|u|) ≤ Real.exp |u| :=
    Real.exp_le_exp.mpr (by linarith [abs_nonneg u])
  linarith

/-- **Pointwise additive joint Taylor remainder bound for `cosh(lv) cos(τv)`:**
For every `M, J ∈ ℕ` and `l, τ, v ∈ ℝ`,
`|cosh(lv) cos(τv) −
    (∑_{m < M} (lv)^{2m} / (2m)!) · (∑_{j < J} (−1)^j (τv)^{2j} / (2j)!)| ≤
  ((|l| |v|)^{2M} / (2M)! + (|τ| |v|)^{2J} / (2J)!) · exp((|l| + |τ|) |v|)`. -/
theorem abs_cosh_mul_cos_sub_double_sum_range_le (M J : ℕ) (l τ v : ℝ) :
    |Real.cosh (l * v) * Real.cos (τ * v) -
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ))| ≤
      ((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ) +
        (|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
        Real.exp ((|l| + |τ|) * |v|) := by
  set S_M := ∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)
  set S_J := ∑ j ∈ Finset.range J,
    (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)
  have hsplit :
      Real.cosh (l * v) * Real.cos (τ * v) - S_M * S_J =
        (Real.cosh (l * v) - S_M) * Real.cos (τ * v) +
          S_M * (Real.cos (τ * v) - S_J) := by ring
  have hSM_nonneg : 0 ≤ S_M := by
    dsimp [S_M]
    refine Finset.sum_nonneg (fun m _ => ?_)
    have hev : 0 ≤ (l * v) ^ (2 * m) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) m
    positivity
  have hSM_le_cosh : S_M ≤ Real.cosh (l * v) :=
    sum_range_even_pow_div_factorial_le_cosh M (l * v)
  have hcosh_le_exp : Real.cosh (l * v) ≤ Real.exp (|l| * |v|) := by
    rw [← abs_mul]
    exact cosh_le_exp_abs (l * v)
  have hSM_le_exp : S_M ≤ Real.exp (|l| * |v|) := hSM_le_cosh.trans hcosh_le_exp
  have hrem_cosh :
      Real.cosh (l * v) - S_M ≤
        ((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ)) * Real.exp (|l| * |v|) := by
    have h := cosh_sub_sum_range_even_pow_div_factorial_le M (l * v)
    have habs : |l * v| = |l| * |v| := abs_mul l v
    have hev : (l * v) ^ (2 * M) = (|l| * |v|) ^ (2 * M) := by
      rw [← habs, pow_mul, pow_mul, sq_abs]
    rwa [hev, habs] at h
  have hrem_cos :
      |Real.cos (τ * v) - S_J| ≤
        ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) * Real.exp (|τ| * |v|) := by
    have h := abs_cos_sub_sum_range_even_pow_div_factorial_le J (τ * v)
    have habs : |τ * v| = |τ| * |v| := abs_mul τ v
    have hev : (τ * v) ^ (2 * J) = (|τ| * |v|) ^ (2 * J) := by
      rw [← habs, pow_mul, pow_mul, sq_abs]
    rwa [hev, habs] at h
  have hterm1 :
      |(Real.cosh (l * v) - S_M) * Real.cos (τ * v)| ≤
        ((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ)) *
          Real.exp ((|l| + |τ|) * |v|) := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hSM_le_cosh)]
    have hcos_le_exp : |Real.cos (τ * v)| ≤ Real.exp (|τ| * |v|) :=
      (Real.abs_cos_le_one _).trans (Real.one_le_exp (by positivity))
    calc (Real.cosh (l * v) - S_M) * |Real.cos (τ * v)|
        ≤ (((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ)) * Real.exp (|l| * |v|)) *
            Real.exp (|τ| * |v|) :=
          mul_le_mul hrem_cosh hcos_le_exp (abs_nonneg _) (by positivity)
      _ = ((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ)) *
            (Real.exp (|l| * |v|) * Real.exp (|τ| * |v|)) := by ring
      _ = ((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|) := by
          rw [← Real.exp_add]; congr 2; ring
  have hterm2 :
      |S_M * (Real.cos (τ * v) - S_J)| ≤
        ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
          Real.exp ((|l| + |τ|) * |v|) := by
    rw [abs_mul, abs_of_nonneg hSM_nonneg]
    calc S_M * |Real.cos (τ * v) - S_J|
        ≤ Real.exp (|l| * |v|) *
            (((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) * Real.exp (|τ| * |v|)) :=
          mul_le_mul hSM_le_exp hrem_cos (abs_nonneg _) (Real.exp_nonneg _)
      _ = ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
            (Real.exp (|l| * |v|) * Real.exp (|τ| * |v|)) := by ring
      _ = ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|) := by
          rw [← Real.exp_add]; congr 2; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  calc |(Real.cosh (l * v) - S_M) * Real.cos (τ * v)| + |S_M * (Real.cos (τ * v) - S_J)|
      ≤ ((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ)) * Real.exp ((|l| + |τ|) * |v|) +
          ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) * Real.exp ((|l| + |τ|) * |v|) :=
        add_le_add hterm1 hterm2
    _ = ((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ) +
          (|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
          Real.exp ((|l| + |τ|) * |v|) := by ring

/-- **Pointwise additive joint Taylor remainder bound for `sinh(lv) cos(τv)`:**
For every `M, J ∈ ℕ` and `l, τ, v ∈ ℝ`,
`|sinh(lv) cos(τv) −
    (∑_{m < M} (lv)^{2m+1} / (2m+1)!) · (∑_{j < J} (−1)^j (τv)^{2j} / (2j)!)| ≤
  ((|l| |v|)^{2M+1} / (2M+1)! + (|τ| |v|)^{2J} / (2J)!) · exp((|l| + |τ|) |v|)`. -/
theorem abs_sinh_mul_cos_sub_double_sum_range_le (M J : ℕ) (l τ v : ℝ) :
    |Real.sinh (l * v) * Real.cos (τ * v) -
        (∑ m ∈ Finset.range M,
            (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ))| ≤
      ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) +
        (|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
        Real.exp ((|l| + |τ|) * |v|) := by
  set S_M := ∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)
  set S_J := ∑ j ∈ Finset.range J,
    (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)
  have hsplit :
      Real.sinh (l * v) * Real.cos (τ * v) - S_M * S_J =
        (Real.sinh (l * v) - S_M) * Real.cos (τ * v) +
          S_M * (Real.cos (τ * v) - S_J) := by ring
  have habs_lv : |l * v| = |l| * |v| := abs_mul l v
  have hSM_abs_le :
      |S_M| ≤ ∑ m ∈ Finset.range M,
        (|l| * |v|) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have hfac0 : (0 : ℝ) ≤ ((2 * m + 1).factorial : ℝ) := Nat.cast_nonneg _
    rw [abs_div, abs_pow, habs_lv, abs_of_nonneg hfac0]
  have hsinh_le_exp : Real.sinh (|l| * |v|) ≤ Real.exp (|l| * |v|) := by
    rw [Real.sinh_eq]
    have := Real.exp_pos (|l| * |v|)
    have := Real.exp_pos (-(|l| * |v|))
    linarith
  have hSM_le_exp : |S_M| ≤ Real.exp (|l| * |v|) :=
    (hSM_abs_le.trans (sum_range_odd_pow_div_factorial_le_sinh_nonneg M (by positivity))).trans
      hsinh_le_exp
  have hrem_sinh :
      |Real.sinh (l * v) - S_M| ≤
        ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) * Real.exp (|l| * |v|) := by
    have h := abs_sinh_sub_sum_range_odd_pow_div_factorial_le M (l * v)
    rwa [habs_lv] at h
  have hrem_cos :
      |Real.cos (τ * v) - S_J| ≤
        ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) * Real.exp (|τ| * |v|) := by
    have h := abs_cos_sub_sum_range_even_pow_div_factorial_le J (τ * v)
    have habs : |τ * v| = |τ| * |v| := abs_mul τ v
    have hev : (τ * v) ^ (2 * J) = (|τ| * |v|) ^ (2 * J) := by
      rw [← habs, pow_mul, pow_mul, sq_abs]
    rwa [hev, habs] at h
  have hterm1 :
      |(Real.sinh (l * v) - S_M) * Real.cos (τ * v)| ≤
        ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) *
          Real.exp ((|l| + |τ|) * |v|) := by
    rw [abs_mul]
    have hcos_le_exp : |Real.cos (τ * v)| ≤ Real.exp (|τ| * |v|) :=
      (Real.abs_cos_le_one _).trans (Real.one_le_exp (by positivity))
    calc |Real.sinh (l * v) - S_M| * |Real.cos (τ * v)|
        ≤ (((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) *
            Real.exp (|l| * |v|)) * Real.exp (|τ| * |v|) :=
          mul_le_mul hrem_sinh hcos_le_exp (abs_nonneg _) (by positivity)
      _ = ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) *
            (Real.exp (|l| * |v|) * Real.exp (|τ| * |v|)) := by ring
      _ = ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|) := by
          rw [← Real.exp_add]; congr 2; ring
  have hterm2 :
      |S_M * (Real.cos (τ * v) - S_J)| ≤
        ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
          Real.exp ((|l| + |τ|) * |v|) := by
    rw [abs_mul]
    calc |S_M| * |Real.cos (τ * v) - S_J|
        ≤ Real.exp (|l| * |v|) *
            (((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) * Real.exp (|τ| * |v|)) :=
          mul_le_mul hSM_le_exp hrem_cos (abs_nonneg _) (Real.exp_nonneg _)
      _ = ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
            (Real.exp (|l| * |v|) * Real.exp (|τ| * |v|)) := by ring
      _ = ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|) := by
          rw [← Real.exp_add]; congr 2; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  calc |(Real.sinh (l * v) - S_M) * Real.cos (τ * v)| + |S_M * (Real.cos (τ * v) - S_J)|
      ≤ ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) *
          Real.exp ((|l| + |τ|) * |v|) +
        ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
          Real.exp ((|l| + |τ|) * |v|) :=
        add_le_add hterm1 hterm2
    _ = ((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) +
          (|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
          Real.exp ((|l| + |τ|) * |v|) := by ring

/-- **Joint two-variable Taylor remainder envelope for `Φ_k` (`k ≥ 2`, `N ∈ ℕ`, `u, l, τ, v ∈ ℝ`):**
`((|u| * |v|) ^ N / N!) * exp((|l| + |τ|) * |v|) * |Φ_k(v)| ≤
  825 * ν.real univ * (8 * |u|) ^ N * exp(−((1/8 − |l| − |τ|) * |v|))`. -/
theorem joint_taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (N : ℕ) (u l τ v : ℝ) :
    ((|u| * |v|) ^ N / (N.factorial : ℝ)) * Real.exp ((|l| + |τ|) * |v|) *
        |arcLineInfiniteDyadicProfile k ν v| ≤
      825 * ν.real univ * (8 * |u|) ^ N *
        Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) := by
  have h1 := abs_mul_pow_div_factorial_le_eight_pow_mul_exp_eighth N u v
  have h2 := abs_arcLineInfiniteDyadicProfile_le_exp_quarter_uniform hk hν v
  have h1_exp :
      ((|u| * |v|) ^ N / (N.factorial : ℝ)) * Real.exp ((|l| + |τ|) * |v|) ≤
        (8 * |u|) ^ N * Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp ((|l| + |τ|) * |v|) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_nonneg _)
  have hprod := mul_le_mul h1_exp h2 (abs_nonneg _) (by positivity)
  refine hprod.trans_eq ?_
  have hexp :
      Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp ((|l| + |τ|) * |v|) *
          Real.exp (-((1 / 4 : ℝ) * |v|)) =
        Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc (8 * |u|) ^ N * Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp ((|l| + |τ|) * |v|) *
          (825 * ν.real univ * Real.exp (-((1 / 4 : ℝ) * |v|)))
      = 825 * ν.real univ * (8 * |u|) ^ N *
          (Real.exp ((1 / 8 : ℝ) * |v|) * Real.exp ((|l| + |τ|) * |v|) *
            Real.exp (-((1 / 4 : ℝ) * |v|))) := by ring
    _ = 825 * ν.real univ * (8 * |u|) ^ N *
          Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) := by rw [hexp]


/-! ## Section 2: Vertical (`τ`-Direction) Taylor Expansion, Stationarity, and Curvature -/

/-- **All-orders integrability of `v ↦ v^n cosh(lv) Φ_k(v)` on `ℝ` across `|l| < 1/8` (`k ≥ 2`, `n ∈ ℕ`).** -/
theorem integrable_pow_mul_cosh_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (n : ℕ) :
    Integrable (fun v : ℝ => v ^ n * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have hc : 0 < 1 / 8 - |l| := sub_pos.mpr hl
  set B := 825 * ν.real univ * (n.factorial : ℝ) * 8 ^ n
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  refine hdom.mono'
    (((continuous_id.pow n).mul
      (Real.continuous_cosh.comp (continuous_const.mul continuous_id))).mul
      (continuous_arcLineInfiniteDyadicProfile hk ν)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.cosh_pos _)]
  have hcosh : Real.cosh (l * v) ≤ Real.exp (|l| * |v|) := by
    rw [← abs_mul]; exact cosh_le_exp_abs (l * v)
  have h1 := abs_pow_mul_abs_arcLineInfiniteDyadicProfile_le_factorial_mul_exp_eighth hk hν n v
  calc |v| ^ n * Real.cosh (l * v) * |arcLineInfiniteDyadicProfile k ν v|
      = Real.cosh (l * v) * (|v| ^ n * |arcLineInfiniteDyadicProfile k ν v|) := by ring
    _ ≤ Real.exp (|l| * |v|) * (B * Real.exp (-((1 / 8 : ℝ) * |v|))) :=
        mul_le_mul hcosh h1 (by positivity) (Real.exp_nonneg _)
    _ = B * (Real.exp (|l| * |v|) * Real.exp (-((1 / 8 : ℝ) * |v|))) := by ring
    _ = B * Real.exp (-((1 / 8 - |l|) * |v|)) := by
        rw [← Real.exp_add]; congr 2; ring

/-- **Full-line integral linearity for the `J`-term vertical even Taylor polynomial against
`cosh(lv) Φ_k(v)` (`k ≥ 2`, `|l| < 1/8`):**
`∫_ℝ cosh(lv) (∑_{j < J} (−1)^j (τv)^{2j} / (2j)!) Φ_k(v) dv =
  ∑_{j < J} ((−1)^j τ^{2j} / (2j)!) ∫_ℝ v^{2j} cosh(lv) Φ_k(v) dv`. -/
theorem integral_sum_range_vertical_even_pow_mul_cosh_mul_profile_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) (J : ℕ) :
    (∫ v : ℝ,
        Real.cosh (l * v) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) =
      ∑ j ∈ Finset.range J,
        ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * j) * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v) := by
  have hfun :
      (fun v : ℝ =>
        Real.cosh (l * v) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => ∑ j ∈ Finset.range J,
        ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          (v ^ (2 * j) * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v) := by
    ext v
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_pow]; ring
  rw [hfun, integral_finsetSum]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    exact integral_const_mul _ _
  · intro j _
    exact (integrable_pow_mul_cosh_mul_arcLineInfiniteDyadicProfile hk hν hl (2 * j)).const_mul _

/-- **Scale-independent geometric `O((8|τ|)^{2J} / (1/8 − |l| − |τ|))` vertical Taylor remainder
bound for `M_k(l, τ)` across `|l| + |τ| < 1/8` (`k ≥ 2`, `J ∈ ℕ`):**
`|(∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) −
    ∑_{j < J} ((−1)^j τ^{2j} / (2j)!) ∫_ℝ v^{2j} cosh(lv) Φ_k(v) dv| ≤
  (1650 · ν.real univ / (1/8 − |l| − |τ|)) · (8|τ|)^{2J}`. -/
theorem abs_oscillatoryMellin_sub_sum_range_vertical_even_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l τ : ℝ} (hlτ : |l| + |τ| < 1 / 8) (J : ℕ) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∑ j ∈ Finset.range J,
        ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * j) * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (1650 * ν.real univ / (1 / 8 - |l| - |τ|)) * (8 * |τ|) ^ (2 * J) := by
  have hk1 : 1 ≤ k := by omega
  have hl8 : |l| < 1 / 8 := by linarith [abs_nonneg τ]
  have hl_half : |l| < 1 / 2 := by linarith
  have hc : 0 < 1 / 8 - |l| - |τ| := by linarith
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half τ,
    ← integral_sum_range_vertical_even_pow_mul_cosh_mul_profile_eq hk hν hl8 τ J]
  have hInt_cosh : Integrable
      (fun v : ℝ => Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ
  have hInt_sum : Integrable
      (fun v : ℝ =>
        Real.cosh (l * v) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) := by
    have hfun :
        (fun v : ℝ =>
          Real.cosh (l * v) *
            (∑ j ∈ Finset.range J,
              (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
            arcLineInfiniteDyadicProfile k ν v) =
        fun v : ℝ => ∑ j ∈ Finset.range J,
          ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
            (v ^ (2 * j) * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v) := by
      ext v
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_pow]; ring
    rw [hfun]
    exact integrable_finsetSum _ (fun j _ =>
      (integrable_pow_mul_cosh_mul_arcLineInfiniteDyadicProfile hk hν hl8 (2 * j)).const_mul _)
  rw [← integral_sub hInt_cosh hInt_sum]
  set B := 825 * ν.real univ * (8 * |τ|) ^ (2 * J)
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |τ|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        Real.cosh (l * v) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v)
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              Real.cosh (l * v) *
                (∑ j ∈ Finset.range J,
                  (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
                arcLineInfiniteDyadicProfile k ν v)|
        ≤ B * (2 / (1 / 8 - |l| - |τ|)) := h1
      _ = (1650 * ν.real univ / (1 / 8 - |l| - |τ|)) * (8 * |τ|) ^ (2 * J) := by
          dsimp [B]; ring
  · have hsub :
        Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          Real.cosh (l * v) *
            (∑ j ∈ Finset.range J,
              (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
            arcLineInfiniteDyadicProfile k ν v =
        Real.cosh (l * v) *
          (Real.cos (τ * v) -
            ∑ j ∈ Finset.range J,
              (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v := by ring
    rw [Real.norm_eq_abs, hsub, abs_mul, abs_mul, abs_of_pos (Real.cosh_pos _)]
    have hcosh : Real.cosh (l * v) ≤ Real.exp (|l| * |v|) := by
      rw [← abs_mul]; exact cosh_le_exp_abs (l * v)
    have hrem := abs_cos_sub_sum_range_even_pow_div_factorial_le J (τ * v)
    have habs_τv : |τ * v| = |τ| * |v| := abs_mul τ v
    have hev_τv : (τ * v) ^ (2 * J) = (|τ| * |v|) ^ (2 * J) := by
      rw [← habs_τv, pow_mul, pow_mul, sq_abs]
    rw [hev_τv, habs_τv] at hrem
    have hprod1 :
        Real.cosh (l * v) *
          |Real.cos (τ * v) -
            ∑ j ∈ Finset.range J,
              (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)| ≤
        ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
          Real.exp ((|l| + |τ|) * |v|) := by
      calc Real.cosh (l * v) *
              |Real.cos (τ * v) -
                ∑ j ∈ Finset.range J,
                  (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)|
          ≤ Real.exp (|l| * |v|) *
              (((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) * Real.exp (|τ| * |v|)) :=
            mul_le_mul hcosh hrem (abs_nonneg _) (Real.exp_nonneg _)
        _ = ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
              (Real.exp (|l| * |v|) * Real.exp (|τ| * |v|)) := by ring
        _ = ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
              Real.exp ((|l| + |τ|) * |v|) := by
            rw [← Real.exp_add]; congr 2; ring
    calc Real.cosh (l * v) *
            |Real.cos (τ * v) -
              ∑ j ∈ Finset.range J,
                (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)| *
            |arcLineInfiniteDyadicProfile k ν v|
        ≤ ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|) * |arcLineInfiniteDyadicProfile k ν v| :=
          mul_le_mul_of_nonneg_right hprod1 (abs_nonneg _)
      _ ≤ B * Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) :=
          joint_taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le hk hν (2 * J) τ l τ v

/-- **Unconditional `J → ∞` vertical power-series convergence for `M_k(l, τ)` across
`|l| + |τ| < 1/8` (`k ≥ 2`):**
`∑_{j < J} ((−1)^j τ^{2j} / (2j)!) ∫_ℝ v^{2j} cosh(lv) Φ_k(v) dv →
  ∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx` as `J → ∞`. -/
theorem tendsto_sum_range_vertical_even_pow_div_factorial_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l τ : ℝ} (hlτ : |l| + |τ| < 1 / 8) :
    Tendsto
      (fun J : ℕ =>
        ∑ j ∈ Finset.range J,
          ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
            (∫ v : ℝ, v ^ (2 * j) * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v))
      atTop
      (nhds (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) := by
  have h64_nonneg : 0 ≤ (8 * |τ|) ^ 2 := sq_nonneg _
  have h8τ_lt : 8 * |τ| < 1 := by linarith [abs_nonneg l]
  have h64_lt : (8 * |τ|) ^ 2 < 1 := by nlinarith [abs_nonneg τ]
  have hgeom : Tendsto (fun J : ℕ => (8 * |τ|) ^ (2 * J)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one h64_nonneg h64_lt
    exact h.congr (fun J => by rw [pow_mul])
  have hmaj : Tendsto
      (fun J : ℕ => (1650 * ν.real univ / (1 / 8 - |l| - |τ|)) * (8 * |τ|) ^ (2 * J))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hgeom.const_mul (1650 * ν.real univ / (1 / 8 - |l| - |τ|))
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun J => ?_) hmaj
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_oscillatoryMellin_sub_sum_range_vertical_even_le hk hν hlτ J

/-- **Scale-independent quadratic `O(τ²)` vertical stationary bound for `M_k(l, τ)` around the
real axis `τ = 0` (`k ≥ 2`, `|l| + |τ| < 1/8`):**
`|(∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) −
    ∫_{x > 0} x^{l − 1/2} V_k(x) dx| ≤ (105600 · ν.real univ / (1/8 − |l| − |τ|)) · τ²`. -/
theorem abs_oscillatoryMellin_sub_realAxis_le_sq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l τ : ℝ} (hlτ : |l| + |τ| < 1 / 8) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x| ≤
      (105600 * ν.real univ / (1 / 8 - |l| - |τ|)) * τ ^ 2 := by
  have hk1 : 1 ≤ k := by omega
  have hl_half : |l| < 1 / 2 := by linarith [abs_nonneg τ]
  have hJ1 := abs_oscillatoryMellin_sub_sum_range_vertical_even_le hk hν hlτ 1
  have hterm0 :
      ∑ j ∈ Finset.range 1,
        ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * j) * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x := by
    rw [Finset.sum_range_one]
    simp only [pow_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul]
    rw [setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l,
      integral_exp_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half]
  rw [hterm0] at hJ1
  refine hJ1.trans_eq ?_
  have hsq : (8 * |τ|) ^ (2 * 1) = 64 * τ ^ 2 := by
    calc (8 * |τ|) ^ 2 = 64 * |τ| ^ 2 := by ring
      _ = 64 * τ ^ 2 := by rw [sq_abs]
  rw [hsq]
  ring

/-- **Vanishing first-order vertical derivative of `M_k(l, τ)` on the real axis `τ = 0` across
`|l| < 1/8` (`k ≥ 2`):**
`((∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) − ∫_{x > 0} x^{l − 1/2} V_k(x) dx) / τ → 0`
as `τ → 0`. -/
theorem tendsto_div_oscillatoryMellin_sub_realAxis_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) :
    Tendsto
      (fun τ : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) / τ)
      (nhds 0) (nhds 0) := by
  set δ := (1 / 8 - |l|) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  set C := 105600 * ν.real univ / δ
  have hmaj : Tendsto (fun τ : ℝ => C * |τ|) (nhds 0) (nhds 0) := by
    simpa using (continuous_abs.tendsto 0).const_mul C
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-δ) δ ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by linarith) hδ_pos
  filter_upwards [hmem] with τ hτ_mem
  have hτ_lt : |τ| < δ := abs_lt.mpr hτ_mem
  have hlτ : |l| + |τ| < 1 / 8 := by dsimp [δ] at hτ_lt; linarith
  rw [sub_zero, Real.norm_eq_abs, abs_div]
  rcases eq_or_ne τ 0 with rfl | hτ_ne
  · simp [C]
  · have hτ_pos : 0 < |τ| := abs_pos.mpr hτ_ne
    have h1 := abs_oscillatoryMellin_sub_realAxis_le_sq hk hν hlτ
    have hdenom : δ ≤ 1 / 8 - |l| - |τ| := by dsimp [δ] at hτ_lt ⊢; linarith
    have hinv : 1 / (1 / 8 - |l| - |τ|) ≤ 1 / δ :=
      one_div_le_one_div_of_le hδ_pos hdenom
    have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
    have h2 : (105600 * ν.real univ / (1 / 8 - |l| - |τ|)) * τ ^ 2 ≤ C * |τ| * |τ| := by
      rw [← sq_abs]
      calc (105600 * ν.real univ / (1 / 8 - |l| - |τ|)) * |τ| ^ 2
          = (1 / (1 / 8 - |l| - |τ|)) * (105600 * ν.real univ * |τ| ^ 2) := by ring
        _ ≤ (1 / δ) * (105600 * ν.real univ * |τ| ^ 2) :=
            mul_le_mul_of_nonneg_right hinv (by positivity)
        _ = C * |τ| * |τ| := by dsimp [C]; ring
    exact (div_le_iff₀ hτ_pos).mpr (h1.trans h2)

/-- **Scale-independent quartic `O(τ⁴)` second-order vertical Taylor remainder bound for
`M_k(l, τ)` around `τ = 0` (`k ≥ 2`, `|l| + |τ| < 1/8`):**
`|(∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) −
    (∫_{x > 0} x^{l − 1/2} V_k(x) dx) +
    (τ² / 2) ∫_ℝ v² cosh(lv) Φ_k(v) dv| ≤ (6758400 · ν.real univ / (1/8 − |l| − |τ|)) · τ⁴`. -/
theorem abs_oscillatoryMellin_sub_realAxis_add_quadratic_le_pow_four
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l τ : ℝ} (hlτ : |l| + |τ| < 1 / 8) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) +
      (τ ^ 2 / 2) *
        (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (6758400 * ν.real univ / (1 / 8 - |l| - |τ|)) * τ ^ 4 := by
  have hk1 : 1 ≤ k := by omega
  have hl_half : |l| < 1 / 2 := by linarith [abs_nonneg τ]
  have hJ2 := abs_oscillatoryMellin_sub_sum_range_vertical_even_le hk hν hlτ 2
  have hterm0 :
      (∫ v : ℝ, Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v) =
      ∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x := by
    rw [setIntegral_Ioi_rpow_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l,
      integral_exp_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half]
  have hsum2 :
      ∑ j ∈ Finset.range 2,
        ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * j) * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v) =
      (∫ x in Ioi (0 : ℝ), x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) -
      (τ ^ 2 / 2) *
        (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v) := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pow_zero, mul_zero, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
      pow_one, mul_one, Nat.factorial_two, Nat.cast_ofNat]
    rw [hterm0]
    ring
  rw [hsum2, sub_sub_eq_add_sub, add_sub_right_comm] at hJ2
  refine hJ2.trans_eq ?_
  have hpow4 : (8 * |τ|) ^ (2 * 2) = 4096 * τ ^ 4 := by
    have habs4 : |τ| ^ 4 = τ ^ 4 := by
      calc |τ| ^ 4 = (|τ| ^ 2) ^ 2 := by ring
        _ = (τ ^ 2) ^ 2 := by rw [sq_abs]
        _ = τ ^ 4 := by ring
    calc (8 * |τ|) ^ (2 * 2) = 4096 * |τ| ^ 4 := by ring
      _ = 4096 * τ ^ 4 := by rw [habs4]
  rw [hpow4]
  ring

/-- **Exact second-order vertical curvature limit of `M_k(l, τ)` on the real axis `τ = 0` across
`|l| < 1/8` (`k ≥ 2`):**
`((∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) − ∫_{x > 0} x^{l − 1/2} V_k(x) dx) / τ² →
  −(1/2) ∫_ℝ v² cosh(lv) Φ_k(v) dv` as `τ → 0` (`τ ≠ 0`). -/
theorem tendsto_div_sq_oscillatoryMellin_sub_realAxis_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) :
    Tendsto
      (fun τ : ℝ =>
        ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) / τ ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (-(1 / 2 : ℝ) *
        ∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v)) := by
  set δ := (1 / 8 - |l|) / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  set C := 6758400 * ν.real univ / δ
  have hmaj : Tendsto (fun τ : ℝ => C * τ ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun τ : ℝ => C * τ ^ 2) (nhds 0) (nhds 0) := by
      simpa using ((continuous_id.pow 2).tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-δ) δ ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by linarith) hδ_pos)
  filter_upwards [hmem, self_mem_nhdsWithin] with τ hτ_mem hτ_ne
  simp only [mem_compl_singleton_iff] at hτ_ne
  have hτ_lt : |τ| < δ := abs_lt.mpr hτ_mem
  have hlτ : |l| + |τ| < 1 / 8 := by dsimp [δ] at hτ_lt; linarith
  have hsq_pos : 0 < τ ^ 2 := sq_pos_of_ne_zero hτ_ne
  rw [Real.norm_eq_abs]
  have hdiff_eq :
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) / τ ^ 2 -
      (-(1 / 2 : ℝ) *
        ∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v) =
      ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) +
        (τ ^ 2 / 2) *
          (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v)) / τ ^ 2 := by
    have hne2 : τ ^ 2 ≠ 0 := hsq_pos.ne'
    field_simp
    ring
  rw [hdiff_eq, abs_div, abs_of_pos hsq_pos, div_le_iff₀ hsq_pos]
  have h1 := abs_oscillatoryMellin_sub_realAxis_add_quadratic_le_pow_four hk hν hlτ
  have hdenom : δ ≤ 1 / 8 - |l| - |τ| := by dsimp [δ] at hτ_lt ⊢; linarith
  have hinv : 1 / (1 / 8 - |l| - |τ|) ≤ 1 / δ :=
    one_div_le_one_div_of_le hδ_pos hdenom
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc |(∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) +
        (τ ^ 2 / 2) *
          (∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v)|
      ≤ (6758400 * ν.real univ / (1 / 8 - |l| - |τ|)) * τ ^ 4 := h1
    _ = (1 / (1 / 8 - |l| - |τ|)) * (6758400 * ν.real univ * τ ^ 4) := by ring
    _ ≤ (1 / δ) * (6758400 * ν.real univ * τ ^ 4) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * τ ^ 2 * τ ^ 2 := by dsimp [C]; ring


/-! ## Section 3: Fourth-Order `O(h⁴)` Cauchy–Riemann Harmonic Saddle-Point Cancellation -/

/-- **Fourth-order `O(h⁴)` Cauchy–Riemann harmonic saddle-point cancellation for `M_k` around
the central point `(l, τ) = (0, 0)` (`s = 1/2`, `k ≥ 2`, `|h| < 1/8`):**
At `(l, τ) = (0, 0)`, the second-order horizontal variation `M_k(h, 0) − M_k(0, 0)` and the
second-order vertical variation `M_k(0, h) − M_k(0, 0)` cancel to fourth order `O(h⁴)`:
`|(M_k(h, 0) − M_k(0, 0)) + (M_k(0, h) − M_k(0, 0))| ≤ (13516800 · ν.real univ / (1/8 − |h|)) · h⁴`. -/
theorem abs_oscillatoryMellin_harmonic_laplacian_defect_le_pow_four
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {h : ℝ} (hh : |h| < 1 / 8) :
    |((∫ x in Ioi (0 : ℝ), x ^ (h - 1 / 2) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν x) +
      ((∫ x in Ioi (0 : ℝ),
          x ^ (-(1 / 2 : ℝ)) * Real.cos (h * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν x)| ≤
      (13516800 * ν.real univ / (1 / 8 - |h|)) * h ^ 4 := by
  have hh0 : |(0 : ℝ)| + |h| < 1 / 8 := by simpa using hh
  have h_horiz := abs_oscillatoryMellin_sub_criticalLine_sub_quadratic_le_pow_four hk hν hh 0
  have h_vert := abs_oscillatoryMellin_sub_realAxis_add_quadratic_le_pow_four hk hν hh0
  simp only [zero_mul, Real.cos_zero, mul_one, zero_sub, abs_zero, sub_zero,
    Real.cosh_zero] at h_horiz h_vert
  set M_h0 := ∫ x in Ioi (0 : ℝ), x ^ (h - 1 / 2) * arcLineInfiniteDyadicVector k ν x
  set M_00 := ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν x
  set M_0h := ∫ x in Ioi (0 : ℝ),
    x ^ (-(1 / 2 : ℝ)) * Real.cos (h * Real.log x) * arcLineInfiniteDyadicVector k ν x
  set Q := (h ^ 2 / 2) * ∫ v : ℝ, v ^ 2 * arcLineInfiniteDyadicProfile k ν v
  have hsplit :
      (M_h0 - M_00) + (M_0h - M_00) =
        (M_h0 - M_00 - Q) + (M_0h - M_00 + Q) := by ring
  rw [hsplit]
  have htri := (abs_add_le (M_h0 - M_00 - Q) (M_0h - M_00 + Q)).trans (add_le_add h_horiz h_vert)
  refine htri.trans_eq ?_
  ring

/-- **Vanishing second-order harmonic Laplacian divided difference of `M_k` at `(l, τ) = (0, 0)`:**
`((M_k(h, 0) − M_k(0, 0)) + (M_k(0, h) − M_k(0, 0))) / h² → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_oscillatoryMellin_harmonic_laplacian_defect_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (0 : ℝ), x ^ (h - 1 / 2) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioi (0 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos (h * Real.log x) *
                arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioi (0 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν x)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  set C := 216268800 * ν.real univ
  have hmaj : Tendsto (fun h : ℝ => C * h ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
    have h0 : Tendsto (fun h : ℝ => C * h ^ 2) (nhds 0) (nhds 0) := by
      simpa using ((continuous_id.pow 2).tendsto 0).const_mul C
    exact h0.mono_left nhdsWithin_le_nhds
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
  have hmem : Ioo (-1 / 16 : ℝ) (1 / 16) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem, self_mem_nhdsWithin] with h hh_mem hh_ne
  simp only [mem_compl_singleton_iff] at hh_ne
  have hh16 : |h| < 1 / 16 := abs_lt.mpr ⟨by linarith [hh_mem.1], hh_mem.2⟩
  have hh8 : |h| < 1 / 8 := by linarith
  have hsq_pos : 0 < h ^ 2 := sq_pos_of_ne_zero hh_ne
  rw [sub_zero, Real.norm_eq_abs, abs_div, abs_of_pos hsq_pos, div_le_iff₀ hsq_pos]
  have h1 := abs_oscillatoryMellin_harmonic_laplacian_defect_le_pow_four hk hν hh8
  have hdenom : (1 / 16 : ℝ) ≤ 1 / 8 - |h| := by linarith
  have hinv : 1 / (1 / 8 - |h|) ≤ 16 := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 16) hdenom
    linarith
  have hν0 : 0 ≤ ν.real univ := measureReal_nonneg
  calc |((∫ x in Ioi (0 : ℝ), x ^ (h - 1 / 2) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν x) +
        ((∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (h * Real.log x) *
              arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν x)|
      ≤ (13516800 * ν.real univ / (1 / 8 - |h|)) * h ^ 4 := h1
    _ = (1 / (1 / 8 - |h|)) * (13516800 * ν.real univ * h ^ 4) := by ring
    _ ≤ 16 * (13516800 * ν.real univ * h ^ 4) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = C * h ^ 2 * h ^ 2 := by dsimp [C]; ring


/-! ## Section 4: Joint Two-Variable `(l, τ)` Taylor Polynomials & Diagonal Power Series -/

/-- **All-orders integrability of `v ↦ v^n Φ_k(v)` on `ℝ` (`k ≥ 2`, `n ∈ ℕ`).** -/
theorem integrable_pow_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) :
    Integrable (fun v : ℝ => v ^ n * arcLineInfiniteDyadicProfile k ν v) := by
  simpa using integrable_pow_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν n 0

/-- **All-orders half-line integrability of `v ↦ v^n Φ_k(v)` on `(0, ∞)` (`k ≥ 2`, `n ∈ ℕ`).** -/
theorem integrableOn_Ioi_zero_pow_mul_arcLineInfiniteDyadicProfile
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (n : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ n * arcLineInfiniteDyadicProfile k ν v) (Ioi (0 : ℝ)) :=
  (integrable_pow_mul_arcLineInfiniteDyadicProfile hk hν n).integrableOn

/-- **Full-line integral linearity for the `(M, J)` double even Taylor polynomial against `Φ_k(v)`:**
`∫_ℝ (∑_{m < M} (lv)^{2m} / (2m)!) (∑_{j < J} (−1)^j (τv)^{2j} / (2j)!) Φ_k(v) dv =
  ∑_{m < M} ∑_{j < J} (l^{2m} / (2m)!) ((−1)^j τ^{2j} / (2j)!) ∫_ℝ v^{2m+2j} Φ_k(v) dv`. -/
theorem integral_double_sum_range_even_pow_mul_profile_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (l τ : ℝ) (M J : ℕ) :
    (∫ v : ℝ,
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) =
      ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
        (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m + 2 * j) * arcLineInfiniteDyadicProfile k ν v) := by
  have hfun :
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
        ((l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ))) *
          (v ^ (2 * m + 2 * j) * arcLineInfiniteDyadicProfile k ν v) := by
    ext v
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_pow, mul_pow, pow_add]
    ring
  rw [hfun, integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      exact integral_const_mul _ _
    · intro j _
      exact (integrable_pow_mul_arcLineInfiniteDyadicProfile hk hν (2 * m + 2 * j)).const_mul _
  · intro m _
    exact integrable_finsetSum _ (fun j _ =>
      (integrable_pow_mul_arcLineInfiniteDyadicProfile hk hν (2 * m + 2 * j)).const_mul _)

/-- **Scale-independent additive geometric remainder bound for the `(M, J)` joint two-variable
Taylor polynomial of `M_k(l, τ)` across `|l| + |τ| < 1/8` (`k ≥ 2`, `M, J ∈ ℕ`):**
`|(∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx) −
    ∑_{m < M} ∑_{j < J} (l^{2m} / (2m)!) ((−1)^j τ^{2j} / (2j)!) ∫_ℝ v^{2m+2j} Φ_k(v) dv| ≤
  (1650 · ν.real univ / (1/8 − |l| − |τ|)) · ((8|l|)^{2M} + (8|τ|)^{2J})`. -/
theorem abs_oscillatoryMellin_sub_double_sum_range_even_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l τ : ℝ} (hlτ : |l| + |τ| < 1 / 8) (M J : ℕ) :
    |(∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
        (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          (∫ v : ℝ, v ^ (2 * m + 2 * j) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (1650 * ν.real univ / (1 / 8 - |l| - |τ|)) *
        ((8 * |l|) ^ (2 * M) + (8 * |τ|) ^ (2 * J)) := by
  have hk1 : 1 ≤ k := by omega
  have hl_half : |l| < 1 / 2 := by linarith [abs_nonneg τ]
  have hc : 0 < 1 / 8 - |l| - |τ| := by linarith
  rw [setIntegral_Ioi_rpow_mul_cos_log_mul_arcLineInfiniteDyadicVector_eq_profile hk1 ν l τ,
    integral_exp_mul_cos_mul_arcLineInfiniteDyadicProfile_eq_cosh hk hν hl_half τ,
    ← integral_double_sum_range_even_pow_mul_profile_eq hk hν l τ M J]
  have hInt_cosh : Integrable
      (fun v : ℝ => Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) :=
    integrable_cosh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ
  have hInt_sum : Integrable
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) := by
    have hfun :
        (fun v : ℝ =>
          (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            (∑ j ∈ Finset.range J,
              (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
            arcLineInfiniteDyadicProfile k ν v) =
        fun v : ℝ => ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
          ((l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ))) *
            (v ^ (2 * m + 2 * j) * arcLineInfiniteDyadicProfile k ν v) := by
      ext v
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [mul_pow, mul_pow, pow_add]; ring
    rw [hfun]
    exact integrable_finsetSum _ (fun m _ =>
      integrable_finsetSum _ (fun j _ =>
        (integrable_pow_mul_arcLineInfiniteDyadicProfile hk hν (2 * m + 2 * j)).const_mul _))
  rw [← integral_sub hInt_cosh hInt_sum]
  set B := 825 * ν.real univ * ((8 * |l|) ^ (2 * M) + (8 * |τ|) ^ (2 * J))
  have hdom : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |τ|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v)
    hdom (Eventually.of_forall fun v => ?_)
  · rw [Real.norm_eq_abs, integral_const_mul, integral_rexp_neg_mul_abs hc] at h1
    calc |∫ v : ℝ,
            (Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
              (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
                (∑ j ∈ Finset.range J,
                  (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
                arcLineInfiniteDyadicProfile k ν v)|
        ≤ B * (2 / (1 / 8 - |l| - |τ|)) := h1
      _ = (1650 * ν.real univ / (1 / 8 - |l| - |τ|)) *
            ((8 * |l|) ^ (2 * M) + (8 * |τ|) ^ (2 * J)) := by
          dsimp [B]; ring
  · rw [Real.norm_eq_abs, ← sub_mul, abs_mul]
    have hrem := abs_cosh_mul_cos_sub_double_sum_range_le M J l τ v
    have ht1 := joint_taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le hk hν (2 * M) l l τ v
    have ht2 := joint_taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le hk hν (2 * J) τ l τ v
    calc |Real.cosh (l * v) * Real.cos (τ * v) -
            (∑ m ∈ Finset.range M, (l * v) ^ (2 * m) / ((2 * m).factorial : ℝ)) *
              (∑ j ∈ Finset.range J,
                (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ))| *
            |arcLineInfiniteDyadicProfile k ν v|
        ≤ (((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ) +
              (|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|)) *
            |arcLineInfiniteDyadicProfile k ν v| :=
          mul_le_mul_of_nonneg_right hrem (abs_nonneg _)
      _ = ((|l| * |v|) ^ (2 * M) / ((2 * M).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|) * |arcLineInfiniteDyadicProfile k ν v| +
          ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
            Real.exp ((|l| + |τ|) * |v|) * |arcLineInfiniteDyadicProfile k ν v| := by ring
      _ ≤ 825 * ν.real univ * (8 * |l|) ^ (2 * M) * Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) +
          825 * ν.real univ * (8 * |τ|) ^ (2 * J) * Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) :=
        add_le_add ht1 ht2
      _ = B * Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) := by dsimp [B]; ring

/-- **Unconditional `N → ∞` diagonal joint two-variable power-series convergence for `M_k(l, τ)`
across `|l| + |τ| < 1/8` (`k ≥ 2`):**
`∑_{m < N} ∑_{j < N} (l^{2m} / (2m)!) ((−1)^j τ^{2j} / (2j)!) ∫_ℝ v^{2m+2j} Φ_k(v) dv →
  ∫_{x > 0} x^{l − 1/2} cos(τ log x) V_k(x) dx` as `N → ∞`. -/
theorem tendsto_double_sum_range_even_pow_div_factorial_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l τ : ℝ} (hlτ : |l| + |τ| < 1 / 8) :
    Tendsto
      (fun N : ℕ =>
        ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
            ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
            (∫ v : ℝ, v ^ (2 * m + 2 * j) * arcLineInfiniteDyadicProfile k ν v))
      atTop
      (nhds (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) := by
  have h8l_lt : 8 * |l| < 1 := by linarith [abs_nonneg τ]
  have h8τ_lt : 8 * |τ| < 1 := by linarith [abs_nonneg l]
  have h64l_lt : (8 * |l|) ^ 2 < 1 := by nlinarith [abs_nonneg l]
  have h64τ_lt : (8 * |τ|) ^ 2 < 1 := by nlinarith [abs_nonneg τ]
  have hgeom_l : Tendsto (fun N : ℕ => (8 * |l|) ^ (2 * N)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) h64l_lt
    exact h.congr (fun N => by rw [pow_mul])
  have hgeom_τ : Tendsto (fun N : ℕ => (8 * |τ|) ^ (2 * N)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) h64τ_lt
    exact h.congr (fun N => by rw [pow_mul])
  have hsum_geom :
      Tendsto (fun N : ℕ => (8 * |l|) ^ (2 * N) + (8 * |τ|) ^ (2 * N)) atTop (nhds 0) := by
    simpa using hgeom_l.add hgeom_τ
  have hmaj : Tendsto
      (fun N : ℕ =>
        (1650 * ν.real univ / (1 / 8 - |l| - |τ|)) *
          ((8 * |l|) ^ (2 * N) + (8 * |τ|) ^ (2 * N)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hsum_geom.const_mul (1650 * ν.real univ / (1 / 8 - |l| - |τ|))
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hmaj
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_oscillatoryMellin_sub_double_sum_range_even_le hk hν hlτ N N

/-- **Half-line integral linearity for the `(M, J)` double odd-even Taylor polynomial against `Φ_k(v)`:**
`∫_{v > 0} 2 (∑_{m < M} (lv)^{2m+1} / (2m+1)!) (∑_{j < J} (−1)^j (τv)^{2j} / (2j)!) Φ_k(v) dv =
  2 ∑_{m < M} ∑_{j < J} (l^{2m+1} / (2m+1)!) ((−1)^j τ^{2j} / (2j)!) ∫_{v > 0} v^{2m+1+2j} Φ_k(v) dv`. -/
theorem setIntegral_Ioi_zero_two_mul_double_sum_range_odd_even_pow_mul_profile_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (l τ : ℝ) (M J : ℕ) :
    (∫ v in Ioi (0 : ℝ),
        2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) =
      2 * ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
        (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          (∫ v in Ioi (0 : ℝ),
            v ^ (2 * m + 1 + 2 * j) * arcLineInfiniteDyadicProfile k ν v) := by
  have hfun :
      (fun v : ℝ =>
        2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => 2 *
        ((∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) := by
    ext v; ring
  rw [hfun, integral_const_mul]
  congr 1
  have hfun2 :
      (fun v : ℝ =>
        (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) =
      fun v : ℝ => ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
        ((l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ))) *
          (v ^ (2 * m + 1 + 2 * j) * arcLineInfiniteDyadicProfile k ν v) := by
    ext v
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_pow, mul_pow, pow_add]; ring
  rw [hfun2, integral_finsetSum]
  · refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      exact integral_const_mul _ _
    · intro j _
      exact (integrableOn_Ioi_zero_pow_mul_arcLineInfiniteDyadicProfile
        hk hν (2 * m + 1 + 2 * j)).const_mul _
  · intro m _
    exact integrable_finsetSum _ (fun j _ =>
      (integrableOn_Ioi_zero_pow_mul_arcLineInfiniteDyadicProfile
        hk hν (2 * m + 1 + 2 * j)).const_mul _)

/-- **Scale-independent additive geometric remainder bound for the `(M, J)` joint two-variable
Taylor polynomial of `Δ_k^{\mathrm{Mellin}}(l, τ)` across `|l| + |τ| < 1/8` (`k ≥ 2`, `M, J ∈ ℕ`):**
`|Δ_k^{\mathrm{Mellin}}(l, τ) −
    2 ∑_{m < M} ∑_{j < J} (l^{2m+1} / (2m+1)!) ((−1)^j τ^{2j} / (2j)!) ∫_{v > 0} v^{2m+1+2j} Φ_k(v) dv| ≤
  (3300 · ν.real univ / (1/8 − |l| − |τ|)) · ((8|l|)^{2M+1} + (8|τ|)^{2J})`. -/
theorem abs_oscillatoryMellin_imbalance_sub_two_mul_double_sum_range_odd_even_le
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l τ : ℝ} (hlτ : |l| + |τ| < 1 / 8) (M J : ℕ) :
    |((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      2 * ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
        (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          (∫ v in Ioi (0 : ℝ),
            v ^ (2 * m + 1 + 2 * j) * arcLineInfiniteDyadicProfile k ν v)| ≤
      (3300 * ν.real univ / (1 / 8 - |l| - |τ|)) *
        ((8 * |l|) ^ (2 * M + 1) + (8 * |τ|) ^ (2 * J)) := by
  have hl_half : |l| < 1 / 2 := by linarith [abs_nonneg τ]
  have hc : 0 < 1 / 8 - |l| - |τ| := by linarith
  rw [setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_mul_cos_log_eq hk hν hl_half τ,
    ← setIntegral_Ioi_zero_two_mul_double_sum_range_odd_even_pow_mul_profile_eq hk hν l τ M J]
  have hInt_sinh : IntegrableOn
      (fun v : ℝ => 2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)
      (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_zero_two_mul_sinh_mul_cos_mul_arcLineInfiniteDyadicProfile hk hν hl_half τ
  have hInt_sum : IntegrableOn
      (fun v : ℝ =>
        2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v) (Ioi (0 : ℝ)) := by
    have hfun :
        (fun v : ℝ =>
          2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (∑ j ∈ Finset.range J,
              (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
            arcLineInfiniteDyadicProfile k ν v) =
        fun v : ℝ => 2 * ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
          ((l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ))) *
            (v ^ (2 * m + 1 + 2 * j) * arcLineInfiniteDyadicProfile k ν v) := by
      ext v
      have h1 :
          (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (∑ j ∈ Finset.range J,
              (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
            arcLineInfiniteDyadicProfile k ν v =
          ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
            ((l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
              ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ))) *
              (v ^ (2 * m + 1 + 2 * j) * arcLineInfiniteDyadicProfile k ν v) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [mul_pow, mul_pow, pow_add]; ring
      calc 2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
              (∑ j ∈ Finset.range J,
                (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
              arcLineInfiniteDyadicProfile k ν v
          = 2 * ((∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
              (∑ j ∈ Finset.range J,
                (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
              arcLineInfiniteDyadicProfile k ν v) := by ring
        _ = 2 * ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
              ((l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
                ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ))) *
                (v ^ (2 * m + 1 + 2 * j) * arcLineInfiniteDyadicProfile k ν v) := by rw [h1]
    rw [hfun]
    exact (integrable_finsetSum _ (fun m _ =>
      integrable_finsetSum _ (fun j _ =>
        (integrableOn_Ioi_zero_pow_mul_arcLineInfiniteDyadicProfile
          hk hν (2 * m + 1 + 2 * j)).const_mul _))).const_mul 2
  rw [← integral_sub hInt_sinh hInt_sum]
  set B := 2 * 825 * ν.real univ * ((8 * |l|) ^ (2 * M + 1) + (8 * |τ|) ^ (2 * J))
  have hdom_full : Integrable (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |τ|) * |v|))) :=
    (integrable_rexp_neg_mul_abs hc).const_mul B
  have hdom : IntegrableOn
      (fun v : ℝ => B * Real.exp (-((1 / 8 - |l| - |τ|) * |v|))) (Ioi (0 : ℝ)) :=
    hdom_full.integrableOn
  have h1 := norm_integral_le_of_norm_le
    (f := fun v : ℝ =>
      2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
        2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
          (∑ j ∈ Finset.range J,
            (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
          arcLineInfiniteDyadicProfile k ν v)
    hdom (ae_restrict_mem measurableSet_Ioi |>.mono fun v _ => ?_)
  · have hle_full :
        (∫ v in Ioi (0 : ℝ), B * Real.exp (-((1 / 8 - |l| - |τ|) * |v|))) ≤
          ∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) := by
      refine setIntegral_le_integral hdom_full (Eventually.of_forall fun v => ?_)
      have := measureReal_nonneg (μ := ν) (s := univ)
      dsimp [B]; positivity
    have hfull_eq :
        (∫ v : ℝ, B * Real.exp (-((1 / 8 - |l| - |τ|) * |v|))) =
          (3300 * ν.real univ / (1 / 8 - |l| - |τ|)) *
            ((8 * |l|) ^ (2 * M + 1) + (8 * |τ|) ^ (2 * J)) := by
      rw [integral_const_mul, integral_rexp_neg_mul_abs hc]
      dsimp [B]; ring
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (hle_full.trans hfull_eq.le)
  · have hsub :
        2 * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v -
          2 * (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            (∑ j ∈ Finset.range J,
              (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ)) *
            arcLineInfiniteDyadicProfile k ν v =
        2 * ((Real.sinh (l * v) * Real.cos (τ * v) -
            (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
              (∑ j ∈ Finset.range J,
                (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ))) *
          arcLineInfiniteDyadicProfile k ν v) := by ring
    rw [Real.norm_eq_abs, hsub, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hrem := abs_sinh_mul_cos_sub_double_sum_range_le M J l τ v
    have ht1 :=
      joint_taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le hk hν (2 * M + 1) l l τ v
    have ht2 :=
      joint_taylor_remainder_mul_abs_arcLineInfiniteDyadicProfile_le hk hν (2 * J) τ l τ v
    calc 2 * (|Real.sinh (l * v) * Real.cos (τ * v) -
              (∑ m ∈ Finset.range M, (l * v) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
                (∑ j ∈ Finset.range J,
                  (-1 : ℝ) ^ j * (τ * v) ^ (2 * j) / ((2 * j).factorial : ℝ))| *
            |arcLineInfiniteDyadicProfile k ν v|)
        ≤ 2 * ((((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ) +
                (|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
              Real.exp ((|l| + |τ|) * |v|)) *
            |arcLineInfiniteDyadicProfile k ν v|) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hrem (abs_nonneg _)) (by positivity)
      _ = 2 * (((|l| * |v|) ^ (2 * M + 1) / ((2 * M + 1).factorial : ℝ)) *
              Real.exp ((|l| + |τ|) * |v|) * |arcLineInfiniteDyadicProfile k ν v| +
            ((|τ| * |v|) ^ (2 * J) / ((2 * J).factorial : ℝ)) *
              Real.exp ((|l| + |τ|) * |v|) * |arcLineInfiniteDyadicProfile k ν v|) := by ring
      _ ≤ 2 * (825 * ν.real univ * (8 * |l|) ^ (2 * M + 1) *
              Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) +
            825 * ν.real univ * (8 * |τ|) ^ (2 * J) *
              Real.exp (-((1 / 8 - |l| - |τ|) * |v|))) :=
          mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) (by positivity)
      _ = B * Real.exp (-((1 / 8 - |l| - |τ|) * |v|)) := by dsimp [B]; ring

/-- **Unconditional `N → ∞` diagonal joint two-variable power-series convergence for
`Δ_k^{\mathrm{Mellin}}(l, τ)` across `|l| + |τ| < 1/8` (`k ≥ 2`):**
`2 ∑_{m < N} ∑_{j < N} (l^{2m+1} / (2m+1)!) ((−1)^j τ^{2j} / (2j)!) ∫_{v > 0} v^{2m+1+2j} Φ_k(v) dv →
  Δ_k^{\mathrm{Mellin}}(l, τ)` as `N → ∞`. -/
theorem tendsto_two_mul_double_sum_range_odd_even_pow_div_factorial_atTop
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l τ : ℝ} (hlτ : |l| + |τ| < 1 / 8) :
    Tendsto
      (fun N : ℕ =>
        2 * ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range N,
          (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
            ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
            (∫ v in Ioi (0 : ℝ),
              v ^ (2 * m + 1 + 2 * j) * arcLineInfiniteDyadicProfile k ν v))
      atTop
      (nhds ((∫ x in Ioi (1 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        ∫ x in Ioc (0 : ℝ) 1,
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) := by
  have h8l_lt : 8 * |l| < 1 := by linarith [abs_nonneg τ]
  have h8τ_lt : 8 * |τ| < 1 := by linarith [abs_nonneg l]
  have h64l_lt : (8 * |l|) ^ 2 < 1 := by nlinarith [abs_nonneg l]
  have h64τ_lt : (8 * |τ|) ^ 2 < 1 := by nlinarith [abs_nonneg τ]
  have hgeom_l_even : Tendsto (fun N : ℕ => (8 * |l|) ^ (2 * N)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) h64l_lt
    exact h.congr (fun N => by rw [pow_mul])
  have hgeom_l : Tendsto (fun N : ℕ => (8 * |l|) ^ (2 * N + 1)) atTop (nhds 0) := by
    have h := hgeom_l_even.mul_const (8 * |l|)
    rw [zero_mul] at h
    exact h.congr (fun N => (pow_succ (8 * |l|) (2 * N)).symm)
  have hgeom_τ : Tendsto (fun N : ℕ => (8 * |τ|) ^ (2 * N)) atTop (nhds 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) h64τ_lt
    exact h.congr (fun N => by rw [pow_mul])
  have hsum_geom :
      Tendsto (fun N : ℕ => (8 * |l|) ^ (2 * N + 1) + (8 * |τ|) ^ (2 * N)) atTop (nhds 0) := by
    simpa using hgeom_l.add hgeom_τ
  have hmaj : Tendsto
      (fun N : ℕ =>
        (3300 * ν.real univ / (1 / 8 - |l| - |τ|)) *
          ((8 * |l|) ^ (2 * N + 1) + (8 * |τ|) ^ (2 * N)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using hsum_geom.const_mul (3300 * ν.real univ / (1 / 8 - |l| - |τ|))
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_) hmaj
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact abs_oscillatoryMellin_imbalance_sub_two_mul_double_sum_range_odd_even_le hk hν hlτ N N

/-- **Master Joint Two-Variable Power-Series, Vertical Curvature, and Harmonic Saddle-Point Witness Theorem:**
There exists a non-zero finite Borel measure `ν` on `ArcParam` symmetric under `arcNeg` such
that for every integer scale `k ≥ 2`:
1. **Vertical (`τ`-Direction) Taylor Remainder & Power-Series Convergence (`|l| + |τ| < 1/8`):**
   - `|M_k(l, τ) − ∑_{j < J} ((−1)^j τ^{2j} / (2j)!) ∫_ℝ v^{2j} cosh(lv) Φ_k(v) dv| ≤
       (1650 · ν.real univ / (1/8 − |l| − |τ|)) · (8|τ|)^{2J} → 0` as `J → ∞`;
2. **Vertical Stationarity & Second-Order Vertical Curvature (`|l| < 1/8`, `τ → 0`):**
   - `(M_k(l, τ) − M_k(l, 0)) / τ → 0` as `τ → 0`,
   - `(M_k(l, τ) − M_k(l, 0)) / τ² → −(1/2) ∫_ℝ v² cosh(lv) Φ_k(v) dv` as `τ → 0` (`τ ≠ 0`);
3. **Fourth-Order `O(h⁴)` Cauchy–Riemann Harmonic Saddle-Point Cancellation (`|h| < 1/8`):**
   - `|(M_k(h, 0) − M_k(0, 0)) + (M_k(0, h) − M_k(0, 0))| ≤
       (13516800 · ν.real univ / (1/8 − |h|)) · h⁴`,
   - `((M_k(h, 0) − M_k(0, 0)) + (M_k(0, h) − M_k(0, 0))) / h² → 0` as `h → 0` (`h ≠ 0`);
4. **Joint Two-Variable `(l, τ)` Taylor Remainder & Diagonal Power-Series Convergence (`|l| + |τ| < 1/8`):**
   - `|M_k(l, τ) − ∑_{m < M} ∑_{j < J} (l^{2m} / (2m)!) ((−1)^j τ^{2j} / (2j)!) ∫_ℝ v^{2m+2j} Φ_k(v) dv| ≤
       (1650 · ν.real univ / (1/8 − |l| − |τ|)) · ((8|l|)^{2M} + (8|τ|)^{2J})`,
   - Diagonal partial sums (`M = J = N`) converge as `N → ∞` to `M_k(l, τ)` and `Δ_k^{\mathrm{Mellin}}(l, τ)`. -/
theorem exists_dyadic_jointTwoVariable_powerSeries_arcWitness :
    ∃ (ν : Measure ArcParam),
      ∃ (_ : IsFiniteMeasure ν),
        ν ≠ 0 ∧
        ν.map arcNeg = ν ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l τ : ℝ}, |l| + |τ| < 1 / 8 → ∀ J : ℕ,
          |(∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∑ j ∈ Finset.range J,
              ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
                (∫ v : ℝ, v ^ (2 * j) * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v)| ≤
            (1650 * ν.real univ / (1 / 8 - |l| - |τ|)) * (8 * |τ|) ^ (2 * J)) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l τ : ℝ}, |l| + |τ| < 1 / 8 →
          Tendsto
            (fun J : ℕ =>
              ∑ j ∈ Finset.range J,
                ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
                  (∫ v : ℝ,
                    v ^ (2 * j) * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v))
            atTop
            (nhds (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 8 →
          Tendsto
            (fun τ : ℝ =>
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
                    arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) / τ)
            (nhds 0) (nhds 0)) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l : ℝ}, |l| < 1 / 8 →
          Tendsto
            (fun τ : ℝ =>
              ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
                    arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * arcLineInfiniteDyadicVector k ν x) / τ ^ 2)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds (-(1 / 2 : ℝ) *
              ∫ v : ℝ, v ^ 2 * Real.cosh (l * v) * arcLineInfiniteDyadicProfile k ν v))) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {h : ℝ}, |h| < 1 / 8 →
          |((∫ x in Ioi (0 : ℝ), x ^ (h - 1 / 2) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν x) +
            ((∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos (h * Real.log x) *
                  arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioi (0 : ℝ), x ^ (-(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν x)| ≤
            (13516800 * ν.real univ / (1 / 8 - |h|)) * h ^ 4) ∧
        (∀ {k : ℕ}, 2 ≤ k →
          Tendsto
            (fun h : ℝ =>
              (((∫ x in Ioi (0 : ℝ), x ^ (h - 1 / 2) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν x) +
                ((∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (h * Real.log x) *
                      arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioi (0 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * arcLineInfiniteDyadicVector k ν x)) / h ^ 2)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l τ : ℝ}, |l| + |τ| < 1 / 8 → ∀ M J : ℕ,
          |(∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∑ m ∈ Finset.range M, ∑ j ∈ Finset.range J,
              (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
                ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
                (∫ v : ℝ, v ^ (2 * m + 2 * j) * arcLineInfiniteDyadicProfile k ν v)| ≤
            (1650 * ν.real univ / (1 / 8 - |l| - |τ|)) *
              ((8 * |l|) ^ (2 * M) + (8 * |τ|) ^ (2 * J))) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l τ : ℝ}, |l| + |τ| < 1 / 8 →
          Tendsto
            (fun N : ℕ =>
              ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range N,
                (l ^ (2 * m) / ((2 * m).factorial : ℝ)) *
                  ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
                  (∫ v : ℝ, v ^ (2 * m + 2 * j) * arcLineInfiniteDyadicProfile k ν v))
            atTop
            (nhds (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x))) ∧
        (∀ {k : ℕ}, 2 ≤ k → ∀ {l τ : ℝ}, |l| + |τ| < 1 / 8 →
          Tendsto
            (fun N : ℕ =>
              2 * ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range N,
                (l ^ (2 * m + 1) / ((2 * m + 1).factorial : ℝ)) *
                  ((-1 : ℝ) ^ j * τ ^ (2 * j) / ((2 * j).factorial : ℝ)) *
                  (∫ v in Ioi (0 : ℝ),
                    v ^ (2 * m + 1 + 2 * j) * arcLineInfiniteDyadicProfile k ν v))
            atTop
            (nhds ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) *
                  arcLineInfiniteDyadicVector k ν x))) := by
  obtain ⟨ν, hfin, hν_ne, hν_sym, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν_ne, hν_sym, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk l τ hlτ J
    exact abs_oscillatoryMellin_sub_sum_range_vertical_even_le hk hν_sym hlτ J
  · intro k hk l τ hlτ
    exact tendsto_sum_range_vertical_even_pow_div_factorial_atTop hk hν_sym hlτ
  · intro k hk l hl
    exact tendsto_div_oscillatoryMellin_sub_realAxis_nhds_zero hk hν_sym hl
  · intro k hk l hl
    exact tendsto_div_sq_oscillatoryMellin_sub_realAxis_nhds_zero hk hν_sym hl
  · intro k hk h hh
    exact abs_oscillatoryMellin_harmonic_laplacian_defect_le_pow_four hk hν_sym hh
  · intro k hk
    exact tendsto_div_sq_oscillatoryMellin_harmonic_laplacian_defect_nhds_zero hk hν_sym
  · intro k hk l τ hlτ M J
    exact abs_oscillatoryMellin_sub_double_sum_range_even_le hk hν_sym hlτ M J
  · intro k hk l τ hlτ
    exact tendsto_double_sum_range_even_pow_div_factorial_atTop hk hν_sym hlτ
  · intro k hk l τ hlτ
    exact tendsto_two_mul_double_sum_range_odd_even_pow_div_factorial_atTop hk hν_sym hlτ

end

end RHTower
