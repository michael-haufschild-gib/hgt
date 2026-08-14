import Mathlib.Analysis.InnerProductSpace.Basic
import GaloisForLFunctions.RHTower.ConstrainedProlateHermiteParityEvaluation

/-!
# Two-mode Rayleigh quotient and exact floor limits

This module formalizes the exact algebraic Rayleigh quotient of the zero-integral two-mode
constrained prolate combination `l₁ e₀ - l₀ e₁`, its quotient relative to the second eigenvalue
`d₁`, its general limit theorem under coordinate convergence and eigenvalue separation
`d₀ / d₁ → 0`, and its specialization to both the positive and negative sector Hermite floor
values `8/11`, `8/13`, and their ratio `13/11`.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The unnormalized zero-integral two-mode constrained seed `l₁ e₀ - l₀ e₁`. -/
def twoModeSeed (l0 l1 : ℝ) (e0 e1 : E) : E := l1 • e0 - l0 • e1

/-- The two-mode seed is exactly orthogonal to the constraint direction `l₀ e₀ + l₁ e₁`. -/
theorem twoModeSeed_constraint_orthogonal (l0 l1 : ℝ) (e0 e1 : E)
    (he01 : inner ℝ e0 e1 = (0 : ℝ))
    (he0 : inner ℝ e0 e0 = (1 : ℝ))
    (he1 : inner ℝ e1 e1 = (1 : ℝ)) :
    inner ℝ (twoModeSeed l0 l1 e0 e1) (l0 • e0 + l1 • e1) = (0 : ℝ) := by
  unfold twoModeSeed
  have he0_sq : ‖e0‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, he0]
  have he1_sq : ‖e1‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, he1]
  simp only [inner_sub_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, he0_sq, he1_sq]
  have he10 : inner ℝ e1 e0 = (0 : ℝ) := by
    rw [real_inner_comm, he01]
  rw [he01, he10]
  ring

/-- The squared norm of the two-mode seed on orthonormal modes is `l₀² + l₁²`. -/
theorem twoModeSeed_norm_sq (l0 l1 : ℝ) (e0 e1 : E)
    (he01 : inner ℝ e0 e1 = (0 : ℝ))
    (he0 : inner ℝ e0 e0 = (1 : ℝ))
    (he1 : inner ℝ e1 e1 = (1 : ℝ)) :
    ‖twoModeSeed l0 l1 e0 e1‖ ^ 2 = l0 ^ 2 + l1 ^ 2 := by
  unfold twoModeSeed
  rw [norm_sub_sq_real]
  have he0_sq : ‖e0‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, he0]
  have he1_sq : ‖e1‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, he1]
  simp only [norm_smul, mul_pow, he0_sq, he1_sq, mul_one, real_inner_smul_left,
    real_inner_smul_right, he01, mul_zero, sub_zero]
  have hsq0 : ‖l0‖ ^ 2 = l0 ^ 2 := sq_abs l0
  have hsq1 : ‖l1‖ ^ 2 = l1 ^ 2 := sq_abs l1
  rw [hsq0, hsq1]
  ring

/-- The quadratic energy of the two-mode seed under an operator diagonal on `e₀, e₁`. -/
theorem twoModeSeed_energy (l0 l1 : ℝ) (e0 e1 : E) (K : E →L[ℝ] E) (d0 d1 : ℝ)
    (hKe0 : K e0 = d0 • e0) (hKe1 : K e1 = d1 • e1)
    (he01 : inner ℝ e0 e1 = (0 : ℝ))
    (he0 : inner ℝ e0 e0 = (1 : ℝ))
    (he1 : inner ℝ e1 e1 = (1 : ℝ)) :
    inner ℝ (twoModeSeed l0 l1 e0 e1) (K (twoModeSeed l0 l1 e0 e1)) =
      l1 ^ 2 * d0 + l0 ^ 2 * d1 := by
  unfold twoModeSeed
  have hK_seed : K (l1 • e0 - l0 • e1) = l1 • (d0 • e0) - l0 • (d1 • e1) := by
    simp [map_sub, map_smul, hKe0, hKe1]
  rw [hK_seed]
  have he0_sq : ‖e0‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, he0]
  have he1_sq : ‖e1‖ ^ 2 = 1 := by rw [← real_inner_self_eq_norm_sq, he1]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, he0_sq, he1_sq]
  have he10 : inner ℝ e1 e0 = (0 : ℝ) := by
    rw [real_inner_comm, he01]
  rw [he01, he10]
  ring

noncomputable section

/-- The exact Rayleigh quotient of the two-mode constrained prolate combination. -/
def twoModeRayleighQuotient (d0 d1 l0 l1 : ℝ) : ℝ :=
  (l1 ^ 2 * d0 + l0 ^ 2 * d1) / (l0 ^ 2 + l1 ^ 2)

/-- Algebraic identity rescaling the two-mode Rayleigh quotient by `d₁`. -/
theorem twoModeRayleighQuotient_div_d1_eq (d0 d1 l0 l1 : ℝ) (hd1 : d1 ≠ 0) :
    twoModeRayleighQuotient d0 d1 l0 l1 / d1 =
      (l1 ^ 2 * (d0 / d1) + l0 ^ 2) / (l0 ^ 2 + l1 ^ 2) := by
  unfold twoModeRayleighQuotient
  have h1 : (l1 ^ 2 * d0 + l0 ^ 2 * d1) / (l0 ^ 2 + l1 ^ 2) / d1 =
      ((l1 ^ 2 * d0 + l0 ^ 2 * d1) / d1) / (l0 ^ 2 + l1 ^ 2) := div_right_comm _ _ _
  rw [h1, add_div, mul_div_cancel_right₀ (l0 ^ 2) hd1, mul_div_assoc]

/-- Limit of the rescaled two-mode Rayleigh quotient under coordinate convergence
and eigenvalue separation `d₀/d₁ → 0`. -/
theorem tendsto_twoModeRayleighQuotient_div_d1
    {ι : Type*} {L : Filter ι}
    {d0 d1 l0 l1 : ι → ℝ} {L0 L1 : ℝ}
    (hl0 : Tendsto l0 L (𝓝 L0))
    (hl1 : Tendsto l1 L (𝓝 L1))
    (hL0 : L0 ≠ 0)
    (hd1 : ∀ᶠ i in L, d1 i ≠ 0)
    (hd_ratio : Tendsto (fun i => d0 i / d1 i) L (𝓝 0)) :
    Tendsto (fun i => twoModeRayleighQuotient (d0 i) (d1 i) (l0 i) (l1 i) / d1 i)
      L (𝓝 (L0 ^ 2 / (L0 ^ 2 + L1 ^ 2))) := by
  have hden_ne : L0 ^ 2 + L1 ^ 2 ≠ 0 := by
    have : 0 < L0 ^ 2 := sq_pos_of_ne_zero hL0
    have : 0 ≤ L1 ^ 2 := sq_nonneg L1
    positivity
  have hnum : Tendsto (fun i => l1 i ^ 2 * (d0 i / d1 i) + l0 i ^ 2)
      L (𝓝 (L1 ^ 2 * 0 + L0 ^ 2)) := by
    exact (hl1.pow 2).mul hd_ratio |>.add (hl0.pow 2)
  simp only [mul_zero, zero_add] at hnum
  have hden : Tendsto (fun i => l0 i ^ 2 + l1 i ^ 2)
      L (𝓝 (L0 ^ 2 + L1 ^ 2)) :=
    (hl0.pow 2).add (hl1.pow 2)
  have hlim := hnum.div hden hden_ne
  refine hlim.congr' ?_
  filter_upwards [hd1] with i hdi
  exact (twoModeRayleighQuotient_div_d1_eq (d0 i) (d1 i) (l0 i) (l1 i) hdi).symm

/-- Limit of the rescaled two-mode spectral gap `(d₁ - ℛ) / d₁` under coordinate convergence
and eigenvalue separation `d₀/d₁ → 0`. -/
theorem tendsto_twoModeRayleighQuotient_gap_ratio
    {ι : Type*} {L : Filter ι}
    {d0 d1 l0 l1 : ι → ℝ} {L0 L1 : ℝ}
    (hl0 : Tendsto l0 L (𝓝 L0))
    (hl1 : Tendsto l1 L (𝓝 L1))
    (hL0 : L0 ≠ 0)
    (hd1 : ∀ᶠ i in L, d1 i ≠ 0)
    (hd_ratio : Tendsto (fun i => d0 i / d1 i) L (𝓝 0)) :
    Tendsto (fun i => (d1 i - twoModeRayleighQuotient (d0 i) (d1 i) (l0 i) (l1 i)) / d1 i)
      L (𝓝 (1 - L0 ^ 2 / (L0 ^ 2 + L1 ^ 2))) := by
  have hlim := tendsto_twoModeRayleighQuotient_div_d1 hl0 hl1 hL0 hd1 hd_ratio
  have hsub : Tendsto (fun i => 1 - twoModeRayleighQuotient (d0 i) (d1 i) (l0 i) (l1 i) / d1 i)
      L (𝓝 (1 - L0 ^ 2 / (L0 ^ 2 + L1 ^ 2))) :=
    (tendsto_const_nhds.sub hlim)
  refine hsub.congr' ?_
  filter_upwards [hd1] with i hdi
  simp only [sub_div, div_self hdi]

open _root_.RHTower

/-- In the positive sector, the limiting ratio `L₀² / (L₀² + L₁²)` for Hermite coordinates
`L₀ = h₀(0)` and `L₁ = h₄(0)` evaluates to `8/11`. -/
theorem positiveSector_twoModeRayleigh_limit_eq_eight_elevenths :
    hermiteOriginSq 0 / (hermiteOriginSq 0 + hermiteOriginSq 2) = 8 / 11 :=
  positive_sector_hermite_floor_ratio_eq

/-- The positive sector spectral gap ratio converges to `3/11`. -/
theorem positiveSector_twoModeRayleigh_gap_limit_eq_three_elevenths :
    1 - (8 : ℝ) / 11 = 3 / 11 := by
  norm_num

/-- In the negative sector, the limiting ratio `L₀² / (L₀² + L₁²)` for Hermite coordinates
`L₀ = h₂(0)` and `L₁ = h₆(0)` evaluates to `8/13`. -/
theorem negativeSector_twoModeRayleigh_limit_eq_eight_thirteenths :
    hermiteOriginSq 1 / (hermiteOriginSq 1 + hermiteOriginSq 3) = 8 / 13 :=
  negative_sector_hermite_floor_ratio_eq

/-- The negative sector spectral gap ratio converges to `5/13`. -/
theorem negativeSector_twoModeRayleigh_gap_limit_eq_five_thirteenths :
    1 - (8 : ℝ) / 13 = 5 / 13 := by
  norm_num

/-- The ratio of positive-to-negative sector floor weights evaluates to `13/11`. -/
theorem parityFloor_twoModeRayleigh_ratio_eq_thirteen_elevenths :
    (hermiteOriginSq 0 / (hermiteOriginSq 0 + hermiteOriginSq 2)) /
      (hermiteOriginSq 1 / (hermiteOriginSq 1 + hermiteOriginSq 3)) = 13 / 11 :=
  parity_floor_weight_ratio_eq

/-- The numerical ratio of positive-to-negative sector floor fractions evaluates to `13/11`. -/
theorem parityFloor_numerical_ratio_eq_thirteen_elevenths :
    ((8 : ℝ) / 11) / ((8 : ℝ) / 13) = 13 / 11 := by
  norm_num

end

end GaloisForLFunctions.RHTower
