import GaloisForLFunctions.TransThresholdPairCorrelation.FejerWeightedPrimeMeanSquare
import GaloisForLFunctions.RHTower.ZetaWeightedGramIntegral
import Zeta23.PrimeSideA.EndsE1

/-!
# The Grid Kernel of a Smooth Height Weight

For grid weights `W_k = W(τ_k)` sampled from a weight `0 ≤ W ≤ 1` on the grid `τ_k = T + kh`, the
weighted kernel `K_W(τ,τ') = Σ_{k<d} W(τ_k) φ̂(τ−τ_k) φ̂(τ'−τ_k)` differs from `W(τ)·K(τ,τ')`
(`K` the unweighted grid kernel) by
`Σ_k (W(τ_k) − W(τ)) φ̂(τ−τ_k) φ̂(τ'−τ_k)` (`KfunW_sub_mul_Kfun_eq`). With `|φ̂(r)| ≤ A/(1 + r²)`,
`A = L + c_ϱ/w`, and a Lipschitz weight, every coefficient is at most `min(ℓ|τ_k − τ|, 1)`.

The grid sums are controlled by one averaging lemma (`sum_grid_le_integral`): a profile that is
locally comparable on cells of length `h` sums to at most `C/h` times its integral. For Lorentz
profiles of width `1/c` this gives `Σ_{k<n} (1 + c²(x − τ_k)²)⁻¹ ≤ 4π/(ch)`
(`sum_lor_grid_le`), and the Lipschitz-weighted sums cost only `√ℓ`
(`min_mul_lor1_le`: `min(ℓ|r|, 1)/(1 + r²) ≤ 2ℓ/(1 + ℓr²)`).
-/

open MeasureTheory Real Set Finset Filter
open scoped BigOperators ArithmeticFunction
open Zeta23 Zeta23.PrimeSide RHTower

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-! ## 1. Lorentz profiles -/

/-- The unit Lorentz profile `(1 + r²)⁻¹`. -/
def lor1 (r : ℝ) : ℝ := (1 + r ^ 2)⁻¹

theorem lor1_pos (r : ℝ) : 0 < lor1 r := by unfold lor1; positivity

theorem lor1_le_one (r : ℝ) : lor1 r ≤ 1 := by
  unfold lor1; exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg r])

theorem lor1_neg (r : ℝ) : lor1 (-r) = lor1 r := by unfold lor1; rw [neg_sq]

theorem continuous_lor1 : Continuous lor1 := by
  unfold lor1
  exact (continuous_const.add (continuous_pow 2)).inv₀ fun r =>
    (add_pos_of_pos_of_nonneg one_pos (sq_nonneg r)).ne'

theorem integrable_lor1 : Integrable lor1 := integrable_inv_one_add_sq

theorem integral_lor1 : ∫ r, lor1 r = π := integral_univ_inv_one_add_sq

/-- `lor1` is antitone in `|r|`. -/
theorem lor1_le_lor1_of_abs_le {a b : ℝ} (h : |a| ≤ |b|) : lor1 b ≤ lor1 a := by
  unfold lor1
  refine inv_anti₀ (by positivity) ?_
  have : a ^ 2 ≤ b ^ 2 := by rw [← sq_abs a, ← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg a) h 2
  linarith

/-- Local comparability: `lor1 a ≤ 4 lor1 b` when `|a − b| ≤ 1/2`. -/
theorem lor1_le_four_mul {a b : ℝ} (hab : |a - b| ≤ 1 / 2) : lor1 a ≤ 4 * lor1 b := by
  unfold lor1
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity)]
  have hb : |b| ≤ |a| + 1 / 2 := by
    have := abs_sub_abs_le_abs_sub b a; rw [abs_sub_comm] at this; linarith
  have h2 : b ^ 2 ≤ (|a| + 1 / 2) ^ 2 := by
    rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg b) hb 2
  nlinarith [sq_abs a, abs_nonneg a, sq_nonneg (|a| - 1 / 6)]

/-- `min(ℓ|r|, 1)/(1 + r²) ≤ 2ℓ/(1 + ℓr²)` for `0 < ℓ`. -/
theorem min_mul_lor1_le {ℓ : ℝ} (hℓ : 0 < ℓ) (r : ℝ) :
    min (ℓ * |r|) 1 * lor1 r ≤ 2 * ℓ * lor1 (Real.sqrt ℓ * r) := by
  have hs : Real.sqrt ℓ ^ 2 = ℓ := Real.sq_sqrt hℓ.le
  unfold lor1
  rw [mul_pow, hs]
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  rcases le_total (ℓ * r ^ 2) 1 with h | h
  · -- inner region: `min ≤ ℓ|r| ≤ ℓ(1 + r²)/2`
    have h1 : min (ℓ * |r|) 1 ≤ ℓ * |r| := min_le_left _ _
    have h2 : |r| ≤ (1 + r ^ 2) / 2 := by nlinarith [sq_abs r, sq_nonneg (|r| - 1)]
    have h3 : 0 ≤ min (ℓ * |r|) 1 := le_min (by positivity) zero_le_one
    nlinarith [mul_le_mul_of_nonneg_left h2 hℓ.le]
  · -- outer region: `min ≤ 1` and `1 + ℓr² ≤ 2ℓr² ≤ 2ℓ(1 + r²)`
    have h1 : min (ℓ * |r|) 1 ≤ 1 := min_le_right _ _
    have h3 : 0 ≤ min (ℓ * |r|) 1 := le_min (by positivity) zero_le_one
    nlinarith

/-! ## 2. Grid sums by cell averaging -/

/-- **Cell averaging.** If `g(x − t) ≤ C g(x − s)` whenever `|s − t| ≤ h/2`, then the grid sum
over `t₀ + kh`, `k < n`, is at most `C/h` times the integral over the union of the cells. -/
theorem sum_grid_le_integral {g : ℝ → ℝ} (hg : Continuous g) {C h t₀ x : ℝ} (hh : 0 < h)
    (hloc : ∀ t s, |s - t| ≤ h / 2 → g (x - t) ≤ C * g (x - s)) (n : ℕ) :
    ∑ k ∈ Finset.range n, g (x - (t₀ + k * h))
      ≤ (C / h) * ∫ s in (t₀ - h / 2)..(t₀ + n * h - h / 2), g (x - s) := by
  set a : ℕ → ℝ := fun k => t₀ + k * h - h / 2 with ha
  have hgc : Continuous fun s => C * g (x - s) := continuous_const.mul (hg.comp (by fun_prop))
  have hcell : ∀ k : ℕ, g (x - (t₀ + k * h)) ≤ (1 / h) * ∫ s in a k..a (k + 1), C * g (x - s) := by
    intro k
    have hlen : a k ≤ a (k + 1) := by simp only [ha]; push_cast; linarith
    have hmono : ∫ s in a k..a (k + 1), g (x - (t₀ + k * h)) ≤ ∫ s in a k..a (k + 1), C * g (x - s) :=
      intervalIntegral.integral_mono_on hlen intervalIntegrable_const (hgc.intervalIntegrable _ _)
        fun s hs => hloc _ _ (by
          simp only [ha] at hs; push_cast at hs
          rw [abs_le]; constructor <;> linarith [hs.1, hs.2])
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have e : a (k + 1) - a k = h := by simp only [ha]; push_cast; ring
    rw [e] at hmono
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hh, mul_comm]
    exact hmono
  calc ∑ k ∈ Finset.range n, g (x - (t₀ + k * h))
      ≤ ∑ k ∈ Finset.range n, (1 / h) * ∫ s in a k..a (k + 1), C * g (x - s) :=
        Finset.sum_le_sum fun k _ => hcell k
    _ = (1 / h) * ∫ s in a 0..a n, C * g (x - s) := by
        rw [← Finset.mul_sum, intervalIntegral.sum_integral_adjacent_intervals
          fun k _ => hgc.intervalIntegrable _ _]
    _ = (C / h) * ∫ s in (t₀ - h / 2)..(t₀ + n * h - h / 2), g (x - s) := by
        rw [intervalIntegral.integral_const_mul]; simp only [ha]; push_cast
        rw [zero_mul, add_zero]; ring

/-- **Lorentz grid sums.** For `0 < c ≤ 1` and `0 < h ≤ 1`:
`Σ_{k<n} (1 + c²(x − (t₀ + kh))²)⁻¹ ≤ 4π/(ch)`. -/
theorem sum_lor_grid_le {c h : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (t₀ x : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range n, lor1 (c * (x - (t₀ + k * h))) ≤ 4 * π / (c * h) := by
  have hgc : Continuous fun r => lor1 (c * r) := continuous_lor1.comp (continuous_const.mul continuous_id)
  have h1 := sum_grid_le_integral (g := fun r => lor1 (c * r)) hgc (C := 4) (t₀ := t₀) (x := x) hh
    (fun t s hts => lor1_le_four_mul (by
      rw [← mul_sub, abs_mul, abs_of_pos hc]
      calc c * |x - t - (x - s)| = c * |s - t| := by congr 1; ring_nf
        _ ≤ 1 * (h / 2) := mul_le_mul hc1 hts (abs_nonneg _) zero_le_one
        _ ≤ 1 / 2 := by linarith)) n
  refine h1.trans ?_
  have hint : Integrable fun s => lor1 (c * (x - s)) := by
    have := (integrable_lor1.comp_mul_left' hc.ne').comp_sub_left x
    simpa [Function.comp] using this
  have hle : (∫ s in (t₀ - h / 2)..(t₀ + n * h - h / 2), lor1 (c * (x - s))) ≤ π / c := by
    have hab : t₀ - h / 2 ≤ t₀ + n * h - h / 2 := by
      have : (0 : ℝ) ≤ n * h := by positivity
      linarith
    rw [intervalIntegral.integral_of_le hab]
    refine (setIntegral_le_integral hint (Eventually.of_forall fun s => (lor1_pos _).le)).trans
      (le_of_eq ?_)
    rw [integral_sub_left_eq_self (fun r => lor1 (c * r)) (μ := volume) x]
    have := Measure.integral_comp_mul_left (fun r => lor1 r) c
    rw [this, integral_lor1, smul_eq_mul, abs_of_pos (inv_pos.mpr hc)]
    field_simp
  calc 4 / h * ∫ s in (t₀ - h / 2)..(t₀ + n * h - h / 2), lor1 (c * (x - s))
      ≤ 4 / h * (π / c) := mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 4 * π / (c * h) := by field_simp

/-- Far from all grid points every term is at most `lor1(D)`. -/
theorem sum_lor1_grid_le_far {D t₀ h x : ℝ} {n : ℕ}
    (hD : ∀ k < n, D ≤ |x - (t₀ + k * h)|) (hD0 : 0 ≤ D) :
    ∑ k ∈ Finset.range n, lor1 (x - (t₀ + k * h)) ≤ n * lor1 D := by
  calc ∑ k ∈ Finset.range n, lor1 (x - (t₀ + k * h)) ≤ ∑ _k ∈ Finset.range n, lor1 D :=
        Finset.sum_le_sum fun k hk => lor1_le_lor1_of_abs_le (by
          rw [abs_of_nonneg hD0]; exact hD k (Finset.mem_range.mp hk))
    _ = n * lor1 D := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ## 3. The weight and the exact kernel identity -/

/-- A height weight: values in `[0, 1]`, Lipschitz with constant `ℓ`. -/
structure HeightWeight (ℓ : ℝ) (W : ℝ → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ W s
  le_one : ∀ s, W s ≤ 1
  lipschitz : ∀ s t, |W s - W t| ≤ ℓ * |s - t|

theorem HeightWeight.abs_sub_le_min {ℓ : ℝ} {W : ℝ → ℝ} (hW : HeightWeight ℓ W) (s t : ℝ) :
    |W s - W t| ≤ min (ℓ * |s - t|) 1 :=
  le_min (hW.lipschitz s t) (abs_sub_le_iff.mpr
    ⟨by linarith [hW.le_one s, hW.nonneg t], by linarith [hW.le_one t, hW.nonneg s]⟩)

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- Grid weights sampled from a height weight. -/
def gridW (p : Setting) (W : ℝ → ℝ) : Fin p.d → ℝ := fun k => W (p.tau k)

/-- **The exact kernel identity.** `K_W − W(τ)K = Σ_k (W(τ_k) − W(τ)) φ̂(τ − τ_k) φ̂(τ' − τ_k)`. -/
theorem KfunW_sub_mul_Kfun_eq (W : ℝ → ℝ) (τ τ' : ℝ) :
    KfunW p F (gridW p W) τ τ' - W τ * Kfun p F τ τ'
      = ∑ k : Fin p.d, (W (p.tau k) - W τ) * (F.phiHat (τ - p.tau k) * F.phiHat (τ' - p.tau k)) := by
  unfold KfunW Kfun gridW
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- `|φ̂(r)| ≤ A lor1(r)` with `A = L + c_ϱ/w`. -/
theorem abs_phiHat_le_lor1 (hF : LocalHypsCoreW cϱ p F) (r : ℝ) :
    |F.phiHat r| ≤ (p.L + cϱ / p.w) * lor1 r := by
  have h := abs_phiHat_mul_one_add_sq_le hF r
  unfold lor1
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact h

/-- `Σ_k |φ̂(τ − τ_k)| |φ̂(τ' − τ_k)| ≤ L²` (Cauchy–Schwarz and the Poisson diagonal). -/
theorem sum_abs_phiHat_mul_le (hF : LocalHypsCoreW cϱ p F) (τ τ' : ℝ) :
    ∑ k : Fin p.d, |F.phiHat (τ - p.tau k)| * |F.phiHat (τ' - p.tau k)| ≤ p.L ^ 2 := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k : Fin p.d => |F.phiHat (τ - p.tau k)|) (fun k : Fin p.d => |F.phiHat (τ' - p.tau k)|)
  have hbound : ∀ σ : ℝ, ∑ k : Fin p.d, |F.phiHat (σ - p.tau k)| ^ 2 ≤ p.L ^ 2 := by
    intro σ
    have h0 := rho_nonneg hF σ
    unfold rho at h0
    have ha := hF.a_le_one
    have hL := hF.L_pos
    simp only [sq_abs]
    nlinarith [sq_nonneg p.L]
  have hS0 : 0 ≤ ∑ k : Fin p.d, |F.phiHat (τ - p.tau k)| * |F.phiHat (τ' - p.tau k)| :=
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h1 := hbound τ
  have h2 := hbound τ'
  have hsq : (∑ k : Fin p.d, |F.phiHat (τ - p.tau k)| * |F.phiHat (τ' - p.tau k)|) ^ 2
      ≤ (p.L ^ 2) ^ 2 := by
    refine hCS.trans ?_
    rw [sq]
    exact mul_le_mul h1 h2 (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
  nlinarith [sq_nonneg p.L, sq_nonneg (∑ k : Fin p.d, |F.phiHat (τ - p.tau k)|
    * |F.phiHat (τ' - p.tau k)| - p.L ^ 2)]

theorem abs_KfunW_le (hF : LocalHypsCoreW cϱ p F) {ℓ : ℝ} {W : ℝ → ℝ} (hW : HeightWeight ℓ W)
    (τ τ' : ℝ) : |KfunW p F (gridW p W) τ τ'| ≤ p.L ^ 2 := by
  refine le_trans ?_ (sum_abs_phiHat_mul_le hF τ τ')
  unfold KfunW gridW
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul, abs_of_nonneg (hW.nonneg _)]
  exact mul_le_of_le_one_left (by positivity) (hW.le_one _)

/-- The Lipschitz cell weight `m_k(τ) = min(ℓ|τ − τ_k|, 1) lor1(τ − τ_k)`. -/
def cellW (p : Setting) (ℓ : ℝ) (k : Fin p.d) (τ : ℝ) : ℝ :=
  min (ℓ * |τ - p.tau k|) 1 * lor1 (τ - p.tau k)

theorem cellW_nonneg {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (k : Fin p.d) (τ : ℝ) : 0 ≤ cellW p ℓ k τ :=
  mul_nonneg (le_min (by positivity) zero_le_one) (lor1_pos _).le

theorem cellW_le_lor1 {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (k : Fin p.d) (τ : ℝ) :
    cellW p ℓ k τ ≤ lor1 (τ - p.tau k) :=
  mul_le_of_le_one_left (lor1_pos _).le (min_le_right _ _)

theorem continuous_cellW (ℓ : ℝ) (k : Fin p.d) : Continuous (cellW p ℓ k) := by
  unfold cellW
  exact ((continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))).min
    continuous_const).mul (continuous_lor1.comp (continuous_id.sub continuous_const))

/-- **Pointwise error of the weighted kernel.**
`|K_W − W(τ)K| ≤ A² Σ_k m_k(τ) lor1(τ' − τ_k)`. -/
theorem abs_KfunW_sub_mul_Kfun_le (hF : LocalHypsCoreW cϱ p F) {ℓ : ℝ} {W : ℝ → ℝ}
    (hW : HeightWeight ℓ W) (τ τ' : ℝ) :
    |KfunW p F (gridW p W) τ τ' - W τ * Kfun p F τ τ'|
      ≤ (p.L + cϱ / p.w) ^ 2 * ∑ k : Fin p.d, cellW p ℓ k τ * lor1 (τ' - p.tau k) := by
  rw [KfunW_sub_mul_Kfun_eq, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul, abs_mul]
  have h1 : |W (p.tau k) - W τ| ≤ min (ℓ * |τ - p.tau k|) 1 := by
    rw [abs_sub_comm (τ) (p.tau k)]; exact hW.abs_sub_le_min _ _
  have h2 := abs_phiHat_le_lor1 hF (τ - p.tau k)
  have h3 := abs_phiHat_le_lor1 hF (τ' - p.tau k)
  unfold cellW
  have hA : 0 ≤ p.L + cϱ / p.w := by
    have := hF.L_pos; have := hF.four_le_cϱ; have := hF.one_le_w; positivity
  calc |W (p.tau k) - W τ| * (|F.phiHat (τ - p.tau k)| * |F.phiHat (τ' - p.tau k)|)
      ≤ min (ℓ * |τ - p.tau k|) 1 * (((p.L + cϱ / p.w) * lor1 (τ - p.tau k))
          * ((p.L + cϱ / p.w) * lor1 (τ' - p.tau k))) :=
        mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) (by have := lor1_pos (τ - p.tau k); positivity))
          (by positivity) (le_trans (abs_nonneg _) h1)
    _ = (p.L + cϱ / p.w) ^ 2 * (min (ℓ * |τ - p.tau k|) 1 * lor1 (τ - p.tau k)
          * lor1 (τ' - p.tau k)) := by ring

/-! ## 4. The first double-integral comparison -/

/-- Mass of a cell weight: `∫ m_k ≤ 2π√ℓ`. -/
theorem integral_cellW_le {ℓ : ℝ} (hℓ : 0 < ℓ) (k : Fin p.d) :
    ∫ τ, cellW p ℓ k τ ≤ 2 * π * Real.sqrt ℓ := by
  have hsl : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  have hmaj : Integrable fun τ => 2 * ℓ * lor1 (Real.sqrt ℓ * (τ - p.tau k)) := by
    have := ((integrable_lor1.comp_mul_left' hsl.ne').comp_sub_right (p.tau k)).const_mul (2 * ℓ)
    simpa [Function.comp] using this
  have hcell : Integrable (cellW p ℓ k) :=
    (integrable_lor1.comp_sub_right (p.tau k)).mono' (continuous_cellW ℓ k).aestronglyMeasurable
      (Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cellW_nonneg hℓ.le k τ)]
        exact cellW_le_lor1 hℓ.le k τ)
  calc ∫ τ, cellW p ℓ k τ ≤ ∫ τ, 2 * ℓ * lor1 (Real.sqrt ℓ * (τ - p.tau k)) :=
        integral_mono hcell hmaj fun τ => min_mul_lor1_le hℓ (τ - p.tau k)
    _ = 2 * π * Real.sqrt ℓ := by
        rw [integral_const_mul, integral_sub_right_eq_self (fun r => lor1 (Real.sqrt ℓ * r)) (p.tau k),
          Measure.integral_comp_mul_left (fun r => lor1 r) (Real.sqrt ℓ), integral_lor1, smul_eq_mul,
          abs_of_pos (inv_pos.mpr hsl)]
        have hs2 : Real.sqrt ℓ * Real.sqrt ℓ = ℓ := Real.mul_self_sqrt hℓ.le
        field_simp
        nlinarith [hs2]

/-- **Comparison of the weighted Frobenius integrand with the window-weighted unweighted one.**
For a height weight `W` and a density `ν` with `lor1(· − a) ν²` integrable,
`|∬ (K_W² − W(τ)²K²) ν ν'| ≤ L²A² (π ∫ ν² Σ_k m_k + 2π√ℓ ∫ ν² Σ_k lor1(· − τ_k))`. -/
theorem abs_integral_KfunW_sq_sub_le (hF : LocalHypsCoreW cϱ p F) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {W : ℝ → ℝ} (hW : HeightWeight ℓ W) {ν : ℝ → ℝ} (hνc : Continuous ν)
    (hνi : ∀ a : ℝ, Integrable fun τ => lor1 (τ - a) * ν τ ^ 2) :
    |∫ q : ℝ × ℝ, (KfunW p F (gridW p W) q.1 q.2 ^ 2 - W q.1 ^ 2 * Kfun p F q.1 q.2 ^ 2)
        * ν q.1 * ν q.2|
      ≤ p.L ^ 2 * (p.L + cϱ / p.w) ^ 2
        * (π * ∫ τ, ν τ ^ 2 * ∑ k : Fin p.d, cellW p ℓ k τ
          + 2 * π * Real.sqrt ℓ * ∫ τ, ν τ ^ 2 * ∑ k : Fin p.d, lor1 (τ - p.tau k)) := by
  set A := p.L + cϱ / p.w with hA
  have hA0 : 0 ≤ A := by
    have := hF.L_pos; have := hF.four_le_cϱ; have := hF.one_le_w; positivity
  have hL := hF.L_pos
  -- integrability of the one-variable pieces
  have hcellν : ∀ k : Fin p.d, Integrable fun τ => cellW p ℓ k τ * ν τ ^ 2 := fun k =>
    (hνi (p.tau k)).mono' ((continuous_cellW ℓ k).mul (hνc.pow 2)).aestronglyMeasurable
      (Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (cellW_nonneg hℓ.le k τ) (sq_nonneg _))]
        exact mul_le_mul_of_nonneg_right (cellW_le_lor1 hℓ.le k τ) (sq_nonneg _))
  have hcell : ∀ k : Fin p.d, Integrable (cellW p ℓ k) := fun k =>
    (integrable_lor1.comp_sub_right (p.tau k)).mono' (continuous_cellW ℓ k).aestronglyMeasurable
      (Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cellW_nonneg hℓ.le k τ)]
        exact cellW_le_lor1 hℓ.le k τ)
  have hlork : ∀ k : Fin p.d, Integrable fun τ => lor1 (τ - p.tau k) := fun k =>
    integrable_lor1.comp_sub_right (p.tau k)
  -- the product majorant
  set M : ℝ × ℝ → ℝ := fun q => p.L ^ 2 * A ^ 2 * ∑ k : Fin p.d,
      (cellW p ℓ k q.1 * ν q.1 ^ 2 * lor1 (q.2 - p.tau k)
        + cellW p ℓ k q.1 * (lor1 (q.2 - p.tau k) * ν q.2 ^ 2)) with hM
  have hMi : Integrable M := by
    refine (integrable_finsetSum _ fun k _ => ?_).const_mul _
    exact ((hcellν k).mul_prod (hlork k)).add ((hcell k).mul_prod (hνi (p.tau k)))
  have hpt : ∀ q : ℝ × ℝ, ‖(KfunW p F (gridW p W) q.1 q.2 ^ 2 - W q.1 ^ 2 * Kfun p F q.1 q.2 ^ 2)
      * ν q.1 * ν q.2‖ ≤ M q := by
    intro q
    rw [Real.norm_eq_abs]
    have hfac : KfunW p F (gridW p W) q.1 q.2 ^ 2 - W q.1 ^ 2 * Kfun p F q.1 q.2 ^ 2
        = (KfunW p F (gridW p W) q.1 q.2 - W q.1 * Kfun p F q.1 q.2)
          * (KfunW p F (gridW p W) q.1 q.2 + W q.1 * Kfun p F q.1 q.2) := by ring
    have hsum : |KfunW p F (gridW p W) q.1 q.2 + W q.1 * Kfun p F q.1 q.2| ≤ 2 * p.L ^ 2 := by
      have h1 := abs_KfunW_le hF hW q.1 q.2
      have h2 := abs_Kfun_le hF q.1 q.2
      rw [abs_mul, abs_of_nonneg (hW.nonneg _)] at *
      calc |KfunW p F (gridW p W) q.1 q.2 + W q.1 * Kfun p F q.1 q.2|
          ≤ |KfunW p F (gridW p W) q.1 q.2| + |W q.1 * Kfun p F q.1 q.2| := abs_add_le _ _
        _ ≤ p.L ^ 2 + 1 * p.L ^ 2 := by
            rw [abs_mul, abs_of_nonneg (hW.nonneg _)]
            exact add_le_add h1 (mul_le_mul (hW.le_one _) h2 (abs_nonneg _) zero_le_one)
        _ = 2 * p.L ^ 2 := by ring
    have hdiff := abs_KfunW_sub_mul_Kfun_le hF hW q.1 q.2
    rw [hfac, abs_mul, abs_mul, abs_mul]
    have hνν : |ν q.1| * |ν q.2| ≤ (ν q.1 ^ 2 + ν q.2 ^ 2) / 2 := by
      nlinarith [sq_nonneg (|ν q.1| - |ν q.2|), sq_abs (ν q.1), sq_abs (ν q.2)]
    have hS0 : 0 ≤ ∑ k : Fin p.d, cellW p ℓ k q.1 * lor1 (q.2 - p.tau k) :=
      Finset.sum_nonneg fun k _ => mul_nonneg (cellW_nonneg hℓ.le k _) (lor1_pos _).le
    calc |KfunW p F (gridW p W) q.1 q.2 - W q.1 * Kfun p F q.1 q.2|
          * |KfunW p F (gridW p W) q.1 q.2 + W q.1 * Kfun p F q.1 q.2| * |ν q.1| * |ν q.2|
        ≤ (A ^ 2 * ∑ k : Fin p.d, cellW p ℓ k q.1 * lor1 (q.2 - p.tau k)) * (2 * p.L ^ 2)
            * ((ν q.1 ^ 2 + ν q.2 ^ 2) / 2) := by
          rw [mul_assoc _ (|ν q.1|)]
          exact mul_le_mul (mul_le_mul hdiff hsum (abs_nonneg _) (by positivity)) hνν
            (by positivity) (by positivity)
      _ = M q := by
          rw [hM]; simp only
          rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  have hint := norm_integral_le_of_norm_le hMi (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs] at hint
  refine hint.trans ?_
  have hlor_int : ∀ k : Fin p.d, ∫ τ, lor1 (τ - p.tau k) = π := fun k => by
    rw [integral_sub_right_eq_self (fun r => lor1 r) (p.tau k), integral_lor1]
  have hcalc : ∫ q, M q = p.L ^ 2 * A ^ 2 * ∑ k : Fin p.d,
      (π * ∫ τ, cellW p ℓ k τ * ν τ ^ 2
        + (∫ τ, cellW p ℓ k τ) * ∫ τ, lor1 (τ - p.tau k) * ν τ ^ 2) := by
    rw [hM, integral_const_mul, integral_finsetSum _ fun k _ =>
      ((hcellν k).mul_prod (hlork k)).add ((hcell k).mul_prod (hνi (p.tau k)))]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_add ((hcellν k).mul_prod (hlork k)) ((hcell k).mul_prod (hνi (p.tau k))),
      integral_prod_mul (fun τ => cellW p ℓ k τ * ν τ ^ 2) (fun τ => lor1 (τ - p.tau k)),
      integral_prod_mul (fun τ => cellW p ℓ k τ) (fun τ => lor1 (τ - p.tau k) * ν τ ^ 2),
      hlor_int k]
    ring
  rw [hcalc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hterm : ∀ k : Fin p.d, π * (∫ τ, cellW p ℓ k τ * ν τ ^ 2)
      + (∫ τ, cellW p ℓ k τ) * ∫ τ, lor1 (τ - p.tau k) * ν τ ^ 2
      ≤ π * (∫ τ, cellW p ℓ k τ * ν τ ^ 2)
        + 2 * π * Real.sqrt ℓ * ∫ τ, lor1 (τ - p.tau k) * ν τ ^ 2 := by
    intro k
    have hb : 0 ≤ ∫ τ, lor1 (τ - p.tau k) * ν τ ^ 2 :=
      integral_nonneg fun τ => mul_nonneg (lor1_pos _).le (sq_nonneg _)
    linarith [mul_le_mul_of_nonneg_right (integral_cellW_le hℓ k) hb]
  have e1 : ∫ τ, ν τ ^ 2 * ∑ k : Fin p.d, cellW p ℓ k τ
      = ∑ k : Fin p.d, ∫ τ, cellW p ℓ k τ * ν τ ^ 2 := by
    rw [← integral_finsetSum _ fun k _ => hcellν k]
    exact integral_congr_ae (Eventually.of_forall fun τ => by
      simp only [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring)
  have e2 : ∫ τ, ν τ ^ 2 * ∑ k : Fin p.d, lor1 (τ - p.tau k)
      = ∑ k : Fin p.d, ∫ τ, lor1 (τ - p.tau k) * ν τ ^ 2 := by
    rw [← integral_finsetSum _ fun k _ => hνi (p.tau k)]
    exact integral_congr_ae (Eventually.of_forall fun τ => by
      simp only [Finset.mul_sum, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring)
  rw [e1, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => hterm k

end GaloisForLFunctions.TransThresholdPairCorrelation
