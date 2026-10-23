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

theorem HeightWeight.continuous {ℓ : ℝ} {W : ℝ → ℝ} (hW : HeightWeight ℓ W) : Continuous W := by
  rw [Metric.continuous_iff]
  intro b ε hε
  refine ⟨ε / (|ℓ| + 1), by positivity, fun a hab => ?_⟩
  rw [Real.dist_eq] at hab ⊢
  calc |W a - W b| ≤ ℓ * |a - b| := hW.lipschitz a b
    _ ≤ (|ℓ| + 1) * |a - b| := mul_le_mul_of_nonneg_right (by linarith [le_abs_self ℓ]) (abs_nonneg _)
    _ < (|ℓ| + 1) * (ε / (|ℓ| + 1)) := mul_lt_mul_of_pos_left hab (by positivity)
    _ = ε := by field_simp

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

theorem cellW_le_lor1 (ℓ : ℝ) (k : Fin p.d) (τ : ℝ) :
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
        exact cellW_le_lor1 ℓ k τ)
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
        * (π * (∫ τ, ν τ ^ 2 * ∑ k : Fin p.d, cellW p ℓ k τ)
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
        exact mul_le_mul_of_nonneg_right (cellW_le_lor1 ℓ k τ) (sq_nonneg _))
  have hcell : ∀ k : Fin p.d, Integrable (cellW p ℓ k) := fun k =>
    (integrable_lor1.comp_sub_right (p.tau k)).mono' (continuous_cellW ℓ k).aestronglyMeasurable
      (Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cellW_nonneg hℓ.le k τ)]
        exact cellW_le_lor1 ℓ k τ)
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
          rw [hM]
          simp only [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
  have hint := norm_integral_le_of_norm_le hMi (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs] at hint
  refine hint.trans ?_
  have hlor_int : ∀ k : Fin p.d, ∫ τ, lor1 (τ - p.tau k) = π := fun k => by
    rw [integral_sub_right_eq_self (fun r => lor1 r) (p.tau k), integral_lor1]
  have hP1 : ∀ k : Fin p.d, Integrable (fun z : ℝ × ℝ =>
      cellW p ℓ k z.1 * ν z.1 ^ 2 * lor1 (z.2 - p.tau k)) := fun k =>
    (hcellν k).mul_prod (hlork k)
  have hP2 : ∀ k : Fin p.d, Integrable (fun z : ℝ × ℝ =>
      cellW p ℓ k z.1 * (lor1 (z.2 - p.tau k) * ν z.2 ^ 2)) := fun k =>
    (hcell k).mul_prod (hνi (p.tau k))
  have hP : ∀ k : Fin p.d, Integrable (fun z : ℝ × ℝ =>
      cellW p ℓ k z.1 * ν z.1 ^ 2 * lor1 (z.2 - p.tau k)
        + cellW p ℓ k z.1 * (lor1 (z.2 - p.tau k) * ν z.2 ^ 2)) := fun k => (hP1 k).add (hP2 k)
  have hcalc : ∫ q, M q = p.L ^ 2 * A ^ 2 * ∑ k : Fin p.d,
      (π * (∫ τ, cellW p ℓ k τ * ν τ ^ 2)
        + (∫ τ, cellW p ℓ k τ) * ∫ τ, lor1 (τ - p.tau k) * ν τ ^ 2) := by
    rw [hM, integral_const_mul, integral_finsetSum _ fun k _ => hP k]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_add (hP1 k) (hP2 k), Measure.volume_eq_prod,
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
    rw [← integral_finsetSum _ fun (k : Fin p.d) _ => hcellν k]
    exact integral_congr_ae (Eventually.of_forall fun τ => by
      simp only [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring)
  have e2 : ∫ τ, ν τ ^ 2 * ∑ k : Fin p.d, lor1 (τ - p.tau k)
      = ∑ k : Fin p.d, ∫ τ, lor1 (τ - p.tau k) * ν τ ^ 2 := by
    rw [← integral_finsetSum _ fun (k : Fin p.d) _ => hνi (p.tau k)]
    exact integral_congr_ae (Eventually.of_forall fun τ => by
      simp only [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring)
  rw [e1, e2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => hterm k

/-! ## 5. The second comparison: the grid kernel against the full lattice on the window -/

/-- `√|r|/(1 + r²)` is integrable (it is at most `(1 + r²)^{-3/4}`). -/
theorem integrable_lor1_mul_sqrt : Integrable fun r => lor1 r * Real.sqrt |r| := by
  have hI := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 3 / 2)
    (by simp; norm_num)
  refine hI.mono' ((continuous_lor1.mul continuous_abs.sqrt).aestronglyMeasurable)
    (Eventually.of_forall fun r => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (lor1_pos r).le (Real.sqrt_nonneg _)),
    Real.norm_eq_abs, sq_abs]
  set u := 1 + r ^ 2 with hu
  have hu1 : 1 ≤ u := by rw [hu]; nlinarith [sq_nonneg r]
  have hu0 : 0 < u := by linarith
  have hsq : Real.sqrt |r| ≤ u ^ (1 / 4 : ℝ) := by
    have h1 : |r| ≤ Real.sqrt u := Real.abs_le_sqrt (by rw [hu]; linarith)
    have h2 : Real.sqrt |r| ≤ Real.sqrt (Real.sqrt u) := Real.sqrt_le_sqrt h1
    have hq : Real.sqrt (Real.sqrt u) = u ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hu0.le]; norm_num
    exact h2.trans (le_of_eq hq)
  have hl : lor1 r = u ^ (-1 : ℝ) := by unfold lor1; rw [Real.rpow_neg_one, hu]
  rw [hl]
  calc u ^ (-1 : ℝ) * Real.sqrt |r| ≤ u ^ (-1 : ℝ) * u ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = u ^ (-(3 / 2 : ℝ) / 2) := by rw [← Real.rpow_add hu0]; norm_num

/-- `|K∞(τ,τ')| = L|Φ(τ − τ')| ≤ L A lor1(τ − τ')`. -/
theorem abs_Kinf_le_lor1 (hF : LocalHypsCoreW cϱ p F) (τ τ' : ℝ) :
    |Kinf p F τ τ'| ≤ p.L * ((p.L + cϱ / p.w) * lor1 (τ - τ')) := by
  unfold Kinf
  rw [abs_mul, abs_of_pos hF.L_pos]
  refine mul_le_mul_of_nonneg_left ?_ hF.L_pos.le
  have h1 := hF.Phi_le_L (τ - τ')
  have h2 := hF.Phi_le_sq (τ - τ')
  unfold lor1
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  nlinarith

/-- `|K(τ,τ')| ≤ A² Σ_k lor1(τ − τ_k) lor1(τ' − τ_k)`. -/
theorem abs_Kfun_le_lor1 (hF : LocalHypsCoreW cϱ p F) (τ τ' : ℝ) :
    |Kfun p F τ τ'|
      ≤ (p.L + cϱ / p.w) ^ 2 * ∑ k : Fin p.d, lor1 (τ - p.tau k) * lor1 (τ' - p.tau k) := by
  unfold Kfun
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  have h2 := abs_phiHat_le_lor1 hF (τ - p.tau k)
  have h3 := abs_phiHat_le_lor1 hF (τ' - p.tau k)
  calc |F.phiHat (τ - p.tau k)| * |F.phiHat (τ' - p.tau k)|
      ≤ ((p.L + cϱ / p.w) * lor1 (τ - p.tau k)) * ((p.L + cϱ / p.w) * lor1 (τ' - p.tau k)) :=
        mul_le_mul h2 h3 (abs_nonneg _) (le_trans (abs_nonneg _) h2)
    _ = (p.L + cϱ / p.w) ^ 2 * (lor1 (τ - p.tau k) * lor1 (τ' - p.tau k)) := by ring

/-- Deep inside the window the grid kernel equals the full-lattice kernel up to `L R₀`
whenever `ρ(τ) ≤ R₀²`. -/
theorem abs_Kinf_sub_Kfun_le_of_rho (hF : LocalHypsCoreW cϱ p F) {R₀ : ℝ} (hR₀ : 0 < R₀) {τ : ℝ}
    (hρ : rho p F τ ≤ R₀ ^ 2) (τ' : ℝ) :
    |Kinf p F τ τ' - Kfun p F τ τ'| ≤ p.L * R₀ := by
  have hL := hF.L_pos
  have h := abs_Kinf_sub_Kfun_le hF τ τ' (s := p.L / R₀) (by positivity)
  have hρ' : rho p F τ' ≤ p.L ^ 2 := by
    unfold rho
    have ha := hF.a_le_one
    have : 0 ≤ ∑ k : Fin p.d, F.phiHat (τ' - p.tau k) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith [sq_nonneg p.L]
  refine h.trans ?_
  have e1 : p.L / R₀ * rho p F τ ≤ p.L / R₀ * R₀ ^ 2 := mul_le_mul_of_nonneg_left hρ (by positivity)
  have e2 : rho p F τ' / (p.L / R₀) ≤ p.L ^ 2 / (p.L / R₀) :=
    div_le_div_of_nonneg_right hρ' (by positivity)
  have e3 : p.L / R₀ * R₀ ^ 2 = p.L * R₀ := by field_simp
  have e4 : p.L ^ 2 / (p.L / R₀) = p.L * R₀ := by field_simp
  linarith

/-- **Second comparison.** For a weight supported in `S = [s₀, s₁]` with `ρ ≤ R₀²` on `S`, and a
density with `|ν(τ')| ≤ B₁ + √|τ' − τ|` for `τ ∈ S`:
`|∬ W(τ)² (K² − K∞²) ν ν'| ≤ L R₀ B₁ (A² Σ_k π ∫ lor1(· − τ_k)|ν| + L A (s₁ − s₀) ∫ k)`,
`k(r) = lor1(r)(B₁ + √|r|)`. -/
theorem abs_integral_window_Kfun_sq_sub_le (hF : LocalHypsCoreW cϱ p F) {ℓ : ℝ} {W : ℝ → ℝ}
    (hW : HeightWeight ℓ W) {s₀ s₁ : ℝ} (hs : s₀ ≤ s₁) (hWS : ∀ τ, τ ∉ Icc s₀ s₁ → W τ = 0)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hρ : ∀ τ ∈ Icc s₀ s₁, rho p F τ ≤ R₀ ^ 2)
    {ν : ℝ → ℝ} {B₁ : ℝ} (hB₁ : 0 ≤ B₁)
    (hνS : ∀ τ ∈ Icc s₀ s₁, ∀ τ', |ν τ'| ≤ B₁ + Real.sqrt |τ' - τ|)
    (hνi : ∀ a : ℝ, Integrable fun τ => lor1 (τ - a) * |ν τ|) :
    |∫ q : ℝ × ℝ, W q.1 ^ 2 * (Kfun p F q.1 q.2 ^ 2 - Kinf p F q.1 q.2 ^ 2) * ν q.1 * ν q.2|
      ≤ p.L * R₀ * B₁ * ((p.L + cϱ / p.w) ^ 2
          * (∑ k : Fin p.d, π * ∫ τ, lor1 (τ - p.tau k) * |ν τ|)
        + p.L * (p.L + cϱ / p.w) * (s₁ - s₀) * ∫ r, lor1 r * (B₁ + Real.sqrt |r|)) := by
  set A := p.L + cϱ / p.w with hA
  have hA0 : 0 ≤ A := by
    have := hF.L_pos; have := hF.four_le_cϱ; have := hF.one_le_w; positivity
  have hL := hF.L_pos
  have hWc : ∀ τ, W τ ^ 2 ≤ 1 := fun τ => by
    have := hW.nonneg τ; have := hW.le_one τ; nlinarith
  -- the convolution kernel
  set kk : ℝ → ℝ := fun r => lor1 r * (B₁ + Real.sqrt |r|) with hkk
  have hkint : Integrable kk := by
    have h := (integrable_lor1.mul_const B₁).add integrable_lor1_mul_sqrt
    refine h.congr (Eventually.of_forall fun r => ?_); simp only [hkk, Pi.add_apply]; ring
  have hkc : Continuous kk := continuous_lor1.mul (continuous_const.add continuous_abs.sqrt)
  have hk0 : ∀ r, 0 ≤ kk r := fun r => mul_nonneg (lor1_pos r).le (by positivity)
  -- `W²` is integrable (bounded, continuous, supported in `S`)
  have hWc' : Continuous fun τ => W τ ^ 2 := hW.continuous.pow 2
  have hW2 : Integrable fun τ => W τ ^ 2 :=
    hWc'.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_Icc (a := s₀) (b := s₁))
      fun x (hx : x ∉ Icc s₀ s₁) => by simp only [hWS x hx]; ring)
  have hW2lor : ∀ k : Fin p.d, Integrable fun τ => W τ ^ 2 * lor1 (τ - p.tau k) := fun k =>
    (integrable_lor1.comp_sub_right (p.tau k)).mono' (hWc'.mul (continuous_lor1.comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable (Eventually.of_forall fun τ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (lor1_pos _).le)]
        exact mul_le_of_le_one_left (lor1_pos _).le (hWc τ))
  -- the majorant
  set M : ℝ × ℝ → ℝ := fun q => p.L * R₀ * B₁ * (A ^ 2 * ∑ k : Fin p.d,
      W q.1 ^ 2 * lor1 (q.1 - p.tau k) * (lor1 (q.2 - p.tau k) * |ν q.2|)
      + p.L * A * (W q.1 ^ 2 * kk (q.1 - q.2))) with hM
  have hconv : Integrable fun q : ℝ × ℝ => W q.1 ^ 2 * kk (q.1 - q.2) := by
    have h := Integrable.convolution_integrand (L := ContinuousLinearMap.mul ℝ ℝ) hW2 hkint
    have h' := h.swap
    refine h'.congr (Eventually.of_forall fun q => ?_)
    simp only [Function.comp, Prod.fst_swap, Prod.snd_swap, ContinuousLinearMap.mul_apply']
    rw [show q.2 - q.1 = -(q.1 - q.2) by ring]
    simp only [hkk, lor1_neg, abs_neg]
  have hsumI : Integrable fun q : ℝ × ℝ => ∑ k : Fin p.d,
      W q.1 ^ 2 * lor1 (q.1 - p.tau k) * (lor1 (q.2 - p.tau k) * |ν q.2|) :=
    integrable_finsetSum (Finset.univ : Finset (Fin p.d)) fun k _ =>
      (hW2lor k).mul_prod (hνi (p.tau k))
  have hMi : Integrable M :=
    ((hsumI.const_mul (A ^ 2)).add (hconv.const_mul (p.L * A))).const_mul (p.L * R₀ * B₁)
  have hpt : ∀ q : ℝ × ℝ, ‖W q.1 ^ 2 * (Kfun p F q.1 q.2 ^ 2 - Kinf p F q.1 q.2 ^ 2)
      * ν q.1 * ν q.2‖ ≤ M q := by
    intro q
    rw [Real.norm_eq_abs]
    have hM0 : 0 ≤ M q := by
      simp only [hM]
      have : 0 ≤ ∑ k : Fin p.d, W q.1 ^ 2 * lor1 (q.1 - p.tau k) * (lor1 (q.2 - p.tau k) * |ν q.2|) :=
        Finset.sum_nonneg fun k _ => by have := lor1_pos (q.1 - p.tau k); have := lor1_pos (q.2 - p.tau k); positivity
      have := hk0 (q.1 - q.2)
      positivity
    by_cases hq : q.1 ∈ Icc s₀ s₁
    · have hdiff := abs_Kinf_sub_Kfun_le_of_rho hF hR₀ (hρ q.1 hq) q.2
      have hK := abs_Kfun_le_lor1 hF q.1 q.2
      have hKi := abs_Kinf_le_lor1 hF q.1 q.2
      have hν1 : |ν q.1| ≤ B₁ := by
        have := hνS q.1 hq q.1; simp only [sub_self, abs_zero, Real.sqrt_zero, add_zero] at this
        exact this
      have hν2 := hνS q.1 hq q.2
      have hfac : Kfun p F q.1 q.2 ^ 2 - Kinf p F q.1 q.2 ^ 2
          = -((Kinf p F q.1 q.2 - Kfun p F q.1 q.2) * (Kfun p F q.1 q.2 + Kinf p F q.1 q.2)) := by
        ring
      rw [hfac, abs_mul, abs_mul, abs_mul, abs_neg, abs_mul, abs_of_nonneg (sq_nonneg (W q.1))]
      have hsum : |Kfun p F q.1 q.2 + Kinf p F q.1 q.2| * |ν q.2|
          ≤ A ^ 2 * ∑ k : Fin p.d, lor1 (q.1 - p.tau k) * lor1 (q.2 - p.tau k) * |ν q.2|
            + p.L * A * kk (q.1 - q.2) := by
        have hs1 := abs_add_le (Kfun p F q.1 q.2) (Kinf p F q.1 q.2)
        have hk : p.L * (A * lor1 (q.1 - q.2)) * |ν q.2| ≤ p.L * A * kk (q.1 - q.2) := by
          simp only [hkk]
          rw [show p.L * (A * lor1 (q.1 - q.2)) * |ν q.2| = p.L * A * (lor1 (q.1 - q.2) * |ν q.2|) by
            ring]
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (lor1_pos _).le)
            (by positivity)
          rw [abs_sub_comm]; exact hν2
        calc |Kfun p F q.1 q.2 + Kinf p F q.1 q.2| * |ν q.2|
            ≤ (|Kfun p F q.1 q.2| + |Kinf p F q.1 q.2|) * |ν q.2| :=
              mul_le_mul_of_nonneg_right hs1 (abs_nonneg _)
          _ ≤ (A ^ 2 * ∑ k : Fin p.d, lor1 (q.1 - p.tau k) * lor1 (q.2 - p.tau k)
                + p.L * (A * lor1 (q.1 - q.2))) * |ν q.2| :=
              mul_le_mul_of_nonneg_right (add_le_add hK hKi) (abs_nonneg _)
          _ ≤ _ := by
              have e : (A ^ 2 * ∑ k : Fin p.d, lor1 (q.1 - p.tau k) * lor1 (q.2 - p.tau k)) * |ν q.2|
                  = A ^ 2 * ∑ k : Fin p.d, lor1 (q.1 - p.tau k) * lor1 (q.2 - p.tau k) * |ν q.2| := by
                rw [mul_assoc, Finset.sum_mul]
              rw [add_mul, e]; exact add_le_add le_rfl hk
      have hS0 : 0 ≤ A ^ 2 * ∑ k : Fin p.d, lor1 (q.1 - p.tau k) * lor1 (q.2 - p.tau k) * |ν q.2|
            + p.L * A * kk (q.1 - q.2) := by
        have : 0 ≤ ∑ k : Fin p.d, lor1 (q.1 - p.tau k) * lor1 (q.2 - p.tau k) * |ν q.2| :=
          Finset.sum_nonneg fun k _ => by
            have := lor1_pos (q.1 - p.tau k); have := lor1_pos (q.2 - p.tau k); positivity
        have := hk0 (q.1 - q.2); positivity
      calc W q.1 ^ 2 * (|Kinf p F q.1 q.2 - Kfun p F q.1 q.2| * |Kfun p F q.1 q.2 + Kinf p F q.1 q.2|)
            * |ν q.1| * |ν q.2|
          = W q.1 ^ 2 * |Kinf p F q.1 q.2 - Kfun p F q.1 q.2| * |ν q.1|
            * (|Kfun p F q.1 q.2 + Kinf p F q.1 q.2| * |ν q.2|) := by ring
        _ ≤ W q.1 ^ 2 * (p.L * R₀) * B₁ * (A ^ 2 * ∑ k : Fin p.d, lor1 (q.1 - p.tau k)
              * lor1 (q.2 - p.tau k) * |ν q.2| + p.L * A * kk (q.1 - q.2)) := by
            refine mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hdiff (sq_nonneg _)) hν1
              (abs_nonneg _) (by positivity)) hsum (by positivity) (by positivity)
        _ = M q := by
            simp only [hM, Finset.mul_sum, mul_add]
            congr 1
            · exact Finset.sum_congr rfl fun k _ => by ring
            · ring
    · rw [hWS q.1 hq]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul,
        abs_zero]; exact hM0
  have hint := norm_integral_le_of_norm_le hMi (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs] at hint
  refine hint.trans ?_
  -- evaluate the majorant
  have hP1 : ∀ k : Fin p.d, Integrable (fun z : ℝ × ℝ =>
      W z.1 ^ 2 * lor1 (z.1 - p.tau k) * (lor1 (z.2 - p.tau k) * |ν z.2|)) := fun k =>
    (hW2lor k).mul_prod (hνi (p.tau k))
  have hI1 : ∀ k : Fin p.d, ∫ z : ℝ × ℝ, W z.1 ^ 2 * lor1 (z.1 - p.tau k)
      * (lor1 (z.2 - p.tau k) * |ν z.2|)
      = (∫ τ, W τ ^ 2 * lor1 (τ - p.tau k)) * ∫ τ, lor1 (τ - p.tau k) * |ν τ| := fun k => by
    rw [Measure.volume_eq_prod]
    exact integral_prod_mul (fun τ => W τ ^ 2 * lor1 (τ - p.tau k)) (fun τ => lor1 (τ - p.tau k) * |ν τ|)
  have hI2 : ∫ z : ℝ × ℝ, W z.1 ^ 2 * kk (z.1 - z.2) = (∫ τ, W τ ^ 2) * ∫ r, kk r := by
    rw [Measure.volume_eq_prod, integral_prod _ (by rw [← Measure.volume_eq_prod]; exact hconv),
      ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    simp only
    rw [integral_const_mul, integral_sub_left_eq_self (fun r => kk r) (μ := volume) τ]
  have hIM : ∫ q, M q = p.L * R₀ * B₁ * (A ^ 2 * ∑ k : Fin p.d,
      (∫ τ, W τ ^ 2 * lor1 (τ - p.tau k)) * (∫ τ, lor1 (τ - p.tau k) * |ν τ|)
      + p.L * A * ((∫ τ, W τ ^ 2) * ∫ r, kk r)) := by
    simp only [hM]
    rw [integral_const_mul, integral_add ((integrable_finsetSum _ fun k _ => hP1 k).const_mul _)
      (hconv.const_mul _), integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun k _ => hP1 k, hI2]
    congr 3
    exact Finset.sum_congr rfl fun k _ => hI1 k
  rw [hIM]
  have hB : 0 ≤ p.L * R₀ * B₁ := by positivity
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ ?_) hB
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => ?_) (sq_nonneg _)
    have hle : ∫ τ, W τ ^ 2 * lor1 (τ - p.tau k) ≤ π := by
      calc ∫ τ, W τ ^ 2 * lor1 (τ - p.tau k) ≤ ∫ τ, lor1 (τ - p.tau k) :=
            integral_mono (hW2lor k) (integrable_lor1.comp_sub_right (p.tau k))
              fun τ => mul_le_of_le_one_left (lor1_pos _).le (hWc τ)
        _ = π := by rw [integral_sub_right_eq_self (fun r => lor1 r) (p.tau k), integral_lor1]
    exact mul_le_mul_of_nonneg_right hle
      (integral_nonneg fun τ => mul_nonneg (lor1_pos _).le (abs_nonneg _))
  · have hk1 : 0 ≤ ∫ r, kk r := integral_nonneg hk0
    have hW2le : ∫ τ, W τ ^ 2 ≤ s₁ - s₀ := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc s₀ s₁)
        (fun τ hτ => by simp only [hWS τ hτ]; ring)]
      calc ∫ τ in Icc s₀ s₁, W τ ^ 2 ≤ ∫ τ in Icc s₀ s₁, (1 : ℝ) :=
            setIntegral_mono_on hW2.integrableOn (integrableOn_const (by simp))
              measurableSet_Icc fun τ _ => hWc τ
        _ = s₁ - s₀ := by
            rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc_of_le hs]
    rw [← mul_assoc (p.L * A)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW2le (by positivity)) hk1

/-! ## 6. Grid sums against the window Lorentz weight -/

theorem tau_eq_natCast (k : Fin p.d) : p.tau k = p.T + (k : ℕ) * p.h := by
  unfold Setting.tau; push_cast; ring

theorem h_pos (hF : LocalHypsCoreW cϱ p F) : 0 < p.h := by
  unfold Setting.h; exact div_pos (by positivity) hF.L_pos

theorem h_le_one (hF : LocalHypsCoreW cϱ p F) : p.h ≤ 1 := by
  unfold Setting.h
  rw [div_le_one hF.L_pos]
  have h8 : 8 ≤ p.L := by have := hF.one_le_w; have := hF.w_le; linarith
  linarith [Real.pi_lt_four]

/-- The grid points lie in `[T, 2T]`. -/
theorem tau_mem_Icc (hF : LocalHypsCoreW cϱ p F) (hT : 0 ≤ p.T) (k : Fin p.d) :
    p.tau k ∈ Icc p.T (2 * p.T) := by
  rw [tau_eq_natCast]
  have hh := h_pos hF
  have hk : ((k : ℕ) : ℝ) + 1 ≤ p.d := by exact_mod_cast k.isLt
  have hd : (p.d : ℝ) * p.h ≤ p.T := by
    unfold Setting.d Setting.h
    have hL := hF.L_pos
    have := Nat.floor_le (show 0 ≤ p.L * p.T / (2 * π) by positivity)
    calc (⌊p.L * p.T / (2 * π)⌋₊ : ℝ) * (2 * π / p.L) ≤ p.L * p.T / (2 * π) * (2 * π / p.L) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = p.T := by field_simp
  constructor
  · have : 0 ≤ ((k : ℕ) : ℝ) * p.h := by positivity
    linarith
  · nlinarith

theorem sum_lor1_tau_le (hF : LocalHypsCoreW cϱ p F) (x : ℝ) :
    ∑ k : Fin p.d, lor1 (x - p.tau k) ≤ 4 * π / p.h := by
  have h := sum_lor_grid_le one_pos le_rfl (h_pos hF) (h_le_one hF) p.T x p.d
  simp only [one_mul] at h
  rw [Fin.sum_univ_eq_sum_range (fun i => lor1 (x - p.tau i))]
  refine le_of_eq_of_le (Finset.sum_congr rfl fun k _ => ?_) h
  unfold Setting.tau; push_cast; rfl

theorem sum_cellW_le (hF : LocalHypsCoreW cϱ p F) {ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (x : ℝ) :
    ∑ k : Fin p.d, cellW p ℓ k x ≤ 8 * π * Real.sqrt ℓ / p.h := by
  have hs : 0 < Real.sqrt ℓ := Real.sqrt_pos.mpr hℓ
  have hs1 : Real.sqrt ℓ ≤ 1 := Real.sqrt_le_one.mpr hℓ1
  have h := sum_lor_grid_le hs hs1 (h_pos hF) (h_le_one hF) p.T x p.d
  calc ∑ k : Fin p.d, cellW p ℓ k x ≤ ∑ k : Fin p.d, 2 * ℓ * lor1 (Real.sqrt ℓ * (x - p.tau k)) :=
        Finset.sum_le_sum fun k _ => min_mul_lor1_le hℓ (x - p.tau k)
    _ = 2 * ℓ * ∑ k ∈ Finset.range p.d, lor1 (Real.sqrt ℓ * (x - (p.T + k * p.h))) := by
        rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range
          (fun i => lor1 (Real.sqrt ℓ * (x - p.tau i)))]
        simp only [Setting.tau, Int.cast_natCast]
    _ ≤ 2 * ℓ * (4 * π / (Real.sqrt ℓ * p.h)) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = 8 * π * Real.sqrt ℓ / p.h := by
        have hs2 : Real.sqrt ℓ * Real.sqrt ℓ = ℓ := Real.mul_self_sqrt hℓ.le
        have hh := h_pos hF
        field_simp
        nlinarith [hs2]

/-- Far from the window: `|x − 3T/2| ≥ 2T` puts every grid point at distance `≥ ¾|x − 3T/2|`, and
`d lor1(¾|x − c|) ≤ (32d/9T²) · lorentzW T c x`. -/
theorem far_bound_lorentz (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) {x : ℝ}
    (hx : 2 * p.T < |x - 3 * p.T / 2|) {f : Fin p.d → ℝ → ℝ}
    (hf : ∀ k y, f k y ≤ lor1 (y - p.tau k)) :
    ∑ k : Fin p.d, f k x ≤ 32 * p.d / (9 * p.T ^ 2) * lorentzW p.T (3 * p.T / 2) x := by
  set u := x - 3 * p.T / 2 with hu
  have hu0 : 0 < |u| := by linarith
  have hu2 : 0 < u ^ 2 := by rw [← sq_abs]; exact pow_pos hu0 2
  have hdist : ∀ k : Fin p.d, 3 / 4 * |u| ≤ |x - p.tau k| := by
    intro k
    have hk := tau_mem_Icc hF hT.le k
    have h1 : |p.tau k - 3 * p.T / 2| ≤ p.T / 2 := by
      rw [abs_le]; constructor <;> linarith [hk.1, hk.2]
    have h2 : |u| ≤ |x - p.tau k| + |p.tau k - 3 * p.T / 2| := by
      rw [hu]; calc |x - 3 * p.T / 2| = |(x - p.tau k) + (p.tau k - 3 * p.T / 2)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    linarith
  have hterm : ∀ k : Fin p.d, f k x ≤ 16 / (9 * u ^ 2) := by
    intro k
    refine (hf k x).trans ?_
    have hd := hdist k
    unfold lor1
    rw [← one_div, div_le_div_iff₀ (by positivity) (mul_pos (by norm_num) hu2)]
    have : (3 / 4 * |u|) ^ 2 ≤ (x - p.tau k) ^ 2 := by
      rw [← sq_abs (x - p.tau k)]; exact pow_le_pow_left₀ (by positivity) hd 2
    nlinarith [sq_abs u]
  have hlor : 1 / (2 * u ^ 2) * p.T ^ 2 ≤ lorentzW p.T (3 * p.T / 2) x := by
    have hT2 : p.T ^ 2 ≤ u ^ 2 := by
      rw [← sq_abs u]; exact pow_le_pow_left₀ hT.le (by linarith) 2
    have e : lorentzW p.T (3 * p.T / 2) x = p.T ^ 2 / (p.T ^ 2 + u ^ 2) := by
      unfold lorentzW; rw [← hu]; field_simp
    rw [e, one_div, inv_mul_eq_div, div_le_div_iff₀ (mul_pos (by norm_num) hu2) (by positivity)]
    nlinarith
  calc ∑ k : Fin p.d, f k x ≤ ∑ _k : Fin p.d, 16 / (9 * u ^ 2) := Finset.sum_le_sum fun k _ => hterm k
    _ = 32 * p.d / (9 * p.T ^ 2) * (1 / (2 * u ^ 2) * p.T ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlor (by positivity)

/-- Near the window `lorentzW ≥ 1/5`. -/
theorem lorentzW_ge_fifth {T x c : ℝ} (hT : 0 < T) (hx : |x - c| ≤ 2 * T) :
    1 / 5 ≤ lorentzW T c x := by
  unfold lorentzW
  have h1 : ((x - c) / T) ^ 2 ≤ 4 := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have : (x - c) ^ 2 ≤ (2 * T) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2
    nlinarith
  rw [one_div]
  exact inv_anti₀ (by positivity) (by linarith)

/-- **Lorentz domination of the lattice sum.** `Σ_k lor1(x − τ_k) ≤ C_σ lorentzW_T(x − 3T/2)`. -/
theorem sum_lor1_tau_le_lorentz (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) (x : ℝ) :
    ∑ k : Fin p.d, lor1 (x - p.tau k)
      ≤ (20 * π / p.h + 32 * p.d / (9 * p.T ^ 2)) * lorentzW p.T (3 * p.T / 2) x := by
  have hh := h_pos hF
  have hW0 := lorentzW_nonneg p.T (3 * p.T / 2) x
  rcases le_or_gt |x - 3 * p.T / 2| (2 * p.T) with hx | hx
  · have h5 := lorentzW_ge_fifth hT hx
    have h0 : 0 ≤ 32 * (p.d : ℝ) / (9 * p.T ^ 2) * lorentzW p.T (3 * p.T / 2) x := by positivity
    calc ∑ k : Fin p.d, lor1 (x - p.tau k) ≤ 4 * π / p.h := sum_lor1_tau_le hF x
      _ = 20 * π / p.h * (1 / 5) := by ring
      _ ≤ 20 * π / p.h * lorentzW p.T (3 * p.T / 2) x :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ ≤ _ := by rw [add_mul]; linarith
  · have := far_bound_lorentz hF hT hx (f := fun k y => lor1 (y - p.tau k)) fun k y => le_rfl
    have h0 : 0 ≤ 20 * π / p.h * lorentzW p.T (3 * p.T / 2) x := by positivity
    linarith

/-- **Lorentz domination of the cell weights.** `Σ_k m_k(x) ≤ C_Ω lorentzW_T(x − 3T/2)`. -/
theorem sum_cellW_le_lorentz (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hℓ1 : ℓ ≤ 1) (x : ℝ) :
    ∑ k : Fin p.d, cellW p ℓ k x
      ≤ (40 * π * Real.sqrt ℓ / p.h + 32 * p.d / (9 * p.T ^ 2)) * lorentzW p.T (3 * p.T / 2) x := by
  have hh := h_pos hF
  have hW0 := lorentzW_nonneg p.T (3 * p.T / 2) x
  rcases le_or_gt |x - 3 * p.T / 2| (2 * p.T) with hx | hx
  · have h5 := lorentzW_ge_fifth hT hx
    have h0 : 0 ≤ 32 * (p.d : ℝ) / (9 * p.T ^ 2) * lorentzW p.T (3 * p.T / 2) x := by positivity
    calc ∑ k : Fin p.d, cellW p ℓ k x ≤ 8 * π * Real.sqrt ℓ / p.h := sum_cellW_le hF hℓ hℓ1 x
      _ = 40 * π * Real.sqrt ℓ / p.h * (1 / 5) := by ring
      _ ≤ 40 * π * Real.sqrt ℓ / p.h * lorentzW p.T (3 * p.T / 2) x :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ ≤ _ := by rw [add_mul]; linarith
  · have := far_bound_lorentz hF hT hx (f := fun k y => cellW p ℓ k y) fun k y => cellW_le_lor1 ℓ k y
    have h0 : 0 ≤ 40 * π * Real.sqrt ℓ / p.h * lorentzW p.T (3 * p.T / 2) x := by positivity
    linarith

end GaloisForLFunctions.TransThresholdPairCorrelation
