import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Normed.Order.Lattice

/-!
# Shell-gap tail decay

A Dirichlet-type sum whose exponents all lie to the right of `A + δ` is smaller than
`e^{-(t-t₀)(A+δ)}` times its value at the reference time, so after multiplying by `e^{2At}` any
determinant defect between the full sum and its bottom shell decays like `e^{-tδ}`.
-/

open Filter Topology

namespace RHTower

noncomputable section

theorem norm_exp_neg_mul (t : ℝ) (w : ℂ) :
    ‖Complex.exp (-((t : ℂ) * w))‖ = Real.exp (-(t * w.re)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- **The shell-gap tail bound.**  Every exponent to the right of `A + δ` contributes at most its
reference value times `e^{-(t-t₀)(A+δ)}`. -/
theorem norm_tsum_shellTail_le {ι : Type*} {w g : ι → ℂ} {A delta t0 : ℝ}
    (hgap : ∀ q, A + delta ≤ (w q).re)
    (hsum : Summable fun q => ‖g q‖ * Real.exp (-(t0 * (w q).re)))
    {t : ℝ} (ht : t0 ≤ t) :
    ‖∑' q, g q * Complex.exp (-((t : ℂ) * w q))‖
      ≤ (∑' q, ‖g q‖ * Real.exp (-(t0 * (w q).re)))
        * Real.exp (-((t - t0) * (A + delta))) := by
  have hpt : ∀ q, ‖g q * Complex.exp (-((t : ℂ) * w q))‖
      ≤ (‖g q‖ * Real.exp (-(t0 * (w q).re))) * Real.exp (-((t - t0) * (A + delta))) := by
    intro q
    rw [norm_mul, norm_exp_neg_mul]
    have hsplit : Real.exp (-(t * (w q).re))
        = Real.exp (-(t0 * (w q).re)) * Real.exp (-((t - t0) * (w q).re)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hmono : Real.exp (-((t - t0) * (w q).re))
        ≤ Real.exp (-((t - t0) * (A + delta))) := by
      refine Real.exp_le_exp.2 ?_
      have h1 : (0 : ℝ) ≤ t - t0 := by linarith
      nlinarith [hgap q, h1]
    rw [hsplit, ← mul_assoc]
    refine mul_le_mul_of_nonneg_left hmono ?_
    positivity
  have hsum' : Summable fun q => (‖g q‖ * Real.exp (-(t0 * (w q).re)))
      * Real.exp (-((t - t0) * (A + delta))) := hsum.mul_right _
  have hnormsum : Summable fun q => ‖g q * Complex.exp (-((t : ℂ) * w q))‖ :=
    hsum'.of_nonneg_of_le (fun q => norm_nonneg _) hpt
  refine le_trans (norm_tsum_le_tsum_norm hnormsum) ?_
  rw [← tsum_mul_right]
  exact Summable.tsum_le_tsum hpt hnormsum hsum'

/-- **The shell-gap determinant defect vanishes.**  If two carriers split into a bottom part of
exponent `A` and a tail of exponent at least `A + δ`, the `e^{2At}`-renormalized difference of the
two products tends to zero. -/
theorem tendsto_shellGap_defect {A delta : ℝ} (hdelta : 0 < delta)
    {b₁ b₂ r₁ r₂ : ℝ} (hb₁ : 0 ≤ b₁) (_hb₂ : 0 ≤ b₂) (hr₁ : 0 ≤ r₁) (_hr₂ : 0 ≤ r₂)
    (Y₁ Y₂ Z₁ Z₂ : ℝ → ℂ)
    (hY₁ : ∀ t, ‖Y₁ t‖ ≤ b₁ * Real.exp (-(t * A)))
    (hY₂ : ∀ t, ‖Y₂ t‖ ≤ b₂ * Real.exp (-(t * A)))
    (hZ₁ : ∀ t, ‖Z₁ t‖ ≤ r₁ * Real.exp (-(t * (A + delta))))
    (hZ₂ : ∀ t, ‖Z₂ t‖ ≤ r₂ * Real.exp (-(t * (A + delta)))) :
    Tendsto (fun t : ℝ => Real.exp (2 * A * t) *
        ‖(Y₁ t + Z₁ t) * (Y₂ t + Z₂ t) - Y₁ t * Y₂ t‖) atTop (𝓝 0) := by
  have hbound : ∀ t : ℝ, Real.exp (2 * A * t) *
      ‖(Y₁ t + Z₁ t) * (Y₂ t + Z₂ t) - Y₁ t * Y₂ t‖
      ≤ (b₁ * r₂ + r₁ * b₂) * Real.exp (-(t * delta))
        + r₁ * r₂ * Real.exp (-(2 * (t * delta))) := by
    intro t
    have hsplit : (Y₁ t + Z₁ t) * (Y₂ t + Z₂ t) - Y₁ t * Y₂ t
        = Y₁ t * Z₂ t + Z₁ t * Y₂ t + Z₁ t * Z₂ t := by ring
    have h1 : ‖Y₁ t * Z₂ t‖ ≤ (b₁ * r₂) *
        (Real.exp (-(t * A)) * Real.exp (-(t * (A + delta)))) := by
      rw [norm_mul]
      have := mul_le_mul (hY₁ t) (hZ₂ t) (norm_nonneg _) (by positivity)
      calc ‖Y₁ t‖ * ‖Z₂ t‖
          ≤ (b₁ * Real.exp (-(t * A))) * (r₂ * Real.exp (-(t * (A + delta)))) := this
        _ = (b₁ * r₂) * (Real.exp (-(t * A)) * Real.exp (-(t * (A + delta)))) := by ring
    have h2 : ‖Z₁ t * Y₂ t‖ ≤ (r₁ * b₂) *
        (Real.exp (-(t * A)) * Real.exp (-(t * (A + delta)))) := by
      rw [norm_mul]
      have := mul_le_mul (hZ₁ t) (hY₂ t) (norm_nonneg _) (by positivity)
      calc ‖Z₁ t‖ * ‖Y₂ t‖
          ≤ (r₁ * Real.exp (-(t * (A + delta)))) * (b₂ * Real.exp (-(t * A))) := this
        _ = (r₁ * b₂) * (Real.exp (-(t * A)) * Real.exp (-(t * (A + delta)))) := by ring
    have h3 : ‖Z₁ t * Z₂ t‖ ≤ (r₁ * r₂) *
        (Real.exp (-(t * (A + delta))) * Real.exp (-(t * (A + delta)))) := by
      rw [norm_mul]
      have := mul_le_mul (hZ₁ t) (hZ₂ t) (norm_nonneg _) (by positivity)
      calc ‖Z₁ t‖ * ‖Z₂ t‖
          ≤ (r₁ * Real.exp (-(t * (A + delta)))) * (r₂ * Real.exp (-(t * (A + delta)))) := this
        _ = (r₁ * r₂) * (Real.exp (-(t * (A + delta))) * Real.exp (-(t * (A + delta)))) := by ring
    have htri : ‖Y₁ t * Z₂ t + Z₁ t * Y₂ t + Z₁ t * Z₂ t‖
        ≤ ‖Y₁ t * Z₂ t‖ + ‖Z₁ t * Y₂ t‖ + ‖Z₁ t * Z₂ t‖ :=
      le_trans (norm_add_le _ _) (by
        have := norm_add_le (Y₁ t * Z₂ t) (Z₁ t * Y₂ t)
        linarith)
    have hexp1 : Real.exp (2 * A * t) *
        (Real.exp (-(t * A)) * Real.exp (-(t * (A + delta)))) = Real.exp (-(t * delta)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have hexp2 : Real.exp (2 * A * t) *
        (Real.exp (-(t * (A + delta))) * Real.exp (-(t * (A + delta))))
        = Real.exp (-(2 * (t * delta))) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [hsplit]
    have hepos : (0 : ℝ) < Real.exp (2 * A * t) := Real.exp_pos _
    calc Real.exp (2 * A * t) * ‖Y₁ t * Z₂ t + Z₁ t * Y₂ t + Z₁ t * Z₂ t‖
        ≤ Real.exp (2 * A * t) * (‖Y₁ t * Z₂ t‖ + ‖Z₁ t * Y₂ t‖ + ‖Z₁ t * Z₂ t‖) :=
          mul_le_mul_of_nonneg_left htri hepos.le
      _ ≤ Real.exp (2 * A * t) * ((b₁ * r₂) *
            (Real.exp (-(t * A)) * Real.exp (-(t * (A + delta))))
          + (r₁ * b₂) * (Real.exp (-(t * A)) * Real.exp (-(t * (A + delta))))
          + (r₁ * r₂) * (Real.exp (-(t * (A + delta))) * Real.exp (-(t * (A + delta))))) := by
          refine mul_le_mul_of_nonneg_left ?_ hepos.le
          linarith [h1, h2, h3]
      _ = (b₁ * r₂ + r₁ * b₂) * (Real.exp (2 * A * t) *
            (Real.exp (-(t * A)) * Real.exp (-(t * (A + delta)))))
          + r₁ * r₂ * (Real.exp (2 * A * t) *
            (Real.exp (-(t * (A + delta))) * Real.exp (-(t * (A + delta))))) := by ring
      _ = (b₁ * r₂ + r₁ * b₂) * Real.exp (-(t * delta))
          + r₁ * r₂ * Real.exp (-(2 * (t * delta))) := by rw [hexp1, hexp2]
  have hlim1 : Tendsto (fun t : ℝ => Real.exp (-(t * delta))) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => -(t * delta)) atTop atBot :=
      Filter.tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hdelta)
    exact Real.tendsto_exp_atBot.comp this
  have hlim2 : Tendsto (fun t : ℝ => Real.exp (-(2 * (t * delta)))) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => -(2 * (t * delta))) atTop atBot := by
      refine Filter.tendsto_neg_atTop_atBot.comp ?_
      exact (tendsto_id.atTop_mul_const hdelta).const_mul_atTop (by norm_num)
    exact Real.tendsto_exp_atBot.comp this
  have hmaj : Tendsto (fun t : ℝ => (b₁ * r₂ + r₁ * b₂) * Real.exp (-(t * delta))
      + r₁ * r₂ * Real.exp (-(2 * (t * delta)))) atTop (𝓝 0) := by
    have h1 := hlim1.const_mul (b₁ * r₂ + r₁ * b₂)
    have h2 := hlim2.const_mul (r₁ * r₂)
    have := h1.add h2
    simpa using this
  refine squeeze_zero (fun t => ?_) hbound hmaj
  positivity

end

end RHTower
