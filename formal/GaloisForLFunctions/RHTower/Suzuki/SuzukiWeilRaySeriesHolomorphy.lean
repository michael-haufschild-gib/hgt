import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilDifferentialPairing

/-!
# The ray series of the transform is holomorphic off the Xi divisor

Step 3a of the route to Suzuki's Lemma 3.2.  The series

`T(z) = sum over q of (integral of (e^{-i gamma_q t} - 1) conj(phi t) dt) / (gamma_q (z - gamma_q))`

is complex differentiable at every point where `XiC` does not vanish.

The uniform dominant is the point of the argument.  A crude `1/dist(z0, Gamma)` bound on each factor
gives only `sum 1/|gamma_q|`, which diverges.  Instead, shrinking the ball to radius `r/2` where
`r <= |z0 - gamma_q|` for *every* `q` (available because the divisor is closed and misses `z0`)
yields `|w - gamma_q| >= |z0 - gamma_q|/2` uniformly, hence

`‖ray term‖ <= 2 M ‖(gamma_q (gamma_q - z0))^{-1}‖`,

whose summability is the corpus's `summable_xiResolventProduct_norm`.  `M` is the uniform numerator
bound `(e^{T/2}+1) ‖phi‖_1`, which exists because every Xi zero satisfies `|Im gamma| < 1/2`.
-/

open Complex Filter Topology MeasureTheory Set
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

/-! ## The ray series is holomorphic off the Xi divisor -/

/-- Off the divisor there is a uniform positive distance to every zero copy. -/
theorem exists_pos_dist_xiSpectralPoint {z₀ : ℂ} (hz₀ : XiC z₀ ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ q : XiZeroCopy, r ≤ ‖z₀ - xiSpectralPoint q‖ := by
  have hopen : IsOpen {z : ℂ | XiC z ≠ 0} :=
    isOpen_ne_fun continuous_XiC continuous_const
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hopen z₀ hz₀
  refine ⟨r / 2, by linarith, fun q => ?_⟩
  by_contra hc
  push_neg at hc
  have hmem : xiSpectralPoint q ∈ Metric.ball z₀ r := by
    rw [Metric.mem_ball, Complex.dist_eq, ← norm_neg]
    have : -(xiSpectralPoint q - z₀) = z₀ - xiSpectralPoint q := by ring
    rw [this]
    linarith
  exact (hball hmem) (XiC_xiSpectralPoint_eq_zero q)

/-- A uniform bound on the ray numerators. -/
theorem norm_raySeriesNumerator_le {φ : ℝ → ℂ} (hφ : Integrable φ) {T : ℝ}
    (hsupp : ∀ t : ℝ, T < |t| → φ t = 0) (q : XiZeroCopy) :
    ‖∫ t : ℝ, (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1) * (starRingEnd ℂ) (φ t)‖
      ≤ (Real.exp (T / 2) + 1) * ∫ t : ℝ, ‖φ t‖ := by
  calc ‖∫ t : ℝ, (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1)
          * (starRingEnd ℂ) (φ t)‖
      ≤ ∫ t : ℝ, ‖(Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1)
          * (starRingEnd ℂ) (φ t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (Real.exp (T / 2) + 1) * ‖φ t‖ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
          (hφ.norm.const_mul _) (Filter.Eventually.of_forall (norm_conj_phi_bound hsupp q))
    _ = (Real.exp (T / 2) + 1) * ∫ t : ℝ, ‖φ t‖ := integral_const_mul _ _

/-- **The ray series is holomorphic off the Xi divisor.** -/
theorem differentiableAt_suzukiPHatRaySum {φ : ℝ → ℂ} (hφ : Integrable φ) {T : ℝ}
    (hsupp : ∀ t : ℝ, T < |t| → φ t = 0) {z₀ : ℂ} (hz₀ : XiC z₀ ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => ∑' q : XiZeroCopy, suzukiPHatRayTerm φ z q) z₀ := by
  obtain ⟨r, hr, hdist⟩ := exists_pos_dist_xiSpectralPoint hz₀
  set M : ℝ := (Real.exp (T / 2) + 1) * ∫ t : ℝ, ‖φ t‖ with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact mul_nonneg (by positivity) (integral_nonneg fun t => norm_nonneg _)
  set U : Set ℂ := Metric.ball z₀ (r / 2) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hz₀U : z₀ ∈ U := Metric.mem_ball_self (by linarith)
  set u : XiZeroCopy → ℝ := fun q =>
    2 * M * ‖(xiSpectralPoint q * (xiSpectralPoint q - z₀))⁻¹‖ with hu
  have husum : Summable u := (summable_xiResolventProduct_norm z₀).mul_left _
  have hbound : ∀ (q : XiZeroCopy), ∀ w ∈ U, ‖suzukiPHatRayTerm φ w q‖ ≤ u q := by
    intro q w hw
    have hd0 : r ≤ ‖z₀ - xiSpectralPoint q‖ := hdist q
    have hwd : ‖w - z₀‖ < r / 2 := by
      rw [Metric.mem_ball, Complex.dist_eq] at hw
      exact hw
    have hlow : ‖z₀ - xiSpectralPoint q‖ / 2 ≤ ‖w - xiSpectralPoint q‖ := by
      have htri : ‖z₀ - xiSpectralPoint q‖
          ≤ ‖z₀ - w‖ + ‖w - xiSpectralPoint q‖ := by
        have := norm_add_le (z₀ - w) (w - xiSpectralPoint q)
        rw [show (z₀ - w) + (w - xiSpectralPoint q) = z₀ - xiSpectralPoint q by ring] at this
        exact this
      have hsym : ‖z₀ - w‖ = ‖w - z₀‖ := by rw [← norm_neg]; congr 1; ring
      rw [hsym] at htri
      linarith
    have hγ0 : (0 : ℝ) < ‖z₀ - xiSpectralPoint q‖ := lt_of_lt_of_le hr hd0
    have hwpos : (0 : ℝ) < ‖w - xiSpectralPoint q‖ := lt_of_lt_of_le (by linarith) hlow
    have hnum := norm_raySeriesNumerator_le hφ hsupp q
    have husym : ‖(xiSpectralPoint q * (xiSpectralPoint q - z₀))⁻¹‖
        = (‖xiSpectralPoint q‖ * ‖z₀ - xiSpectralPoint q‖)⁻¹ := by
      rw [norm_inv, norm_mul]
      congr 2
      rw [← norm_neg]
      congr 1
      ring
    have hunn : 0 ≤ u q := by
      rw [hu]
      exact mul_nonneg (by linarith) (norm_nonneg _)
    rcases eq_or_ne (xiSpectralPoint q * (w - xiSpectralPoint q)) 0 with h0 | h0
    · rw [suzukiPHatRayTerm, h0, div_zero, norm_zero]
      exact hunn
    · have hγpos : (0 : ℝ) < ‖xiSpectralPoint q‖ := by
        rcases eq_or_ne (xiSpectralPoint q) 0 with hz | hz
        · exact absurd (by rw [hz, zero_mul]) h0
        · exact norm_pos_iff.mpr hz
      have hprodpos : (0 : ℝ) < ‖xiSpectralPoint q‖ * ‖w - xiSpectralPoint q‖ :=
        mul_pos hγpos hwpos
      have hhalfpos : (0 : ℝ) < ‖xiSpectralPoint q‖ * ‖z₀ - xiSpectralPoint q‖ / 2 := by
        positivity
      have hA : ‖xiSpectralPoint q‖ * ‖z₀ - xiSpectralPoint q‖ / 2
          ≤ ‖xiSpectralPoint q‖ * ‖w - xiSpectralPoint q‖ := by
        have hmul := mul_le_mul_of_nonneg_left hlow (norm_nonneg (xiSpectralPoint q))
        calc ‖xiSpectralPoint q‖ * ‖z₀ - xiSpectralPoint q‖ / 2
            = ‖xiSpectralPoint q‖ * (‖z₀ - xiSpectralPoint q‖ / 2) := by ring
          _ ≤ ‖xiSpectralPoint q‖ * ‖w - xiSpectralPoint q‖ := hmul
      simp only [hu]
      rw [suzukiPHatRayTerm, norm_div, norm_mul, husym]
      calc ‖∫ t : ℝ, (Complex.exp (-(I * xiSpectralPoint q * (t : ℂ))) - 1)
              * (starRingEnd ℂ) (φ t)‖ / (‖xiSpectralPoint q‖ * ‖w - xiSpectralPoint q‖)
          ≤ M / (‖xiSpectralPoint q‖ * ‖w - xiSpectralPoint q‖) :=
            div_le_div_of_nonneg_right hnum hprodpos.le
        _ ≤ M / (‖xiSpectralPoint q‖ * ‖z₀ - xiSpectralPoint q‖ / 2) :=
            div_le_div_of_nonneg_left hM0 hhalfpos hA
        _ = 2 * M * (‖xiSpectralPoint q‖ * ‖z₀ - xiSpectralPoint q‖)⁻¹ := by
            field_simp
  have hdiff : ∀ q : XiZeroCopy, DifferentiableOn ℂ (fun w : ℂ => suzukiPHatRayTerm φ w q) U := by
    intro q
    intro w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    have hne : w - xiSpectralPoint q ≠ 0 := by
      intro hc
      have hd0 : r ≤ ‖z₀ - xiSpectralPoint q‖ := hdist q
      have hwd : ‖w - z₀‖ < r / 2 := by
        rw [Metric.mem_ball, Complex.dist_eq] at hw
        exact hw
      have heq : xiSpectralPoint q = w := by
        have : w - xiSpectralPoint q = 0 := hc
        linear_combination -this
      rw [← heq] at hwd
      have hsym : ‖xiSpectralPoint q - z₀‖ = ‖z₀ - xiSpectralPoint q‖ := by
        rw [← norm_neg]; congr 1; ring
      rw [hsym] at hwd
      linarith
    have hden : xiSpectralPoint q * (w - xiSpectralPoint q) ≠ 0 :=
      mul_ne_zero (xiSpectralPoint_ne_zero q) hne
    unfold suzukiPHatRayTerm
    exact (differentiableAt_const _).div (by fun_prop) hden
  have hDon : DifferentiableOn ℂ
      (fun w : ℂ => ∑' q : XiZeroCopy, suzukiPHatRayTerm φ w q) U :=
    differentiableOn_tsum_of_summable_norm husum hdiff hUopen hbound
  exact hDon.differentiableAt (hUopen.mem_nhds hz₀U)

end
end RHTower

