import GaloisForLFunctions.goldbach.LiLiu.MellinWeight

/-! # Termwise Mellin inversion for the arithmetic terms

At fixed abscissa the absolute value of a Dirichlet term is independent
of height. Multiplication by an integrable Mellin weight therefore permits
termwise integration whenever the Dirichlet series converges absolutely.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Filter Set MetaplecticMobiusDescent.CubicEisenstein
noncomputable section

private def line (σ t : ℝ) : ℂ := (σ : ℂ) + t * I

private theorem line_continuous (σ : ℝ) : Continuous (line σ) := by
  unfold line
  fun_prop

/-- An integrable vertical multiplier commutes with an absolutely convergent Dirichlet series. -/
theorem integral_LSeries_mul (a : ℕ → ℂ) {c : ℝ} (hs : LSeriesSummable a c)
    {V : ℝ → ℂ} (hV : Integrable V) :
    (∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * V t) =
      ∑' n, ∫ t : ℝ, LSeries.term a ((c : ℂ) + t * I) n * V t := by
  let F (n : ℕ) (t : ℝ) := LSeries.term a (line c t) n * V t
  have hn (n : ℕ) (t : ℝ) : ‖F n t‖ = ‖LSeries.term a c n‖ * ‖V t‖ := by
    simp [F, line, norm_mul, LSeries.norm_term_eq]
  have hc (n : ℕ) : Continuous fun t : ℝ => LSeries.term a (line c t) n := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp
    simp only [LSeries.term_of_ne_zero hp.ne', div_eq_mul_inv, ← Complex.cpow_neg]
    exact continuous_const.mul ((line_continuous c).neg.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hp.ne')))
  have hi (n : ℕ) : Integrable (F n) := by
    apply (hV.norm.const_mul ‖LSeries.term a c n‖).mono'
      ((hc n).aestronglyMeasurable.mul hV.1)
    exact Eventually.of_forall fun t => (hn n t).le
  have hsum : Summable fun n => ∫ t : ℝ, ‖F n t‖ := by
    simp only [hn, integral_const_mul]
    exact (summable_norm_iff.mpr hs).mul_right _
  calc
    _ = ∫ t : ℝ, ∑' n, F n t := by simp only [F, line, LSeries, tsum_mul_right]
    _ = _ := (integral_tsum_of_summable_integral_norm hi hsum).symm

/-- Shifted Dirichlet coefficients are recovered with their full normalization. -/
theorem companion_LSeries_inversion (φ : TestWeight) (a : ℕ → ℂ) (ha : a 0 = 0)
    {N : ℕ} (hN : 0 < N) (b σ : ℝ) (hs : LSeriesSummable a ((b + σ : ℝ) : ℂ)) :
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, LSeries a (((b + σ : ℝ) : ℂ) + t * I) *
      ((N : ℂ) ^ ((σ : ℂ) + t * I) * mellin (companion φ) ((σ : ℂ) + t * I))) =
    ∑' n : ℕ, (a n * (n : ℂ) ^ (-(b : ℂ))) * companion φ ((n : ℝ) / N) := by
  have hV := compactMellin_vertical_integrable _ _ _ (by norm_num)
    (companion_support φ) (companion_smooth φ) σ
  have hN' : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hd := vertical_power_mul_integrable _ hV (N : ℝ) σ hN'
  simp only [Complex.ofReal_natCast] at hd
  rw [integral_LSeries_mul a hs hd, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ha]
  have hp : 0 < (n : ℝ) / N := div_pos (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hN)
  rw [companion_inversion φ σ _ hp]
  let B := a n * (n : ℂ) ^ (-(b : ℂ))
  have he (t : ℝ) : LSeries.term a (((b + σ : ℝ) : ℂ) + t * I) n *
      ((N : ℂ) ^ line σ t * mellin (companion φ) (line σ t)) =
      B * ((((n : ℝ) / N : ℝ) : ℂ) ^ (-line σ t) * mellin (companion φ) (line σ t)) := by
    have harg : -(((b + σ : ℝ) : ℂ) + t * I) = -(b : ℂ) + (-line σ t) := by
      simp only [line, Complex.ofReal_add]
      ring
    rw [LSeries.term_def₀ ha, harg, Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn.ne'),
      positive_quotient_cpow_neg _ _ (Nat.cast_pos.mpr hn) hN', Complex.ofReal_natCast]
    dsimp [B]
    ring
  change _ * (∫ t : ℝ, LSeries.term a _ n * ((N : ℂ) ^ line σ t * mellin (companion φ) (line σ t))) =
    B * (_ * ∫ t : ℝ, (((n : ℝ) / N : ℝ) : ℂ) ^ (-line σ t) * mellin (companion φ) (line σ t))
  simp only [he, integral_const_mul]
  ring

#print axioms companion_LSeries_inversion
end
end GaloisForLFunctions.Goldbach.LiLiu
