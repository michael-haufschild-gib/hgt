import GaloisForLFunctions.goldbach.LiLiu.Arithmetic.UnitSamples
import GaloisForLFunctions.goldbach.LiLiu.Mellin.VerticalLine
import Mathlib.MeasureTheory.Integral.Prod

/-! # Two-variable Mellin inversion of the exact arithmetic diagonal -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Filter MetaplecticMobiusDescent.CubicEisenstein
open scoped ComplexConjugate
noncomputable section

private theorem separate_dirichlet_term (a : ℕ → ℂ) (h0 : a 0=0) (s z : ℂ) (k : ℕ) :
    LSeries.term a (1+(s+conj z)) k =
      (a k / k) * (k:ℂ)^(-s) * conj ((k:ℂ)^(-z)) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  have hn : (k:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hcc := _root_.RHTower.GaussZeroSum.ofReal_cpow_conj (Nat.cast_pos.mpr hk) (-z)
  simp only [Complex.ofReal_natCast] at hcc
  rw [LSeries.term_def₀ h0, show -(1+(s+conj z)) = -1 + -s + conj (-z) by rw [map_neg]; ring,
    cpow_add _ _ hn, cpow_add _ _ hn, hcc, cpow_neg_one]
  ring

/-- The same absolute Dirichlet majorant works on the whole product contour:
only the real part of the exponent enters the norm of a term. -/
theorem diagonal_line_integral (a : ℕ → ℂ) (h0 : a 0=0) (σ : ℝ)
    (ha : LSeriesSummable a ((1+2*σ:ℝ):ℂ)) {V : ℝ → ℂ} (hc : Measurable V) (hV : Integrable V) :
    (∫ p : ℝ × ℝ, LSeries a (1+(mellinLine σ p.1 + conj (mellinLine σ p.2))) *
      (V p.1 * conj (V p.2))) = ∑' k : ℕ, (a k / k) *
        ((∫ t : ℝ, (k:ℂ)^(-mellinLine σ t)*V t) * conj (∫ t : ℝ, (k:ℂ)^(-mellinLine σ t)*V t)) := by
  let w (p : ℝ × ℝ) := 1+(mellinLine σ p.1 + conj (mellinLine σ p.2))
  let K (k : ℕ) (p : ℝ × ℝ) := LSeries.term a (w p) k * (V p.1 * conj (V p.2))
  let c (k : ℕ) := ‖LSeries.term a ((1+2*σ:ℝ):ℂ) k‖
  let g (p : ℝ × ℝ) := ‖V p.1‖ * ‖V p.2‖
  have hw (p : ℝ × ℝ) : (w p).re = 1+2*σ := by simp [w,mellinLine,two_mul]
  have hcont : Continuous w := by dsimp [w,mellinLine]; fun_prop
  have hK (k : ℕ) : Measurable (K k) := by
    simp only [K,LSeries.term_def₀ h0]
    exact (measurable_const.mul (measurable_const.pow hcont.measurable.neg)).mul
      ((hc.comp measurable_fst).mul (continuous_conj.measurable.comp (hc.comp measurable_snd)))
  have hnorm (k : ℕ) (p : ℝ × ℝ) : ‖K k p‖ = c k * g p := by
    simp [K,c,g,LSeries.norm_term_eq,hw]
  have hg : Integrable g := hV.norm.mul_prod hV.norm
  have hi (k : ℕ) : Integrable (K k) := (hg.const_mul (c k)).mono' (hK k).aestronglyMeasurable
    (Eventually.of_forall fun p => (hnorm k p).le)
  have hsum : Summable fun k => ∫ p, ‖K k p‖ := by
    simp only [hnorm,integral_const_mul]
    exact (summable_norm_iff.mpr ha).mul_right _
  calc
    _ = ∫ p, ∑' k, K k p := by simp only [K,w,LSeries,tsum_mul_right]
    _ = ∑' k, ∫ p, K k p := (integral_tsum_of_summable_integral_norm hi hsum).symm
    _ = _ := by
      apply tsum_congr
      intro k
      let F (t : ℝ) := (k:ℂ)^(-mellinLine σ t)*V t
      have he (p : ℝ × ℝ) : K k p = (a k/k) * (F p.1 * conj (F p.2)) := by
        simp only [K,w,F,separate_dirichlet_term a h0,map_mul]
        ring
      simp only [he,integral_const_mul,integral_prod_mul,integral_conj,F]

/-- Formula (7.5) on the Hermitian product contour, including the 1/N normalization. -/
theorem diagonal_mellin_evaluation (N : ℕ) [NeZero N] (φ : TestWeight) {σ : ℝ} (hσ : 0 < σ) :
    (1/(2*Real.pi) : ℂ)^2 * (∫ p : ℝ × ℝ, diagonalSeries N
      (mellinLine σ p.1 + conj (mellinLine σ p.2)) *
      (mellinMultiplier N φ (mellinLine σ p.1) * conj (mellinMultiplier N φ (mellinLine σ p.2)))) =
      (diagonal φ N : ℂ) := by
  have hn : 0 < N := NeZero.pos N
  have hp : 0 < (N:ℝ) := Nat.cast_pos.mpr hn
  have hV := mellinMultiplier_integrable N hn φ σ
  have hline : Continuous (mellinLine σ) := by unfold mellinLine; fun_prop
  have hc := (mellinMultiplier_continuous N hn φ).comp hline
  simp only [diagonalSeries]
  rw [diagonal_line_integral _ (diagonalCoefficient_zero _) σ
    (diagonalSeries_summable N (by simp; linarith only [hσ])) hc.measurable hV,
    ← tsum_mul_left, ← diagonal_samples N φ]
  apply tsum_congr
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  let c : ℂ := 1/(2*Real.pi)
  let J := ∫ t : ℝ, (k:ℂ)^(-mellinLine σ t)*mellinMultiplier N φ (mellinLine σ t)
  have hi : companion φ ((k:ℝ)/N) = c * J := by
    rw [companion_inversion φ σ _ (div_pos (Nat.cast_pos.mpr hk) hp)]
    simp only [J,c,mellinLine,mellinMultiplier,positive_quotient_cpow_neg _ _ (Nat.cast_pos.mpr hk) hp,
      Complex.ofReal_natCast,mul_assoc]
  change c^2 * (_ * (J * conj J)) = _
  rw [hi,map_mul, show conj c=c by simp [c]]
  ring

#print axioms diagonal_mellin_evaluation
end
end GaloisForLFunctions.Goldbach.LiLiu
