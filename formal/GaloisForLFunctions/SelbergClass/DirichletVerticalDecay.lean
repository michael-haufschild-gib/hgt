import GaloisForLFunctions.HTGeometry.BohrExponentialSeriesCoefficient
import GaloisForLFunctions.HTGeometry.LinearOdeBohrSpectrum
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# Vertical decay of an absolutely convergent Dirichlet series

On a line of absolute convergence a Dirichlet series is almost periodic.
Decay at one end therefore forces it to vanish, and extraction of its
distinct Bohr frequencies kills every positive-index coefficient.
-/

noncomputable section
open Complex Filter Topology

namespace GaloisForLFunctions.SelbergClass

theorem lSeries_term_vertical (f : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    LSeries.term f ((σ : ℂ) + (t : ℂ) * I) n =
      LSeries.term f σ n * expChar (-Real.log n) t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hlog : Complex.log n = (Real.log n : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne',
      expChar, Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, hlog]
    have he : Complex.exp ((Real.log n : ℂ) * ((σ : ℂ) + (t : ℂ) * I)) =
        Complex.exp ((Real.log n : ℂ) * σ) *
          (Complex.exp (((-Real.log n * t : ℝ) : ℂ) * I))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    field_simp

/-- A vertical limit of zero forces all visible Dirichlet coefficients to vanish. -/
theorem coeff_eq_zero_of_lSeries_vertical_tendsto_zero {f : ℕ → ℂ} {σ : ℝ}
    (hf : LSeriesSummable f σ)
    (hlim : Tendsto (fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℂ) * I)) atTop (𝓝 0)) :
    ∀ n, 0 < n → f n = 0 := by
  let a : ℕ → ℂ := fun n => LSeries.term f σ (n + 1)
  let ω : ℕ → ℝ := fun n => -Real.log (n + 1)
  have ha : Summable fun n => ‖a n‖ := (summable_nat_add_iff 1).mpr hf.norm
  have heq : (fun t : ℝ => LSeries f ((σ : ℂ) + (t : ℂ) * I)) =
      expSeriesCarrier a ω := by
    funext t
    have hft : LSeriesSummable f ((σ : ℂ) + (t : ℂ) * I) :=
      hf.of_re_le_re (by simp)
    have hsplit := hft.sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, LSeries.term_zero, zero_add] at hsplit
    rw [LSeries, ← hsplit]
    exact tsum_congr fun n => by
      simpa only [a, ω, Nat.cast_add, Nat.cast_one] using lSeries_term_vertical f σ t (n + 1)
  have hzero : ∀ t, expSeriesCarrier a ω t = 0 :=
    _root_.HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero
      (isBohrAlmostPeriodic_expSeriesCarrier ha ω) (heq ▸ hlim)
  have hω : Function.Injective ω := by
    intro i j hij
    have hlog : Real.log (i + 1) = Real.log (j + 1) := neg_injective hij
    have hij' := Real.log_injOn_pos (by positivity : 0 < (i : ℝ) + 1)
      (by positivity : 0 < (j : ℝ) + 1) hlog
    exact Nat.add_right_cancel (show i + 1 = j + 1 by exact_mod_cast hij')
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hk : a k = 0 := (bohrCoefficient_expSeriesCarrier ha hω k).symm.trans
    (bohrCoefficient_of_eq_zero hzero (ω k))
  change LSeries.term f σ (k + 1) = 0 at hk
  rw [LSeries.term_of_ne_zero (by omega), div_eq_zero_iff] at hk
  exact hk.resolve_right (Complex.cpow_ne_zero_iff.mpr
    (.inl (by exact_mod_cast Nat.succ_ne_zero k)))

end GaloisForLFunctions.SelbergClass
