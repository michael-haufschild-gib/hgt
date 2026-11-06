import GaloisForLFunctions.VerifiedHeightRungs.JensenEntries
import GaloisForLFunctions.ThetaCuspSections.AllApertureFiniteRankCriterion

/-!
# Theta sections from verified zeros

If RH holds through `T + 1`, the current is nonnegative on `|b| ≤ T` at every aperture: only zeros with ordinate
within `½` of `b` can obstruct, and these are on the line. With the window criterion at every aperture, rank `N` is
positive definite at every `0 < a ≤ 3/4` once RH holds through `D (N+1)³ + 1`.
-/

open Complex
open RHTower
open GaloisForLFunctions.ThetaCuspSections.CriticalCollar
open GaloisForLFunctions.ThetaCuspSections.LogarithmicCollar

namespace GaloisForLFunctions.VerifiedHeightRungs

/-- Verified zeros make the current nonnegative at every positive aperture. -/
theorem current_nonneg_of_rhVerifiedThrough {T a b : ℝ} (ha : 0 < a) (hRH : RHVerifiedThrough (T + 1))
    (hb : |b| ≤ T) : 0 ≤ current a b := by
  apply current_nonneg_of_re_logDeriv_nonneg
  have hre : (1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I : ℂ).re = 1 / 2 + a := by
    norm_num [Complex.mul_re, Complex.mul_im]
  have him : (1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I : ℂ).im = b := by
    norm_num [Complex.mul_re, Complex.mul_im]
  by_cases hxi : xi (1 / 2 + ((b : ℂ) - (a : ℂ) * I) * I) = 0
  · rw [logDeriv_apply, hxi, div_zero, Complex.zero_re]
  refine re_logDeriv_xi_nonneg_of_window (by rw [hre]; linarith only [ha]) hxi fun q hq => ?_
  rw [him] at hq
  have hγ : |(xiSpectralPoint q).re| ≤ T + 1 := by
    rw [re_xiSpectralPoint]
    have h1 : |(q.1 : ℂ).im| ≤ |b| + |b - (q.1 : ℂ).im| := by
      have := abs_sub_abs_le_abs_sub ((q.1 : ℂ).im) b
      rw [abs_sub_comm ((q.1 : ℂ).im) b] at this
      linarith only [this]
    linarith only [h1, hb, hq]
  have hd := im_xiSpectralPoint_eq_zero hRH q hγ
  rw [im_xiSpectralPoint] at hd
  have hβ : (q.1 : ℂ).re - 1 / 2 = 0 := by linarith only [hd]
  rw [hβ, hre, him]
  have e : (1 / 2 + a - 1 / 2 : ℝ) = a := by ring
  rw [e]
  have h2 := sq_nonneg (b - (q.1 : ℂ).im)
  have h3 : 0 < a ^ 2 := by positivity
  norm_num
  linarith only [h2, h3]

/-- **Theta rung.** There is `D` such that RH through `D (N+1)³ + 1` makes the signed section of rank `N` positive
definite at every aperture `0 < a ≤ 3/4`. -/
theorem exists_signedHankel_posDef_of_rhVerifiedThrough : ∃ D : ℝ, 4 ≤ D ∧ ∀ N : ℕ,
    RHVerifiedThrough (D * ((N : ℝ) + 1) ^ 3 + 1) → ∀ a : ℝ, 0 < a → a ≤ 3 / 4 →
      (thetaCuspCenterMixedSignedHankel a N).PosDef := by
  obtain ⟨D, hD, h⟩ := exists_signedHankel_posDef_of_current_nonneg
  exact ⟨D, hD, fun N hRH a ha ha2 => h N a ha ha2 fun b hb => current_nonneg_of_rhVerifiedThrough ha hRH hb⟩

end GaloisForLFunctions.VerifiedHeightRungs

#print axioms GaloisForLFunctions.VerifiedHeightRungs.exists_signedHankel_posDef_of_rhVerifiedThrough
