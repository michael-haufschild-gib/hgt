import GaloisForLFunctions.RHTower.XiRealPartDerivativeCurvesCriterion
import GaloisForLFunctions.RHTower.XiCosineShiftVinogradovKorobovWindow

/-!
# The curves `Re ξ = 0` and `Im ξ' = 0` are disjoint near the line `Re s = 1`

An intersection point `s` of `{Re ξ = 0}` and `{Im ξ' = 0}` with `Re s > ½` lies in the disc
`|s − (½ + iγ)| ≤ β − ½` of a zero `ρ = β + iγ` with `β > ½`
(`exists_offline_zero_disc_of_curve_intersection`, reflected to `β > ½`). The Vinogradov–Korobov
region gives `β − ½ ≤ ½ − w(|γ|)` above `γ₁`, and `w` decreases. Hence
(`curves_disjoint_of_vinogradovKorobov`): for `|Im s| ≥ γ₁ + ½`, no intersection has
`Re s > 1 − w(|Im s| + ½)`.

By the curve criterion (`riemannHypothesis_iff_re_xi_eq_zero_imp_im_deriv_xi_ne_zero`), RH is the
extension of this disjointness from the Vinogradov–Korobov region to the whole right half-strip.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- **Disjointness near `Re s = 1`.** -/
theorem curves_disjoint_of_vinogradovKorobov :
    ∃ γ₁ : ℝ, Real.exp (Real.exp 1) ≤ γ₁ ∧ ∀ s : ℂ, 1 / 2 < s.re → γ₁ + 1 / 2 ≤ |s.im| →
      1 - vkHadamardWidth (|s.im| + 1 / 2) < s.re → (xi s).re = 0 → (deriv xi s).im ≠ 0 := by
  obtain ⟨γ₁, hγ₁, hvk⟩ := abs_re_sub_half_le_vinogradovKorobov
  refine ⟨γ₁, hγ₁, fun s hs1 hsim hsre hre him => ?_⟩
  obtain ⟨ρ, hρ, hρne, hdepth, hdisc⟩ := exists_offline_zero_disc_of_curve_intersection hs1 hre him
  -- reflect to `Re ρ > ½`
  obtain ⟨ρ', hρ', hρ're, hρ'im⟩ : ∃ ρ' : ℂ, xi ρ' = 0 ∧ ρ'.re = 1 / 2 + |ρ.re - 1 / 2| ∧
      ρ'.im = ρ.im := by
    rcases le_or_gt (1 / 2) ρ.re with hc | hc
    · exact ⟨ρ, hρ, by rw [abs_of_nonneg (by linarith)]; ring, rfl⟩
    · refine ⟨1 - (starRingEnd ℂ) ρ, by rw [xi_one_sub, xi_conj, hρ, map_zero], ?_, by simp⟩
      rw [abs_of_neg (by linarith)]; simp; ring
  have hzeta : riemannZeta ρ' = 0 := by
    have hne : ρ' ≠ 1 := by
      intro h1; have := xi_zero_re_lt_one hρ'; rw [h1] at this; simp at this
    exact (xi_eq_zero_iff (by rw [hρ're]; positivity) hne).mp hρ'
  have hb : |ρ.re - 1 / 2| < 1 / 2 := by
    have := xi_zero_re_lt_one hρ'; rw [hρ're] at this; linarith
  -- the ordinate of `ρ` is within `|Re ρ − ½| < ½` of `Im s`
  have hγclose : |s.im - ρ.im| ≤ |ρ.re - 1 / 2| := by
    have := Complex.abs_im_le_norm (s - (1 / 2 + (ρ.im : ℂ) * I))
    simp at this
    linarith
  have hγ : γ₁ ≤ |ρ'.im| := by
    rw [hρ'im]
    have := abs_sub_abs_le_abs_sub s.im ρ.im
    linarith
  have hρ'0 : 0 < ρ'.re := by rw [hρ're]; positivity
  have hdisp := hvk ρ' hρ'0 (xi_zero_re_lt_one hρ') hzeta hγ
  rw [hρ're, show 1 / 2 + |ρ.re - 1 / 2| - 1 / 2 = |ρ.re - 1 / 2| by ring,
    abs_of_nonneg (abs_nonneg _)] at hdisp
  have hup : |ρ'.im| ≤ |s.im| + 1 / 2 := by
    rw [hρ'im]
    have := abs_sub_abs_le_abs_sub ρ.im s.im
    rw [abs_sub_comm] at this
    linarith
  have hanti := vkHadamardWidth_antitoneOn
    (show |ρ'.im| ∈ Ici (Real.exp (Real.exp 1)) from le_trans hγ₁ hγ)
    (show |s.im| + 1 / 2 ∈ Ici (Real.exp (Real.exp 1)) by simp only [mem_Ici]; linarith) hup
  linarith

end

end RHTower
