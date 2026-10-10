import GaloisForLFunctions.HTGeometry.AnalyticZeroHeightDescent
import GaloisForLFunctions.RHTower.ZetaBranchingDilationCascade

/-!
# Dilation cascades by height descent

`riemannZeta_ne_zero_of_branching` closes a dilation cascade `ρ ↦ 1 - ρ/k` by driving an orbit to
the real axis, which needs a uniform contraction rate `k ≥ κ > 1`. This module closes it by height
descent instead (`GaloisForLFunctions.HTGeometry.AnalyticOnNhd.eqOn_zero_of_imDescent`): a
non-real zero of minimal height in a compact band would have a lower descendant.

* `riemannZeta_ne_zero_of_imDescent`: if every non-real zero of `ζ` in a compact set `K ∌ 1` has a
  non-real zero in `K` of strictly smaller `|Im|`, then `ζ` has no non-real zero in `K`.
* `riemannZeta_ne_zero_of_dilationDescent`: if every zero with real part in `[a, b] ⊂ (0, 1)` has
  `ζ(ρ/k) = 0` for some `k > 1` from a set `D`, and the band is invariant under every
  `x ↦ 1 - x/k`, `k ∈ D`, then `ζ` has no zero with real part in `[a, b]`. No uniform lower bound
  on `D` is needed, so dilations `k → 1⁺` are allowed.
-/

open Complex

namespace RHTower.DilationCascade

noncomputable section

/-- `ζ` is analytic on `ℂ \ {1}`. -/
theorem analyticOnNhd_riemannZeta_compl_one : AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (differentiableAt_riemannZeta hz).differentiableWithinAt) isOpen_compl_singleton

/-- **Height descent for `ζ`.** -/
theorem riemannZeta_ne_zero_of_imDescent {K : Set ℂ} (hK : IsCompact K) (h1 : (1 : ℂ) ∉ K)
    (hdesc : ∀ z ∈ K, riemannZeta z = 0 → z.im ≠ 0 →
      ∃ w ∈ K, riemannZeta w = 0 ∧ w.im ≠ 0 ∧ |w.im| < |z.im|)
    {s : ℂ} (hs : s ∈ K) (him : s.im ≠ 0) : riemannZeta s ≠ 0 := by
  intro hz
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) _).isPreconnected
  have hKU : K ⊆ {1}ᶜ := fun z hzK h => h1 (Set.mem_singleton_iff.mp h ▸ hzK)
  have heq := GaloisForLFunctions.HTGeometry.AnalyticOnNhd.eqOn_zero_of_imDescent
    analyticOnNhd_riemannZeta_compl_one hconn hK hKU hdesc hs hz him
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  exact riemannZeta_ne_zero_of_one_lt_re (by norm_num : (1 : ℝ) < (2 : ℂ).re) (heq h2)

/-- **Dilation descent.** -/
theorem riemannZeta_ne_zero_of_dilationDescent {a b : ℝ} {D : Set ℝ} (ha : 0 < a) (hb : b < 1)
    (hD : ∀ k ∈ D, 1 < k)
    (hinv : ∀ k ∈ D, ∀ x : ℝ, a ≤ x → x ≤ b → a ≤ 1 - x / k ∧ 1 - x / k ≤ b)
    (hbranch : ∀ ρ : ℂ, riemannZeta ρ = 0 → a ≤ ρ.re → ρ.re ≤ b → ρ.im ≠ 0 →
      ∃ k ∈ D, riemannZeta (ρ / k) = 0)
    {s : ℂ} (h1 : a ≤ s.re) (h2 : s.re ≤ b) : riemannZeta s ≠ 0 := by
  by_cases him : s.im = 0
  · have hs : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hs]
    exact riemannZeta_ofReal_ne_zero (by linarith) (by linarith)
  set K : Set ℂ := {z | a ≤ z.re ∧ z.re ≤ b ∧ |z.im| ≤ |s.im|} with hKdef
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hc : IsClosed ({z : ℂ | a ≤ z.re} ∩ {z | z.re ≤ b} ∩ {z | |z.im| ≤ |s.im|}) :=
        ((isClosed_le continuous_const Complex.continuous_re).inter
          (isClosed_le Complex.continuous_re continuous_const)).inter
          (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
      convert hc using 1
      ext z
      simp only [hKdef, Set.mem_setOf_eq, Set.mem_inter_iff, and_assoc]
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |s.im|)).subset ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right]
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 1 + |s.im| := by
            have : |z.re| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1], by linarith [hz.2.1]⟩
            linarith [hz.2.2]
  have h1K : (1 : ℂ) ∉ K := fun h => by
    have := h.2.1
    simp at this
    linarith
  refine riemannZeta_ne_zero_of_imDescent hKc h1K ?_ ⟨h1, h2, le_rfl⟩ him
  rintro z ⟨hza, hzb, hzs⟩ hz0 hzim
  obtain ⟨k, hkD, hk0⟩ := hbranch z hz0 hza hzb hzim
  have hk : 1 < k := hD k hkD
  have hkpos : 0 < k := by linarith
  have hdre : (z / k).re = z.re / k := by
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) from rfl, Complex.div_ofReal_re]
  have hdim : (z / k).im = z.im / k := by
    rw [show (k : ℂ) = ((k : ℝ) : ℂ) from rfl, Complex.div_ofReal_im]
  have hre0 : 0 < (z / k).re := by rw [hdre]; exact div_pos (by linarith) hkpos
  have hre1 : (z / k).re < 1 := by rw [hdre, div_lt_one hkpos]; linarith
  have hwim : (1 - z / k).im = -(z.im / k) := by
    simp only [Complex.sub_im, Complex.one_im, zero_sub, hdim]
  have habs : |(1 - z / k).im| = |z.im| / k := by
    rw [hwim, abs_neg, abs_div, abs_of_pos hkpos]
  have hzpos : 0 < |z.im| := abs_pos.mpr hzim
  refine ⟨1 - z / k, ⟨?_, ?_, ?_⟩, (riemannZeta_one_sub_eq_zero_iff hre0 hre1).mpr hk0, ?_, ?_⟩
  · simp only [Complex.sub_re, Complex.one_re, hdre]; exact (hinv k hkD z.re hza hzb).1
  · simp only [Complex.sub_re, Complex.one_re, hdre]; exact (hinv k hkD z.re hza hzb).2
  · rw [habs]; exact (div_le_self (abs_nonneg _) hk.le).trans hzs
  · rw [hwim]; exact neg_ne_zero.mpr (div_ne_zero hzim hkpos.ne')
  · rw [habs]; exact div_lt_self hzpos hk

end

end RHTower.DilationCascade
