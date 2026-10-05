import GaloisForLFunctions.RHTower.BoundedExponentPoissonNonlanding
import GaloisForLFunctions.RHTower.ZetaVerticalSqrtBound

/-!
# Jensen's formula for zeta on the half-plane `Re s > ½`

The map `w ↦ s = 1/(1 - w)` carries the unit disc onto the half-plane `Re s > ½`, the unit circle
minus `1` onto the critical line, and `0` to the pole `s = 1`.  The entire function
`g(s) = (s - 1) ζ(s)` (`zetaEntire`) has `g(1) = 1`, so `G(w) = g(1/(1 - w))` is analytic on the
closed disc of every radius `r < 1` with `G(0) = 1`.  Its zeros in the open disc are the points
`u = 1 - 1/ρ` for the zeros `ρ` of `ζ` with `Re ρ > ½`, and `1/|u| = |ρ|/|1 - ρ|`.

Jensen's formula then bounds the circle averages of `log |G|` from below by
`Σ_u log (r/|u|)`, and the bound `|ζ(s)| ≤ 5 √(|s| + 2)` on `Re s ≥ ½` gives
`log |G(w)| ≤ A - 2 log |1 - w|` on the closed disc.
-/

open Complex Metric Real

namespace RHTower

noncomputable section

/-- The map `w ↦ 1/(1 - w)` from the unit disc onto the half-plane `Re s > ½`. -/
def halfPlaneOfDisc (w : ℂ) : ℂ := (1 - w)⁻¹

/-- `G(w) = (s - 1) ζ(s)` at `s = 1/(1 - w)`. -/
def zetaDisc (w : ℂ) : ℂ := zetaEntire (halfPlaneOfDisc w)

theorem re_halfPlaneOfDisc_ge {w : ℂ} (hw : ‖w‖ ≤ 1) (hw1 : w ≠ 1) :
    1 / 2 ≤ (halfPlaneOfDisc w).re := by
  have hne : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hpos : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr hne
  have hw2 : w.re * w.re + w.im * w.im ≤ 1 := by
    have : Complex.normSq w ≤ 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
    rwa [Complex.normSq_apply] at this
  unfold halfPlaneOfDisc
  rw [Complex.inv_re, le_div_iff₀ hpos, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  nlinarith

theorem re_halfPlaneOfDisc_gt {w : ℂ} (hw : ‖w‖ < 1) : 1 / 2 < (halfPlaneOfDisc w).re := by
  have hw1 : w ≠ 1 := by rintro rfl; simp at hw
  have hne : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hpos : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr hne
  have hw2 : w.re * w.re + w.im * w.im < 1 := by
    have : Complex.normSq w < 1 := by
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
    rwa [Complex.normSq_apply] at this
  unfold halfPlaneOfDisc
  rw [Complex.inv_re, lt_div_iff₀ hpos, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  nlinarith

theorem zetaEntire_eval_one : zetaEntire 1 = 1 := by
  rw [zetaEntire, sub_self, zero_mul, zero_add, Complex.Gammaℝ_one, inv_one]

theorem zetaDisc_zero : zetaDisc 0 = 1 := by
  rw [zetaDisc, halfPlaneOfDisc, sub_zero, inv_one, zetaEntire_eval_one]

theorem differentiableOn_zetaDisc : DifferentiableOn ℂ zetaDisc {1}ᶜ := by
  intro w hw
  have hne : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  refine (differentiable_zetaEntire _).comp_differentiableWithinAt (s := {1}ᶜ) w ?_
  exact ((differentiableAt_const _).sub differentiableAt_id).inv hne |>.differentiableWithinAt

theorem analyticAt_zetaDisc {w : ℂ} (hw : w ≠ 1) : AnalyticAt ℂ zetaDisc w :=
  differentiableOn_zetaDisc.analyticAt (isOpen_compl_singleton.mem_nhds hw)

theorem analyticOnNhd_zetaDisc_closedBall {r : ℝ} (hr : r < 1) :
    AnalyticOnNhd ℂ zetaDisc (closedBall 0 r) := by
  intro w hw
  refine analyticAt_zetaDisc ?_
  rintro rfl
  rw [mem_closedBall, dist_zero_right, norm_one] at hw
  linarith

/-- A zero `ρ` of `ζ` with `Re ρ > ½` gives the disc zero `u = 1 - 1/ρ`, with
`|u| = |1 - ρ|/|ρ| < 1`. -/
theorem zetaDisc_one_sub_inv {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re) :
    zetaDisc (1 - ρ⁻¹) = 0 ∧ ‖1 - ρ⁻¹‖ = ‖1 - ρ‖ / ‖ρ‖ ∧ ‖1 - ρ⁻¹‖ < 1 := by
  have hρ0 : ρ ≠ 0 := by rintro rfl; simp at hre; linarith
  have hρ1 : ρ ≠ 1 := by
    rintro rfl
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hρ
  have hnorm : ‖1 - ρ⁻¹‖ = ‖1 - ρ‖ / ‖ρ‖ := by
    rw [show (1 : ℂ) - ρ⁻¹ = -(1 - ρ) / ρ by field_simp; ring, norm_div, norm_neg]
  refine ⟨?_, hnorm, ?_⟩
  · rw [zetaDisc, halfPlaneOfDisc, sub_sub_cancel, inv_inv, zetaEntire_eq hρ1, hρ, mul_zero]
  · rw [hnorm, div_lt_one (norm_pos_iff.mpr hρ0)]
    have h1 : ‖1 - ρ‖ ^ 2 < ‖ρ‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
      nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

/-- **Jensen's lower bound.**  If `Φ` is analytic on the closed disc of radius `r` with
`Φ(0) ≠ 0`, then for finitely many zeros `u` of `Φ` with `|u| < r`,
`Σ_u log (r/|u|) + log |Φ(0)| ≤ (circle average of log |Φ| at radius r)`. -/
theorem sum_log_div_norm_add_log_le_circleAverage {Φ : ℂ → ℂ} {r : ℝ} (hr0 : 0 < r)
    (han : AnalyticOnNhd ℂ Φ (closedBall 0 r)) (h0 : Φ 0 ≠ 0) {U : Finset ℂ}
    (hU : ∀ u ∈ U, Φ u = 0) (hUr : ∀ u ∈ U, ‖u‖ < r) :
    ∑ u ∈ U, Real.log (r / ‖u‖) + Real.log ‖Φ 0‖
      ≤ circleAverage (fun w => Real.log ‖Φ w‖) 0 r := by
  have habs : |r| = r := abs_of_pos hr0
  have han' : AnalyticOnNhd ℂ Φ (closedBall 0 |r|) := by rw [habs]; exact han
  have hjensen := han'.circleAverage_log_norm hr0.ne' h0
  rw [hjensen, add_le_add_iff_right]
  set D := MeromorphicOn.divisor Φ (closedBall (0 : ℂ) |r|) with hD
  set φ : ℂ → ℝ := fun u => (D u : ℝ) * Real.log (r * ‖0 - u‖⁻¹) with hφ
  have hfin := D.finiteSupport (isCompact_closedBall 0 |r|)
  have hsupp : Function.support φ ⊆ ↑(hfin.toFinset ∪ U) := by
    intro u hu
    have : D u ≠ 0 := by
      intro h0'; apply hu; simp only [hφ, h0', Int.cast_zero, zero_mul]
    simp only [Finset.coe_union, Set.Finite.coe_toFinset, Set.mem_union]
    exact Or.inl this
  rw [finsum_eq_sum_of_support_subset φ hsupp]
  have hDnn : ∀ u, 0 ≤ D u := fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg han' u
  have hφnn : ∀ u, 0 ≤ φ u := by
    intro u
    by_cases hu : u ∈ closedBall (0 : ℂ) |r|
    · refine mul_nonneg (by exact_mod_cast hDnn u) ?_
      rw [zero_sub, norm_neg]
      rcases eq_or_ne u 0 with hu0 | hu0
      · rw [hu0, norm_zero, inv_zero, mul_zero, Real.log_zero]
      · apply Real.log_nonneg
        rw [mem_closedBall, dist_zero_right, habs] at hu
        rw [← div_eq_mul_inv, le_div_iff₀ (norm_pos_iff.mpr hu0), one_mul]
        exact hu
    · simp only [hφ, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu, Int.cast_zero,
        zero_mul, le_refl]
  have hterm : ∀ u ∈ U, Real.log (r / ‖u‖) ≤ φ u := by
    intro u hu
    have hu0 : u ≠ 0 := by
      rintro rfl; exact h0 (hU 0 hu)
    have hur : ‖u‖ < r := hUr u hu
    have humem : u ∈ closedBall (0 : ℂ) |r| := by
      rw [mem_closedBall, dist_zero_right, habs]; exact hur.le
    have hlog0 : 0 ≤ Real.log (r / ‖u‖) :=
      Real.log_nonneg (by rw [le_div_iff₀ (norm_pos_iff.mpr hu0), one_mul]; exact hur.le)
    have hD1 : 1 ≤ D u := by
      rw [hD, MeromorphicOn.AnalyticOnNhd.divisor_apply han' humem]
      have hana := han' u humem
      have hne0 : analyticOrderAt Φ u ≠ 0 := by
        rw [Ne, hana.analyticOrderAt_eq_zero, not_not]; exact hU u hu
      have hzero_mem : (0 : ℂ) ∈ closedBall (0 : ℂ) |r| := mem_closedBall_self (abs_nonneg r)
      have hnetop : analyticOrderAt Φ u ≠ ⊤ :=
        AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected han'
          (convex_closedBall _ _).isPreconnected hzero_mem humem (by
            rw [Ne, (han' 0 hzero_mem).analyticOrderAt_eq_zero.mpr h0]
            exact ENat.zero_ne_top)
      obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hnetop
      rw [← hm] at hne0 ⊢
      have hm1 : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · exact absurd (by rw [h]; rfl) hne0
        · exact h
      simp only [ENat.map_coe, WithTop.untop₀_coe]
      exact_mod_cast hm1
    have heq : Real.log (r * ‖0 - u‖⁻¹) = Real.log (r / ‖u‖) := by
      rw [zero_sub, norm_neg, div_eq_mul_inv]
    simp only [hφ, heq]
    have hD1R : (1 : ℝ) ≤ (D u : ℝ) := by exact_mod_cast hD1
    nlinarith
  calc ∑ u ∈ U, Real.log (r / ‖u‖) ≤ ∑ u ∈ U, φ u := Finset.sum_le_sum hterm
    _ ≤ ∑ u ∈ hfin.toFinset ∪ U, φ u :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          fun u _ _ => hφnn u

/-- **Jensen's lower bound for `G`.**  For finitely many zeros `u` of `G` in the disc of radius
`r < 1`, `Σ_u log (r/|u|) ≤ (circle average of log |G| at radius r)`. -/
theorem sum_log_div_norm_le_circleAverage_zetaDisc {U : Finset ℂ}
    (hU : ∀ u ∈ U, zetaDisc u = 0) {r : ℝ} (hr0 : 0 < r) (hr : r < 1)
    (hUr : ∀ u ∈ U, ‖u‖ < r) :
    ∑ u ∈ U, Real.log (r / ‖u‖) ≤ circleAverage (fun w => Real.log ‖zetaDisc w‖) 0 r := by
  have h := sum_log_div_norm_add_log_le_circleAverage hr0 (analyticOnNhd_zetaDisc_closedBall hr)
    (by rw [zetaDisc_zero]; exact one_ne_zero) hU hUr
  rwa [zetaDisc_zero, norm_one, Real.log_one, add_zero] at h

/-- Polynomial growth of `(s - 1) ζ(s)` on `Re s ≥ ½`. -/
theorem exists_norm_zetaEntire_le :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → ‖zetaEntire s‖ ≤ K * (‖s‖ + 2) ^ 2 := by
  obtain ⟨K₀, hK₀⟩ := (isCompact_closedBall (1 : ℂ) 1).exists_bound_of_continuousOn
    (differentiable_zetaEntire.continuous.continuousOn)
  refine ⟨max K₀ 5 + 1, by linarith [le_max_right K₀ 5], fun s hs => ?_⟩
  have hs2 : (1 : ℝ) ≤ (‖s‖ + 2) ^ 2 := by nlinarith [norm_nonneg s]
  have hK : 0 ≤ max K₀ 5 := le_trans (by norm_num) (le_max_right _ _)
  by_cases h1 : ‖s - 1‖ ≤ 1
  · have hmem : s ∈ closedBall (1 : ℂ) 1 := by rw [mem_closedBall, dist_eq_norm]; exact h1
    calc ‖zetaEntire s‖ ≤ K₀ := hK₀ s hmem
      _ ≤ max K₀ 5 + 1 := by linarith [le_max_left K₀ 5]
      _ = (max K₀ 5 + 1) * 1 := (mul_one _).symm
      _ ≤ (max K₀ 5 + 1) * (‖s‖ + 2) ^ 2 := mul_le_mul_of_nonneg_left hs2 (by linarith)
  · have hsne : s ≠ 1 := by rintro rfl; simp at h1
    have hζ := norm_riemannZeta_le_sqrt_norm_add_two_half hs one_pos (not_le.mp h1).le
    rw [zetaEntire_eq hsne, norm_mul]
    have hsub : ‖s - 1‖ ≤ ‖s‖ + 2 := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖s‖ + 2 := by rw [norm_one]; linarith
    have hsq : Real.sqrt (‖s‖ + 2) ≤ ‖s‖ + 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [norm_nonneg s]
    have hζ' : ‖riemannZeta s‖ ≤ 5 * (‖s‖ + 2) := by
      have : (2 + 1 / (1 : ℝ) + 2) = 5 := by norm_num
      rw [this] at hζ
      linarith
    calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ (‖s‖ + 2) * (5 * (‖s‖ + 2)) :=
          mul_le_mul hsub hζ' (norm_nonneg _) (by positivity)
      _ = 5 * (‖s‖ + 2) ^ 2 := by ring
      _ ≤ (max K₀ 5 + 1) * (‖s‖ + 2) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          linarith [le_max_right K₀ 5]

/-- **The growth bound on the closed disc.**  `log |G(w)| ≤ A - 2 log |1 - w|` for `|w| ≤ 1`,
`w ≠ 1`. -/
theorem exists_log_norm_zetaDisc_le :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → w ≠ 1 →
      Real.log ‖zetaDisc w‖ ≤ A - 2 * Real.log ‖1 - w‖ := by
  obtain ⟨K, hK1, hK⟩ := exists_norm_zetaEntire_le
  refine ⟨Real.log K + 2 * Real.log 5, by
    have := Real.log_nonneg hK1
    have : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
    linarith, fun w hw hw1 => ?_⟩
  have hne : (1 - w) ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have hn0 : 0 < ‖1 - w‖ := norm_pos_iff.mpr hne
  have hn2 : ‖1 - w‖ ≤ 2 := by
    calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  have hs : ‖halfPlaneOfDisc w‖ = 1 / ‖1 - w‖ := by
    rw [halfPlaneOfDisc, norm_inv, one_div]
  have hbound : ‖halfPlaneOfDisc w‖ + 2 ≤ 5 / ‖1 - w‖ := by
    rw [hs, div_add' _ _ _ hn0.ne', div_le_div_iff_of_pos_right hn0]
    nlinarith
  have hG := hK _ (re_halfPlaneOfDisc_ge hw hw1)
  have hlog2 : 2 * Real.log ‖1 - w‖ ≤ 2 * Real.log 5 := by
    have := Real.log_le_log hn0 (by linarith : ‖1 - w‖ ≤ 5)
    linarith
  rcases eq_or_ne (zetaDisc w) 0 with h0 | h0
  · rw [h0, norm_zero, Real.log_zero]
    have := Real.log_nonneg hK1
    linarith
  · have hpos : 0 < ‖zetaDisc w‖ := norm_pos_iff.mpr h0
    have h1 : ‖zetaDisc w‖ ≤ K * (5 / ‖1 - w‖) ^ 2 := by
      refine hG.trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
      exact pow_le_pow_left₀ (by positivity) hbound 2
    have h2 := Real.log_le_log hpos h1
    rw [Real.log_mul (by linarith) (by positivity), Real.log_pow, Real.log_div (by norm_num)
      hn0.ne'] at h2
    push_cast at h2
    linarith

end

end RHTower
