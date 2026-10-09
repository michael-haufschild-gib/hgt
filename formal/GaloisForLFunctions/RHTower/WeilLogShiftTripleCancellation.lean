import GaloisForLFunctions.RHTower.RiemannAutocorrBalancedQuadratic
import GaloisForLFunctions.RHTower.WeilLogShiftFiniteTailCompensation

/-!
# Inverse-quartic cancellation on three actual arithmetic indices

The two endpoint weights cancel the first moment of the unequal logarithmic
gaps exactly. One weight is chosen per arithmetic index, independently of the
potential sampling point.
-/

noncomputable section

namespace RHTower

private theorem triple_log_step_bounds (x : ℝ) (hx : 0 < x) :
    0 < Real.log (x + 1) - Real.log x ∧
      Real.log (x + 1) - Real.log x ≤ x⁻¹ := by
  constructor
  · exact sub_pos.mpr (Real.log_lt_log hx (by linarith))
  · calc
      _ = Real.log ((x + 1) / x) := by rw [Real.log_div (by positivity) hx.ne']
      _ ≤ 1 / x := (log_step_bounds hx).2
      _ = _ := by rw [one_div]

/-- Every three consecutive actual arithmetic kernel columns admit a normalized
convex-endpoint cancellation with an inverse-quartic envelope. -/
theorem exists_pairedLogKernel_triple_inverseFourth_envelope :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, 1 ≤ n →
      ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ ∀ y : ℝ,
        |a * pairedLogKernel y n + (1 - a) * pairedLogKernel y (n + 2) -
          pairedLogKernel y (n + 1)| ≤ B * Real.exp (2 * |y|) * ((n : ℝ) ^ 4)⁻¹ := by
  obtain ⟨E, hE, hbalanced⟩ := exists_riemannAutocorr_balanced_quadratic_envelope
  refine ⟨2 * E, by positivity, ?_⟩
  intro n hn
  let x : ℝ := n
  have hx1 : 1 ≤ x := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hx : 0 < x := by linarith
  let d1 := Real.log (x + 1) - Real.log x
  let d2 := Real.log (x + 2) - Real.log (x + 1)
  have hd1 : 0 < d1 ∧ d1 ≤ x⁻¹ := triple_log_step_bounds x hx
  have hd2 : 0 < d2 ∧ d2 ≤ (x + 1)⁻¹ := by
    simpa only [d2, show (x + 1) + 1 = x + 2 by ring] using
      triple_log_step_bounds (x + 1) (by linarith)
  have hxle : x ≤ x + 1 := by linarith
  have hinv : (x + 1)⁻¹ ≤ x⁻¹ := by gcongr
  have hd2inv : d2 ≤ x⁻¹ := hd2.2.trans hinv
  have hd1abs : |d1| ≤ 1 := by
    rw [abs_of_pos hd1.1]
    exact hd1.2.trans (inv_le_one_of_one_le₀ hx1)
  have hd2abs : |d2| ≤ 1 := by
    rw [abs_of_pos hd2.1]
    exact hd2inv.trans (inv_le_one_of_one_le₀ hx1)
  have hS : 0 < d1 + d2 := by linarith [hd1.1, hd2.1]
  let a := d2 / (d1 + d2)
  let b := d1 / (d1 + d2)
  have ha : 0 ≤ a := (div_pos hd2.1 hS).le
  have hb : 0 ≤ b := (div_pos hd1.1 hS).le
  have hsum : a + b = 1 := by
    dsimp only [a, b]
    field_simp [hS.ne']; ring
  have ha1 : a ≤ 1 := by linarith
  have hbval : 1 - a = b := by linarith
  have hbal : a * (-d1) + b * d2 = 0 := by
    dsimp only [a, b]
    field_simp [hS.ne']; ring
  let V := a * d1 ^ 2 + b * d2 ^ 2
  have hV0 : 0 ≤ V := by dsimp only [V]; positivity
  have hvariance : V = d1 * d2 := by
    dsimp only [V, a, b]
    field_simp [hS.ne']
  have hV : V ≤ (x ^ 2)⁻¹ := by
    calc
      V = d1 * d2 := hvariance
      _ ≤ x⁻¹ * x⁻¹ := mul_le_mul hd1.2 hd2inv hd2.1.le (by positivity)
      _ = _ := by field_simp
  refine ⟨a, ha, ha1, ?_⟩
  intro y
  rw [hbval]
  let c := Real.log (x + 1)
  have hlog : 0 ≤ Real.log x := Real.log_natCast_nonneg n
  have hcg : Real.log x ≤ c := Real.log_le_log hx hxle
  have hc : 0 ≤ c := hlog.trans hcg
  have hexp : Real.exp (-(2 * Real.log x)) = (x ^ 2)⁻¹ := by
    rw [show -(2 * Real.log x) = -Real.log (x ^ 2) by
      rw [Real.log_pow]; norm_num only, Real.exp_neg, Real.exp_log (by positivity)]
  have hterm (z : ℝ) (hz : Real.log x - |y| ≤ |z|) :
      E * Real.exp (-(2 * |z|)) * V ≤ E * Real.exp (2 * |y|) * (x ^ 4)⁻¹ := by
    have he : Real.exp (-(2 * |z|)) ≤ Real.exp (2 * |y|) * (x ^ 2)⁻¹ := by
      calc
        _ ≤ Real.exp (2 * |y| + -(2 * Real.log x)) := Real.exp_le_exp.mpr (by linarith)
        _ = _ := by rw [Real.exp_add, hexp]
    calc
      _ ≤ (E * (Real.exp (2 * |y|) * (x ^ 2)⁻¹)) * (x ^ 2)⁻¹ :=
        mul_le_mul (mul_le_mul_of_nonneg_left he hE.le) hV hV0 (by positivity)
      _ = _ := by field_simp
  have hzplus : Real.log x - |y| ≤ |y + c| := by
    have h := abs_sub_abs_le_abs_add c y
    rw [abs_of_nonneg hc, add_comm c y] at h
    linarith
  have hzminus : Real.log x - |y| ≤ |y - c| := by
    have h := abs_sub_abs_le_abs_sub c y
    rw [abs_of_nonneg hc, abs_sub_comm c y] at h
    linarith
  have hp := hbalanced (y + c) (-d1) d2 a b
    (by simpa only [abs_neg] using hd1abs) hd2abs ha hb hbal
  have hm := hbalanced (y - c) d1 (-d2) a b hd1abs
    (by simpa only [abs_neg] using hd2abs) ha hb (by nlinarith [hbal])
  rw [show (-d1) ^ 2 = d1 ^ 2 by ring] at hp
  rw [show (-d2) ^ 2 = d2 ^ 2 by ring] at hm
  have hpB := hp.trans (hterm (y + c) hzplus)
  have hmB := hm.trans (hterm (y - c) hzminus)
  have hp0 : (y + c) + -d1 = y + Real.log n := by dsimp only [c, d1, x]; ring
  have hp2 : (y + c) + d2 = y + Real.log (n + 2 : ℕ) := by
    dsimp only [c, d2, x]
    push_cast
    ring
  have hm0 : (y - c) + d1 = y - Real.log n := by dsimp only [c, d1, x]; ring
  have hm2 : (y - c) + -d2 = y - Real.log (n + 2 : ℕ) := by
    dsimp only [c, d2, x]
    push_cast
    ring
  have hcp : y + c = y + Real.log (n + 1 : ℕ) := by dsimp only [c, x]; push_cast; rfl
  have hcm : y - c = y - Real.log (n + 1 : ℕ) := by dsimp only [c, x]; push_cast; rfl
  rw [hp0, hp2, hcp] at hpB
  rw [hm0, hm2, hcm] at hmB
  calc
    _ = |(a * (riemannAutocorr (y + Real.log n) - riemannAutocorr (y + Real.log (n + 1 : ℕ))) +
          b * (riemannAutocorr (y + Real.log (n + 2 : ℕ)) - riemannAutocorr (y + Real.log (n + 1 : ℕ)))) +
        (a * (riemannAutocorr (y - Real.log n) - riemannAutocorr (y - Real.log (n + 1 : ℕ))) +
          b * (riemannAutocorr (y - Real.log (n + 2 : ℕ)) - riemannAutocorr (y - Real.log (n + 1 : ℕ))))| := by
      congr 1
      unfold pairedLogKernel
      linear_combination (riemannAutocorr (y + Real.log (n + 1 : ℕ)) +
        riemannAutocorr (y - Real.log (n + 1 : ℕ))) * hsum
    _ ≤ _ := abs_add_le _ _
    _ ≤ (E * Real.exp (2 * |y|) * (x ^ 4)⁻¹) +
        (E * Real.exp (2 * |y|) * (x ^ 4)⁻¹) := add_le_add hpB hmB
    _ = _ := by dsimp only [x]; ring

end RHTower
