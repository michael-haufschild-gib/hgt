import GaloisForLFunctions.HTGeometry.GammaJumpTranslationEnergy

/-!
# Scale bounds for the conjugated Gamma second difference

Two estimates control `2F(L) − e^{-σs}F(L+s) − e^{σs}F(L−s)` at the two ends of the scale ray.

*Near zero* it is `O(s)` for a Lipschitz profile — the two translation increments contribute `Ks`
each and the two exponential defects `|1 − e^{∓σs}| ≤ σ s e^{σs}` contribute the rest.  Against the
kernel `1/(e^s − 1) ≤ 1/s` this gives a **bounded** integrand on `(0,1]`, which is what makes the
scale integral converge at the singular end.

*Far out* it is `O(e^{σs})` for a bounded profile, and the kernel decays like `2e^{-s}`, so the
product decays like `e^{-(1-σ)s}` — convergent exactly when `σ < 1`.

Together these are the joint integrability that lets the `L`- and `s`-integrations of the Gamma
pairing be exchanged.
-/

namespace GaloisForLFunctions.HTGeometry

/-- `|1 − e^{x}| ≤ |x| e^{|x|}`. -/
theorem abs_one_sub_exp_le (x : ℝ) : |1 - Real.exp x| ≤ |x| * Real.exp |x| := by
  rcases le_total x 0 with hx | hx
  · have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx
    have h2 : 1 - Real.exp x ≤ -x := by
      have := Real.add_one_le_exp x
      linarith
    have h3 : (0 : ℝ) ≤ 1 - Real.exp x := by linarith
    rw [abs_of_nonneg h3, abs_of_nonpos hx]
    calc 1 - Real.exp x ≤ -x := h2
      _ ≤ -x * Real.exp (-x) := by
          have he : (1 : ℝ) ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
          nlinarith [neg_nonneg.mpr hx]
  · have h1 : (1 : ℝ) ≤ Real.exp x := Real.one_le_exp hx
    have h2 : Real.exp x - 1 ≤ x * Real.exp x := by
      have hneg := Real.add_one_le_exp (-x)
      have hex : (0 : ℝ) < Real.exp x := Real.exp_pos x
      have hmul : Real.exp (-x) * Real.exp x = 1 := by
        rw [← Real.exp_add]; simp
      have hstep := mul_le_mul_of_nonneg_right hneg hex.le
      rw [hmul] at hstep
      nlinarith [hstep]
    rw [abs_of_nonpos (by linarith), abs_of_nonneg hx]
    linarith

/-- **The near-zero bound.**  A Lipschitz profile makes the conjugated second difference linear in
the scale. -/
theorem abs_shiftedSecondDifference_le_mul {F : ℝ → ℝ} {K B σ : ℝ}
    (hK : ∀ x y : ℝ, |F x - F y| ≤ K * |x - y|) (hB : ∀ x, |F x| ≤ B)
    (hσ : 0 ≤ σ) {s : ℝ} (hs0 : 0 ≤ s) (L : ℝ) :
    |shiftedSecondDifference σ F L s| ≤ (2 * K + 2 * B * σ * Real.exp (σ * s)) * s := by
  have hsplit : shiftedSecondDifference σ F L s
      = (F L - F (L + s)) + (F L - F (L - s))
        + (1 - Real.exp (-(σ * s))) * F (L + s) + (1 - Real.exp (σ * s)) * F (L - s) := by
    rw [shiftedSecondDifference]
    ring
  have h1 : |F L - F (L + s)| ≤ K * s := by
    have := hK L (L + s)
    have habs : |L - (L + s)| = s := by
      rw [show L - (L + s) = -s by ring, abs_neg, abs_of_nonneg hs0]
    rwa [habs] at this
  have h2 : |F L - F (L - s)| ≤ K * s := by
    have := hK L (L - s)
    have habs : |L - (L - s)| = s := by
      rw [show L - (L - s) = s by ring, abs_of_nonneg hs0]
    rwa [habs] at this
  have hσs : 0 ≤ σ * s := mul_nonneg hσ hs0
  have h3 : |1 - Real.exp (-(σ * s))| ≤ σ * s * Real.exp (σ * s) := by
    have := abs_one_sub_exp_le (-(σ * s))
    rwa [abs_neg, abs_of_nonneg hσs] at this
  have h4 : |1 - Real.exp (σ * s)| ≤ σ * s * Real.exp (σ * s) := by
    have := abs_one_sub_exp_le (σ * s)
    rwa [abs_of_nonneg hσs] at this
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hexp : 0 < Real.exp (σ * s) := Real.exp_pos _
  rw [hsplit]
  calc |(F L - F (L + s)) + (F L - F (L - s))
        + (1 - Real.exp (-(σ * s))) * F (L + s) + (1 - Real.exp (σ * s)) * F (L - s)|
      ≤ |(F L - F (L + s)) + (F L - F (L - s)) + (1 - Real.exp (-(σ * s))) * F (L + s)|
        + |(1 - Real.exp (σ * s)) * F (L - s)| := abs_add_le _ _
    _ ≤ (|(F L - F (L + s)) + (F L - F (L - s))|
        + |(1 - Real.exp (-(σ * s))) * F (L + s)|)
        + |(1 - Real.exp (σ * s)) * F (L - s)| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ ((|F L - F (L + s)| + |F L - F (L - s)|)
        + |(1 - Real.exp (-(σ * s))) * F (L + s)|)
        + |(1 - Real.exp (σ * s)) * F (L - s)| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ ((K * s + K * s) + σ * s * Real.exp (σ * s) * B) + σ * s * Real.exp (σ * s) * B := by
          gcongr
          · rw [abs_mul]
            exact mul_le_mul h3 (hB _) (abs_nonneg _) (by positivity)
          · rw [abs_mul]
            exact mul_le_mul h4 (hB _) (abs_nonneg _) (by positivity)
    _ = (2 * K + 2 * B * σ * Real.exp (σ * s)) * s := by ring

/-- **The far bound.**  A bounded profile makes the conjugated second difference grow no faster
than the conjugation itself. -/
theorem abs_shiftedSecondDifference_le_exp {F : ℝ → ℝ} {B σ : ℝ}
    (hB : ∀ x, |F x| ≤ B) (hσ : 0 ≤ σ) {s : ℝ} (hs0 : 0 ≤ s) (L : ℝ) :
    |shiftedSecondDifference σ F L s| ≤ 4 * B * Real.exp (σ * s) := by
  have hBnn : 0 ≤ B := le_trans (abs_nonneg _) (hB 0)
  have hσs : 0 ≤ σ * s := mul_nonneg hσ hs0
  have he1 : Real.exp (-(σ * s)) ≤ Real.exp (σ * s) := Real.exp_le_exp.mpr (by linarith)
  have he0 : (0 : ℝ) < Real.exp (-(σ * s)) := Real.exp_pos _
  have hge : (1 : ℝ) ≤ Real.exp (σ * s) := Real.one_le_exp hσs
  rw [shiftedSecondDifference]
  calc |2 * F L - Real.exp (-(σ * s)) * F (L + s) - Real.exp (σ * s) * F (L - s)|
      ≤ |2 * F L - Real.exp (-(σ * s)) * F (L + s)| + |Real.exp (σ * s) * F (L - s)| :=
        abs_sub _ _
    _ ≤ (|2 * F L| + |Real.exp (-(σ * s)) * F (L + s)|) + |Real.exp (σ * s) * F (L - s)| := by
        gcongr
        exact abs_sub _ _
    _ ≤ (2 * B + Real.exp (σ * s) * B) + Real.exp (σ * s) * B := by
        gcongr
        · rw [abs_mul]
          simpa using mul_le_mul_of_nonneg_left (hB L) (by norm_num : (0:ℝ) ≤ 2)
        · rw [abs_mul, abs_of_pos he0]
          exact mul_le_mul he1 (hB _) (abs_nonneg _) (by positivity)
        · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_left (hB _) (by positivity)
    _ ≤ 4 * B * Real.exp (σ * s) := by nlinarith

end GaloisForLFunctions.HTGeometry
