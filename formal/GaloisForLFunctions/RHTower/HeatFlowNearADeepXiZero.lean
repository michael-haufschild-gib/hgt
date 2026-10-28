import GaloisForLFunctions.RHTower.XiZeroFreeCofactorNearAnOrdinate
import GaloisForLFunctions.RHTower.GaussianAverageOfALocallyTameFunction
import GaloisForLFunctions.RHTower.XiLineHalfGaussInstance
import GaloisForLFunctions.RHTower.DeBruijnDefectPairPersistence

/-!
# The heat flow stays close to `Ξ` near a zero, for a polylogarithmic time

Write `σ(z) = 1/2 + iz`, so `Ξ(z) = ξ(σ(z))`.  Near an ordinate `T` factor `ξ = P·g` on
`B(c, 12)`, `c = 2 + iT`, with the cofactor bound `‖g′/g‖ ≤ K` on `B(c, 11)`
(`exists_xi_cofactor_near_ordinate`).  For `σ(z)` at distance `d_ρ` from each zero `ρ` of the
ball (multiplicity `m_ρ`):

* **Ratio** (`norm_xi_le_mul_exp_of_cofactor`).  `‖ξ(s)‖ ≤ ‖ξ(σ(z))‖ e^{a‖s − σ(z)‖}` on `B(c, 11)`,
  `a = Σ m_ρ/d_ρ + K`.  The polynomial factor gains at most `e^{m_ρ‖s − σ(z)‖/d_ρ}` per zero; the
  cofactor gains at most `e^{K‖s − σ(z)‖}` (Grönwall along the segment).
* **Tail** (`norm_XiC_vertical_le`).  Along the horizontal line through `σ(z)`, the growth beyond
  the ball (`norm_xiLine_le_far`, and the reflection `ξ(1 − s̄) = conj ξ(s)`) gives
  `‖Ξ(z − iu)‖ ≤ e^{8a} ‖Ξ(z)‖ e^{(a + log X + 2)|u|} e^{u²/8t}` for `|u| > 1`, `X = Im σ(z)`.
* **Comparison** (`norm_riemannHeat_sub_XiC_lt`).  With `A = a + log X + 3`, if `t ≤ 1/(1000 A²)`
  then `‖H_t(z) − Ξ(z)‖ < ‖Ξ(z)‖`
  (`norm_integral_gaussDensity_mul_sub_le` with `λ = 1/(32t)`).
-/

open Complex Metric Filter Set MeasureTheory

namespace RHTower.DeBruijn

noncomputable section

/-! ## Ratio bounds -/

/-- The polynomial factor gains at most `exp(Σ m_ρ ‖s₂ − s₁‖/‖s₁ − ρ‖)`. -/
theorem norm_prod_sub_pow_le {Z : Finset ℂ} {m : ℂ → ℕ} {s₁ s₂ : ℂ} (hZ : ∀ ρ ∈ Z, s₁ ≠ ρ) :
    ‖∏ ρ ∈ Z, (s₂ - ρ) ^ m ρ‖
      ≤ ‖∏ ρ ∈ Z, (s₁ - ρ) ^ m ρ‖
        * Real.exp ((∑ ρ ∈ Z, (m ρ : ℝ) / ‖s₁ - ρ‖) * ‖s₂ - s₁‖) := by
  rw [norm_prod, norm_prod, Finset.sum_mul, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun ρ _ => norm_nonneg _) fun ρ hρ => ?_
  have hd : 0 < ‖s₁ - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hZ ρ hρ))
  rw [norm_pow, norm_pow]
  have hbase : ‖s₂ - ρ‖ ≤ ‖s₁ - ρ‖ * Real.exp (‖s₂ - s₁‖ / ‖s₁ - ρ‖) := by
    have h1 : ‖s₂ - ρ‖ ≤ ‖s₁ - ρ‖ + ‖s₂ - s₁‖ := by
      calc ‖s₂ - ρ‖ = ‖(s₁ - ρ) + (s₂ - s₁)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h2 := Real.add_one_le_exp (‖s₂ - s₁‖ / ‖s₁ - ρ‖)
    calc ‖s₂ - ρ‖ ≤ ‖s₁ - ρ‖ * (‖s₂ - s₁‖ / ‖s₁ - ρ‖ + 1) := by
          rw [mul_add, mul_div_cancel₀ _ hd.ne', mul_one]; linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hd.le
  calc ‖s₂ - ρ‖ ^ m ρ ≤ (‖s₁ - ρ‖ * Real.exp (‖s₂ - s₁‖ / ‖s₁ - ρ‖)) ^ m ρ :=
        pow_le_pow_left₀ (norm_nonneg _) hbase _
    _ = ‖s₁ - ρ‖ ^ m ρ * Real.exp ((m ρ : ℝ) / ‖s₁ - ρ‖ * ‖s₂ - s₁‖) := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring

/-- A zero-free factor with `‖g′/g‖ ≤ K` on a convex open set gains at most `e^{K‖s₂ − s₁‖}`. -/
theorem norm_le_mul_exp_of_logDeriv_le {g : ℂ → ℂ} {U : Set ℂ} (hU : Convex ℝ U)
    (hg : AnalyticOnNhd ℂ g U) (hg0 : ∀ z ∈ U, g z ≠ 0) {K : ℝ}
    (hK : ∀ s ∈ U, ‖deriv g s / g s‖ ≤ K) {s₁ s₂ : ℂ} (h₁ : s₁ ∈ U) (h₂ : s₂ ∈ U) :
    ‖g s₂‖ ≤ ‖g s₁‖ * Real.exp (K * ‖s₂ - s₁‖) := by
  set γ : ℝ → ℂ := fun x => s₁ + (x : ℂ) * (s₂ - s₁) with hγ
  have hγU : ∀ x ∈ Icc (0 : ℝ) 1, γ x ∈ U := by
    intro x hx
    have := hU.add_smul_sub_mem h₁ h₂ hx
    simpa [hγ, Complex.real_smul] using this
  have hγd : ∀ x : ℝ, HasDerivAt γ (s₂ - s₁) x := by
    intro x
    have := ((hasDerivAt_id x).ofReal_comp.mul_const (s₂ - s₁)).const_add s₁
    simpa [hγ] using this
  have hF : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt (fun x => g (γ x)) (deriv g (γ x) * (s₂ - s₁)) x :=
    fun x hx => ((hg _ (hγU x hx)).differentiableAt.hasDerivAt).comp x (hγd x)
  have hbound : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖deriv g (γ x) * (s₂ - s₁)‖ ≤ (K * ‖s₂ - s₁‖) * ‖g (γ x)‖ := by
    intro x hx
    have hne := hg0 _ (hγU x hx)
    have h := hK _ (hγU x hx)
    rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hne)] at h
    rw [norm_mul]
    nlinarith [norm_nonneg (s₂ - s₁)]
  have h := GaloisForLFunctions.HTGeometry.norm_le_mul_exp_of_norm_deriv_le_Icc zero_le_one hF
    hbound
  simpa [hγ] using h

/-- **Ratio bound near an ordinate.** -/
theorem norm_xi_le_mul_exp_of_cofactor {c : ℂ} {R : ℝ} {Z : Finset ℂ} {m : ℂ → ℕ} {g : ℂ → ℂ}
    {K : ℝ} (hg : AnalyticOnNhd ℂ g (ball c R)) (hg0 : ∀ z ∈ ball c R, g z ≠ 0)
    (heq : EqOn xi (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z) (ball c R))
    (hK : ∀ s ∈ ball c R, ‖deriv g s / g s‖ ≤ K) {s₁ s₂ : ℂ} (h₁ : s₁ ∈ ball c R)
    (h₂ : s₂ ∈ ball c R) (hZ : ∀ ρ ∈ Z, s₁ ≠ ρ) :
    ‖xi s₂‖ ≤ ‖xi s₁‖ * Real.exp ((∑ ρ ∈ Z, (m ρ : ℝ) / ‖s₁ - ρ‖ + K) * ‖s₂ - s₁‖) := by
  rw [heq h₁, heq h₂, norm_mul, norm_mul]
  have hP := norm_prod_sub_pow_le (m := m) (s₂ := s₂) hZ
  have hG := norm_le_mul_exp_of_logDeriv_le (convex_ball c R) hg hg0 hK h₁ h₂
  calc ‖∏ ρ ∈ Z, (s₂ - ρ) ^ m ρ‖ * ‖g s₂‖
      ≤ (‖∏ ρ ∈ Z, (s₁ - ρ) ^ m ρ‖
          * Real.exp ((∑ ρ ∈ Z, (m ρ : ℝ) / ‖s₁ - ρ‖) * ‖s₂ - s₁‖))
        * (‖g s₁‖ * Real.exp (K * ‖s₂ - s₁‖)) :=
        mul_le_mul hP hG (norm_nonneg _) (by positivity)
    _ = _ := by rw [add_mul, Real.exp_add]; ring

/-! ## Transfer to `Ξ` -/

theorem norm_half_add_I_mul_sub (w z : ℂ) :
    ‖(1 / 2 + I * w) - (1 / 2 + I * z)‖ = ‖w - z‖ := by
  rw [show (1 / 2 + I * w) - (1 / 2 + I * z) = I * (w - z) by ring, norm_mul, Complex.norm_I,
    one_mul]

theorem XiC_eq_xi (w : ℂ) : XiC w = xi (1 / 2 + I * w) := by
  simp only [XiC]; ring_nf

/-- `Ξ` is tame at `z` with rate `a = Σ m_ρ/‖σ(z) − ρ‖ + K` on `B(z, 2)` when `σ(z) ∈ B(c, 9)`. -/
theorem XiC_tame_of_cofactor {c : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {g : ℂ → ℂ} {K : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball c 11)) (hg0 : ∀ z ∈ ball c 11, g z ≠ 0)
    (heq : EqOn xi (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z) (ball c 11))
    (hK : ∀ s ∈ ball c 11, ‖deriv g s / g s‖ ≤ K) {z : ℂ} (hz : 1 / 2 + I * z ∈ ball c 9)
    (hZ : ∀ ρ ∈ Z, 1 / 2 + I * z ≠ ρ) :
    ∀ w ∈ closedBall z 2, ‖XiC w‖ ≤ ‖XiC z‖
      * Real.exp ((∑ ρ ∈ Z, (m ρ : ℝ) / ‖(1 / 2 + I * z) - ρ‖ + K) * ‖w - z‖) := by
  intro w hw
  have hwz : ‖w - z‖ ≤ 2 := by simpa [dist_eq_norm] using hw
  have hzc : ‖(1 / 2 + I * z) - c‖ < 9 := by simpa [dist_eq_norm] using hz
  have hw11 : 1 / 2 + I * w ∈ ball c 11 := by
    rw [mem_ball, dist_eq_norm]
    calc ‖(1 / 2 + I * w) - c‖ ≤ ‖(1 / 2 + I * w) - (1 / 2 + I * z)‖ + ‖(1 / 2 + I * z) - c‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < 11 := by rw [norm_half_add_I_mul_sub]; linarith
  have h := norm_xi_le_mul_exp_of_cofactor hg hg0 heq hK
    (ball_subset_ball (by norm_num) hz) hw11 hZ
  rw [norm_half_add_I_mul_sub] at h
  rwa [XiC_eq_xi, XiC_eq_xi]

theorem half_add_I_mul_sub_I_mul (z : ℂ) (u : ℝ) :
    1 / 2 + I * (z - I * u) = (1 / 2 + I * z) + u := by
  ring_nf; rw [I_sq]; ring

theorem xiLine_eq_xi_add (s : ℂ) (u : ℝ) :
    xiLine s.im (s.re - 1 / 2 + u) = xi (s + u) := by
  rw [xiLine]
  congr 1
  apply Complex.ext <;> simp

theorem norm_xiLine_neg (X w : ℝ) : ‖xiLine X (-w)‖ = ‖xiLine X w‖ := by
  rw [xiLine, xiLine, xi_half_sub_eq_conj, Complex.norm_conj]

/-- The far growth of `ξ` along a horizontal line, for `|w| ≥ 9/2`. -/
theorem norm_xiLine_le_far_abs {X w t : ℝ} (hX : 200 ≤ X) (ht : 0 < t) (ht1 : t ≤ 1)
    (hw : 9 / 2 ≤ |w|) {U : ℝ} (hU : 9 / 2 ≤ U) (hwU : |w| ≤ U + 4) :
    ‖xiLine X w‖ ≤ ‖xiLine X (9 / 2)‖
      * Real.exp ((Real.log X + 2) * U + U ^ 2 / (8 * t)) := by
  have hfar : ‖xiLine X |w|‖ ≤ ‖xiLine X (9 / 2)‖ * Real.exp ((Real.log (X / (2 * Real.pi)) / 2
      + 2 + (|w| + 1 / 2) / (2 * X)) * (|w| - 9 / 2)) := norm_xiLine_le_far hX le_rfl hw
  have hnorm : ‖xiLine X w‖ = ‖xiLine X |w|‖ := by
    rcases le_total 0 w with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, norm_xiLine_neg]
  rw [hnorm]
  refine hfar.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _))
  have hX0 : 0 < X := by linarith
  have hlog : Real.log (X / (2 * Real.pi)) / 2 ≤ Real.log X := by
    have h1 : Real.log (X / (2 * Real.pi)) ≤ Real.log X :=
      Real.log_le_log (by positivity) (div_le_self hX0.le (by nlinarith [Real.pi_gt_three]))
    have h2 : 0 ≤ Real.log (X / (2 * Real.pi)) :=
      Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four])
    linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hd : 0 ≤ |w| - 9 / 2 := by linarith
  have hdU : |w| - 9 / 2 ≤ U := by linarith
  have hfrac : (|w| + 1 / 2) / (2 * X) * (|w| - 9 / 2) ≤ U ^ 2 / (8 * t) := by
    have hnum : (|w| + 1 / 2) * (|w| - 9 / 2) ≤ 2 * U ^ 2 := by nlinarith
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hnum (by positivity : (0 : ℝ) ≤ 8 * t)]
  have hcoef : 0 ≤ Real.log (X / (2 * Real.pi)) / 2 + 2 := by
    have := Real.log_nonneg (show (1 : ℝ) ≤ X / (2 * Real.pi) by
      rw [le_div_iff₀ (by positivity)]; nlinarith [Real.pi_lt_four])
    linarith
  calc (Real.log (X / (2 * Real.pi)) / 2 + 2 + (|w| + 1 / 2) / (2 * X)) * (|w| - 9 / 2)
      = (Real.log (X / (2 * Real.pi)) / 2 + 2) * (|w| - 9 / 2)
        + (|w| + 1 / 2) / (2 * X) * (|w| - 9 / 2) := by ring
    _ ≤ (Real.log X + 2) * U + U ^ 2 / (8 * t) := by
        have := mul_le_mul hdU (le_refl _) hd (by linarith : (0:ℝ) ≤ U)
        nlinarith [mul_le_mul_of_nonneg_right (by linarith : Real.log (X / (2 * Real.pi)) / 2 + 2
          ≤ Real.log X + 2) hd, mul_le_mul_of_nonneg_left hdU (by linarith : (0:ℝ) ≤ Real.log X + 2)]

end

end RHTower.DeBruijn
