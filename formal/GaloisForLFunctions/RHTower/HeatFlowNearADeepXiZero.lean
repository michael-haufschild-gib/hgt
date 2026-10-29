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
  apply Complex.ext
  · simp; ring
  · simp

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

/-- **The vertical tail of `Ξ`.**  For `σ(z) ∈ B(c, 5/2)`, `c = 2 + iT`, and `|u| > 1`,
`‖Ξ(z − iu)‖ ≤ e^{8a} ‖Ξ(z)‖ e^{(a + log X + 2)|u|} e^{u²/8t}` with `X = Im σ(z)`. -/
theorem norm_XiC_vertical_le {c : ℂ} {T : ℝ} (hc : c = 2 + (T : ℂ) * I) {Z : Finset ℂ}
    {m : ℂ → ℕ} {g : ℂ → ℂ} {K : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball c 11)) (hg0 : ∀ z ∈ ball c 11, g z ≠ 0)
    (heq : EqOn xi (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z) (ball c 11))
    (hK : ∀ s ∈ ball c 11, ‖deriv g s / g s‖ ≤ K) (hK0 : 0 ≤ K) {z : ℂ}
    (hz : 1 / 2 + I * z ∈ ball c (5 / 2)) (hZ : ∀ ρ ∈ Z, 1 / 2 + I * z ≠ ρ)
    (hX : 200 ≤ (1 / 2 + I * z).im) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (u : ℝ) (hu : 1 < |u|) :
    ‖XiC (z - I * u)‖ ≤
      Real.exp (8 * (∑ ρ ∈ Z, (m ρ : ℝ) / ‖(1 / 2 + I * z) - ρ‖ + K)) * ‖XiC z‖
        * Real.exp ((∑ ρ ∈ Z, (m ρ : ℝ) / ‖(1 / 2 + I * z) - ρ‖ + K
            + Real.log (1 / 2 + I * z).im + 2) * |u|) * Real.exp (u ^ 2 / (8 * t)) := by
  set sz : ℂ := 1 / 2 + I * z with hsz
  set a : ℝ := ∑ ρ ∈ Z, (m ρ : ℝ) / ‖sz - ρ‖ + K with ha
  set X : ℝ := sz.im with hXdef
  have ha0 : 0 ≤ a := by
    have : 0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / ‖sz - ρ‖ := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hszc : ‖sz - c‖ < 5 / 2 := by simpa [dist_eq_norm] using hz
  have hsz11 : sz ∈ ball c 11 := ball_subset_ball (by norm_num) hz
  have hratio : ∀ s ∈ ball c 11, ‖xi s‖ ≤ ‖xi sz‖ * Real.exp (a * ‖s - sz‖) := fun s hs =>
    norm_xi_le_mul_exp_of_cofactor hg hg0 heq hK hsz11 hs hZ
  have hXi : XiC (z - I * u) = xi (sz + u) := by rw [XiC_eq_xi, half_add_I_mul_sub_I_mul]
  have hXz : XiC z = xi sz := XiC_eq_xi z
  rw [hXi, hXz]
  have hE8 : 1 ≤ Real.exp (8 * a) := Real.one_le_exp (by positivity)
  have hEu : 1 ≤ Real.exp (u ^ 2 / (8 * t)) := Real.one_le_exp (by positivity)
  have hN := norm_nonneg (xi sz)
  rcases lt_or_ge (|u|) (17 / 2) with hsmall | hlarge
  · have hin : sz + u ∈ ball c 11 := by
      rw [mem_ball, dist_eq_norm]
      calc ‖sz + u - c‖ ≤ ‖sz - c‖ + ‖(u : ℂ)‖ := by
            rw [show sz + u - c = (sz - c) + u by ring]; exact norm_add_le _ _
        _ < 11 := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith
    have h := hratio _ hin
    rw [show sz + u - sz = (u : ℂ) by ring, Complex.norm_real, Real.norm_eq_abs] at h
    have hmono : Real.exp (a * |u|) ≤ Real.exp ((a + Real.log X + 2) * |u|) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg u])
    calc ‖xi (sz + u)‖ ≤ ‖xi sz‖ * Real.exp (a * |u|) := h
      _ ≤ Real.exp (8 * a) * ‖xi sz‖ * Real.exp ((a + Real.log X + 2) * |u|)
            * Real.exp (u ^ 2 / (8 * t)) := by
          have h1 : ‖xi sz‖ * Real.exp (a * |u|)
              ≤ ‖xi sz‖ * Real.exp ((a + Real.log X + 2) * |u|) :=
            mul_le_mul_of_nonneg_left hmono hN
          have hP : 0 ≤ ‖xi sz‖ * Real.exp ((a + Real.log X + 2) * |u|) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left hE8 hP,
            mul_le_mul_of_nonneg_left hEu (mul_nonneg (by positivity : (0:ℝ) ≤ Real.exp (8 * a)) hP)]
  · -- far: the horizontal-line growth beyond the window
    have hre : |sz.re - 1 / 2| < 4 := by
      have h := Complex.abs_re_le_norm (sz - c)
      have hre' : (sz - c).re = sz.re - 2 := by rw [hc]; simp
      rw [hre'] at h
      have h2 := abs_lt.mp (lt_of_le_of_lt h hszc)
      rw [abs_lt]
      constructor <;> linarith [h2.1, h2.2]
    set w : ℝ := sz.re - 1 / 2 + u with hw
    have hwabs1 : 9 / 2 ≤ |w| := by
      have h1 : u = w + -(sz.re - 1 / 2) := by rw [hw]; ring
      have h2 : |u| ≤ |w| + |-(sz.re - 1 / 2)| := by
        conv_lhs => rw [h1]
        exact abs_add_le _ _
      rw [abs_neg] at h2
      linarith
    have hwabs2 : |w| ≤ |u| + 4 := by
      have := abs_add_le (sz.re - 1 / 2) u
      rw [← hw] at this
      linarith
    have hfar := norm_xiLine_le_far_abs (X := X) hX ht ht1 hwabs1 (by linarith) hwabs2
    rw [xiLine_eq_xi_add] at hfar
    have hanchor : xiLine X (9 / 2) = xi (5 + (X : ℂ) * I) := by
      rw [xiLine]; congr 1; push_cast; ring
    have hW11 : (5 : ℂ) + (X : ℂ) * I ∈ ball c 11 := by
      rw [mem_ball, dist_eq_norm, hc]
      have him : |X - T| < 5 / 2 := by
        have h := Complex.abs_im_le_norm (sz - c)
        have him' : (sz - c).im = X - T := by rw [hc, hXdef]; simp
        rw [him'] at h
        linarith
      calc ‖(5 : ℂ) + (X : ℂ) * I - (2 + (T : ℂ) * I)‖ = ‖(3 : ℂ) + ((X - T : ℝ) : ℂ) * I‖ := by
            congr 1; push_cast; ring
        _ ≤ ‖(3 : ℂ)‖ + ‖((X - T : ℝ) : ℂ) * I‖ := norm_add_le _ _
        _ < 11 := by
            rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
            norm_num; linarith
    have hWdist : ‖(5 + (X : ℂ) * I) - sz‖ ≤ 8 := by
      have h1 : ‖(5 + (X : ℂ) * I) - c‖ < 11 := by simpa [dist_eq_norm] using hW11
      have h2 : ‖(5 + (X : ℂ) * I) - c‖ ≤ 11 / 2 := by
        rw [hc]
        have him : |X - T| < 5 / 2 := by
          have h := Complex.abs_im_le_norm (sz - c)
          have him' : (sz - c).im = X - T := by rw [hc, hXdef]; simp
          rw [him'] at h
          linarith
        calc ‖(5 : ℂ) + (X : ℂ) * I - (2 + (T : ℂ) * I)‖
            = ‖(3 : ℂ) + ((X - T : ℝ) : ℂ) * I‖ := by congr 1; push_cast; ring
          _ ≤ ‖(3 : ℂ)‖ + ‖((X - T : ℝ) : ℂ) * I‖ := norm_add_le _ _
          _ ≤ 11 / 2 := by
              rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
              norm_num; linarith
      calc ‖(5 + (X : ℂ) * I) - sz‖ ≤ ‖(5 + (X : ℂ) * I) - c‖ + ‖c - sz‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 8 := by rw [norm_sub_rev c sz]; linarith
    have hWratio : ‖xi (5 + (X : ℂ) * I)‖ ≤ ‖xi sz‖ * Real.exp (8 * a) := by
      refine (hratio _ hW11).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hN)
      nlinarith
    have hsz_eq : sz + u = (sz.im : ℂ) * I + ((sz.re : ℂ) + u) := by
      apply Complex.ext <;> simp
    rw [hanchor] at hfar
    have hfar' : ‖xi (sz + u)‖ ≤ ‖xi (5 + (X : ℂ) * I)‖
        * Real.exp ((Real.log X + 2) * |u| + |u| ^ 2 / (8 * t)) := by
      have := hfar
      rwa [show sz + (u : ℂ) = sz + u from rfl] at this
    rw [sq_abs] at hfar'
    calc ‖xi (sz + u)‖ ≤ ‖xi sz‖ * Real.exp (8 * a)
          * Real.exp ((Real.log X + 2) * |u| + u ^ 2 / (8 * t)) :=
          hfar'.trans (mul_le_mul_of_nonneg_right hWratio (Real.exp_pos _).le)
      _ ≤ Real.exp (8 * a) * ‖xi sz‖ * Real.exp ((a + Real.log X + 2) * |u|)
            * Real.exp (u ^ 2 / (8 * t)) := by
          rw [Real.exp_add]
          have hmono : Real.exp ((Real.log X + 2) * |u|) ≤ Real.exp ((a + Real.log X + 2) * |u|) :=
            Real.exp_le_exp.mpr (by nlinarith [abs_nonneg u])
          have hP : 0 ≤ Real.exp (8 * a) * ‖xi sz‖ := by positivity
          calc ‖xi sz‖ * Real.exp (8 * a)
                * (Real.exp ((Real.log X + 2) * |u|) * Real.exp (u ^ 2 / (8 * t)))
              = (Real.exp (8 * a) * ‖xi sz‖) * Real.exp ((Real.log X + 2) * |u|)
                * Real.exp (u ^ 2 / (8 * t)) := by ring
            _ ≤ (Real.exp (8 * a) * ‖xi sz‖) * Real.exp ((a + Real.log X + 2) * |u|)
                * Real.exp (u ^ 2 / (8 * t)) := by gcongr

/-- The numerical inequality behind the comparison: for `A ≥ 1` and `t A² ≤ 1/1000`, the error
factor of `norm_integral_gaussDensity_mul_sub_le` with `λ = 1/(32t)` is at most `1/5`. -/
theorem heat_error_factor_le {A t : ℝ} (hA : 1 ≤ A) (ht : 0 < t) (htA : t * A ^ 2 ≤ 1 / 1000) :
    t * (42 * A ^ 2 * Real.exp (4 * A ^ 2 * t)
      + 20 * (Real.exp (8 * A) + 1 + 4 * A)
        * Real.exp (-(1 / (32 * t)) + 8 * (A + 1 / (32 * t)) ^ 2 * t)) ≤ 1 / 5 := by
  have hA2 : 1 ≤ A ^ 2 := by nlinarith
  have ht1 : t ≤ 1 / 1000 := by nlinarith
  have he1 : Real.exp (4 * A ^ 2 * t) ≤ 3 := by
    have h4 : 4 * A ^ 2 * t ≤ 1 := by nlinarith
    calc Real.exp (4 * A ^ 2 * t) ≤ Real.exp 1 := Real.exp_le_exp.mpr h4
      _ ≤ 3 := by have := Real.exp_one_lt_d9; linarith
  have hpart1 : t * (42 * A ^ 2 * Real.exp (4 * A ^ 2 * t)) ≤ 126 / 1000 := by
    have : t * (42 * A ^ 2 * Real.exp (4 * A ^ 2 * t)) = 42 * (t * A ^ 2) * Real.exp (4 * A ^ 2 * t) := by
      ring
    rw [this]
    have hnn : 0 ≤ t * A ^ 2 := by positivity
    calc 42 * (t * A ^ 2) * Real.exp (4 * A ^ 2 * t) ≤ 42 * (1 / 1000) * 3 := by gcongr
      _ = 126 / 1000 := by norm_num
  have hexpo : -(1 / (32 * t)) + 8 * (A + 1 / (32 * t)) ^ 2 * t
      = 8 * A ^ 2 * t + A / 2 - 3 / (128 * t) := by
    field_simp; ring
  have hinv : 1000 * A ^ 2 ≤ 1 / t := by
    rw [le_div_iff₀ ht]; nlinarith
  have h3 : 23 * A ^ 2 ≤ 3 / (128 * t) := by
    have : 3 / (128 * t) = 3 / 128 * (1 / t) := by field_simp
    rw [this]; nlinarith
  have hsum : 8 * A + (8 * A ^ 2 * t + A / 2 - 3 / (128 * t)) ≤ 0 := by nlinarith
  have hB : Real.exp (8 * A) + 1 + 4 * A ≤ 3 * Real.exp (8 * A) := by
    have h1 : 1 ≤ Real.exp (8 * A) := Real.one_le_exp (by linarith)
    have h2 : 8 * A + 1 ≤ Real.exp (8 * A) := Real.add_one_le_exp _
    linarith
  have hpart2 : t * (20 * (Real.exp (8 * A) + 1 + 4 * A)
      * Real.exp (-(1 / (32 * t)) + 8 * (A + 1 / (32 * t)) ^ 2 * t)) ≤ 60 / 1000 := by
    rw [hexpo]
    have hE : (Real.exp (8 * A) + 1 + 4 * A) * Real.exp (8 * A ^ 2 * t + A / 2 - 3 / (128 * t))
        ≤ 3 := by
      calc (Real.exp (8 * A) + 1 + 4 * A) * Real.exp (8 * A ^ 2 * t + A / 2 - 3 / (128 * t))
          ≤ 3 * Real.exp (8 * A) * Real.exp (8 * A ^ 2 * t + A / 2 - 3 / (128 * t)) := by
            gcongr
        _ = 3 * Real.exp (8 * A + (8 * A ^ 2 * t + A / 2 - 3 / (128 * t))) := by
            rw [Real.exp_add]; ring
        _ ≤ 3 * Real.exp 0 := by gcongr
        _ = 3 := by simp
    calc t * (20 * (Real.exp (8 * A) + 1 + 4 * A)
          * Real.exp (8 * A ^ 2 * t + A / 2 - 3 / (128 * t)))
        = 20 * t * ((Real.exp (8 * A) + 1 + 4 * A)
          * Real.exp (8 * A ^ 2 * t + A / 2 - 3 / (128 * t))) := by ring
      _ ≤ 20 * (1 / 1000) * 3 := by gcongr
      _ = 60 / 1000 := by norm_num
  rw [mul_add]
  linarith

/-- **The heat flow stays close to `Ξ`.**  With `a = Σ m_ρ/‖σ(z) − ρ‖ + K`, `X = Im σ(z)` and
`A = a + log X + 3`, if `t ≤ 1/(1000 A²)` then `‖H_t(z) − Ξ(z)‖ < ‖Ξ(z)‖`. -/
theorem norm_riemannHeat_sub_XiC_lt {c : ℂ} {T : ℝ} (hc : c = 2 + (T : ℂ) * I) {Z : Finset ℂ}
    {m : ℂ → ℕ} {g : ℂ → ℂ} {K : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball c 11)) (hg0 : ∀ z ∈ ball c 11, g z ≠ 0)
    (heq : EqOn xi (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * g z) (ball c 11))
    (hK : ∀ s ∈ ball c 11, ‖deriv g s / g s‖ ≤ K) (hK0 : 0 ≤ K)
    (hzero : ∀ s ∈ ball c 11, xi s = 0 → s ∈ Z) {z : ℂ}
    (hz : 1 / 2 + I * z ∈ ball c (5 / 2)) (hZ : ∀ ρ ∈ Z, 1 / 2 + I * z ≠ ρ)
    (hX : 200 ≤ (1 / 2 + I * z).im) {t : ℝ} (ht : 0 < t)
    (htA : t ≤ 1 / (1000 * (∑ ρ ∈ Z, (m ρ : ℝ) / ‖(1 / 2 + I * z) - ρ‖ + K
      + Real.log (1 / 2 + I * z).im + 3) ^ 2)) :
    ‖riemannHeat t z - XiC z‖ < ‖XiC z‖ := by
  set sz : ℂ := 1 / 2 + I * z with hsz
  set a : ℝ := ∑ ρ ∈ Z, (m ρ : ℝ) / ‖sz - ρ‖ + K with ha
  set X : ℝ := sz.im with hXdef
  set A : ℝ := a + Real.log X + 3 with hAdef
  have ha0 : 0 ≤ a := by
    have : 0 ≤ ∑ ρ ∈ Z, (m ρ : ℝ) / ‖sz - ρ‖ := Finset.sum_nonneg fun _ _ => by positivity
    linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  have hA1 : 1 ≤ A := by linarith
  have htA2 : t * A ^ 2 ≤ 1 / 1000 := by
    have hpos : 0 < 1000 * A ^ 2 := by positivity
    rw [le_div_iff₀ hpos] at htA
    linarith
  have ht1 : t ≤ 1 := by nlinarith
  have hsz11 : sz ∈ ball c 11 := ball_subset_ball (by norm_num) hz
  have hF0 : XiC z ≠ 0 := by
    rw [XiC_eq_xi]
    intro h0
    exact hZ sz (hzero sz hsz11 h0) rfl
  have hloc : ∀ w ∈ closedBall z 2, ‖XiC w‖ ≤ ‖XiC z‖ * Real.exp (A * ‖w - z‖) := by
    intro w hw
    refine (XiC_tame_of_cofactor hg hg0 heq hK (ball_subset_ball (by norm_num) hz) hZ w hw).trans ?_
    gcongr
    linarith
  have htail : ∀ u : ℝ, 1 < |u| → ‖XiC (z - I * u)‖
      ≤ Real.exp (8 * A) * ‖XiC z‖ * Real.exp (A * |u|) * Real.exp (u ^ 2 / (8 * t)) := by
    intro u hu
    refine (norm_XiC_vertical_le hc hg hg0 heq hK hK0 hz hZ hX ht ht1 u hu).trans ?_
    have h1 : Real.exp (8 * a) ≤ Real.exp (8 * A) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp ((a + Real.log X + 2) * |u|) ≤ Real.exp (A * |u|) :=
      Real.exp_le_exp.mpr (by nlinarith [abs_nonneg u])
    gcongr
  have hmain := norm_integral_gaussDensity_mul_sub_le (F := XiC) XiC_differentiable ht hA1
    (by linarith : (0 : ℝ) ≤ A) (Real.exp_pos (8 * A)).le (by positivity : (0 : ℝ) ≤ 1 / (32 * t))
    hloc htail (integrable_gaussDensity_mul_XiC ht z)
  rw [← riemannHeat_eq_integral_gaussian_XiC ht z] at hmain
  have hfac := heat_error_factor_le hA1 ht htA2
  have hN : 0 < ‖XiC z‖ := norm_pos_iff.mpr hF0
  calc ‖riemannHeat t z - XiC z‖
      ≤ t * ‖XiC z‖ * (42 * A ^ 2 * Real.exp (4 * A ^ 2 * t)
        + 20 * (Real.exp (8 * A) + 1 + 4 * A)
          * Real.exp (-(1 / (32 * t)) + 8 * (A + 1 / (32 * t)) ^ 2 * t)) := hmain
    _ = ‖XiC z‖ * (t * (42 * A ^ 2 * Real.exp (4 * A ^ 2 * t)
        + 20 * (Real.exp (8 * A) + 1 + 4 * A)
          * Real.exp (-(1 / (32 * t)) + 8 * (A + 1 / (32 * t)) ^ 2 * t))) := by ring
    _ ≤ ‖XiC z‖ * (1 / 5) := mul_le_mul_of_nonneg_left hfac hN.le
    _ < ‖XiC z‖ := by linarith

end

end RHTower.DeBruijn
