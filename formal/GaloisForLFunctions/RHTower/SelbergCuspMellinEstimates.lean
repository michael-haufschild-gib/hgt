import GaloisForLFunctions.RHTower.SelbergCuspMellinResidues
import GaloisForLFunctions.HTGeometry.GammaHalfIntegerLineBound

/-!
# Estimates for the cusp Mellin–Barnes integrand on the imaginary axis

For `y > 0` let `g(u) = (2πy)^{-u} Γ(u) F(s + u/d)`.

* On a line `Re u = c > 0` to the right of the abscissa (`Re s + c/d > 1`) the integrand is
  integrable: `F` is bounded there and `Γ` is integrable on the line
  (`ExtendedSelbergClass.integrable_cuspMellinIntegrand_right`).
* On horizontal segments `[a, c] ± iT` the integrand is `O(T^N e^{-πT/2})`: `Γ` decays on
  vertical strips and `F` grows at most polynomially there, so the horizontal integrals vanish
  as `T → ∞` (`ExtendedSelbergClass.tendsto_hIntegral_cuspMellinIntegrand`).
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.SelbergClass

namespace RHTower

noncomputable section

/-- A class member is bounded to the right of any abscissa beyond `1`. -/
theorem ExtendedSelbergClass.exists_bound_re_ge (F : ExtendedSelbergClass) {σ : ℝ} (hσ : 1 < σ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, σ ≤ w.re → ‖F w‖ ≤ M := by
  have hsumm : Summable (fun n : ℕ =>
      ‖LSeries.term (fun n => (F.coeff n : ℂ)) (σ : ℂ) n‖) :=
    (F.lSeriesSummable (σ : ℂ) (by simpa using hσ)).norm
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun n => (F.coeff n : ℂ)) (σ : ℂ) n‖,
    tsum_nonneg fun n => norm_nonneg _, fun w hw => ?_⟩
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term (fun n => (F.coeff n : ℂ)) w n‖) :=
    hsumm.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => norm_term_le_of_re_le hw n)
  have hval := F.lSeries_eq_value w (by linarith)
  change ‖F.continuation.value w‖ ≤ _
  rw [← hval]
  calc ‖LSeries (fun n => (F.coeff n : ℂ)) w‖
      ≤ ∑' n : ℕ, ‖LSeries.term (fun n => (F.coeff n : ℂ)) w n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n => (F.coeff n : ℂ)) (σ : ℂ) n‖ :=
        hnorm.tsum_le_tsum (fun n => norm_term_le_of_re_le hw n) hsumm

theorem norm_twoPiY_cpow_neg {y : ℝ} (hy : 0 < y) (u : ℂ) :
    ‖(((2 * Real.pi * y : ℝ)) : ℂ) ^ (-u)‖ = (2 * Real.pi * y) ^ (-u.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]

theorem re_add_div_degree (s u : ℂ) (d : ℝ) : (s + u / (d : ℂ)).re = s.re + u.re / d := by
  rw [Complex.add_re, Complex.div_ofReal_re]

theorem im_add_div_degree (s u : ℂ) (d : ℝ) : (s + u / (d : ℂ)).im = s.im + u.im / d := by
  rw [Complex.add_im, Complex.div_ofReal_im]

/-- **Integrability on a line to the right.** -/
theorem ExtendedSelbergClass.integrable_cuspMellinIntegrand_right (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s : ℂ) {y c : ℝ} (hy : 0 < y) (hc : 0 < c)
    (hσ : 1 < s.re + c / F.gammaData.degree) :
    Integrable (fun t : ℝ =>
      F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ) ((c : ℂ) + (t : ℂ) * I)) := by
  obtain ⟨M, hM, hMb⟩ := F.exists_bound_re_ge hσ
  set x : ℂ := (((2 * Real.pi * y : ℝ)) : ℂ) with hx
  have hx0 : x ≠ 0 := by rw [hx]; exact_mod_cast (by positivity : (0 : ℝ) < 2 * Real.pi * y).ne'
  have hre : ∀ t : ℝ, (s + ((c : ℂ) + (t : ℂ) * I) / (F.gammaData.degree : ℂ)).re =
      s.re + c / F.gammaData.degree := by
    intro t; rw [re_add_div_degree]; simp
  have hcont : Continuous (fun t : ℝ => F.cuspMellinIntegrand s x ((c : ℂ) + (t : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hne : ((c : ℂ) + (t : ℂ) * I) ≠ F.cuspPole s := by
      intro h
      have h1 := (F.add_div_eq_one_iff hd s _).2 h
      have h2 := congrArg Complex.re h1
      rw [hre t, Complex.one_re] at h2
      linarith
    have hΓ : ∀ k : ℕ, ((c : ℂ) + (t : ℂ) * I) ≠ -(k : ℂ) := by
      intro k h
      have := congrArg Complex.re h
      simp at this
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have han := F.analyticAt_cuspMellinIntegrand hd s hx0 hΓ hne
    exact ContinuousAt.comp (g := F.cuspMellinIntegrand s x)
      (f := fun t : ℝ => (c : ℂ) + (t : ℂ) * I) (x := t) han.continuousAt (by fun_prop)
  have hΓint : Integrable (fun t : ℝ => ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖) :=
    (gamma_verticalIntegrable_of_pos hc).norm
  refine Integrable.mono' (hΓint.const_mul ((2 * Real.pi * y) ^ (-c) * M))
    hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  rw [ExtendedSelbergClass.cuspMellinIntegrand, norm_mul, norm_mul, hx, norm_twoPiY_cpow_neg hy]
  have hFb := hMb _ (le_of_eq (hre t).symm)
  have hre' : ((c : ℂ) + (t : ℂ) * I).re = c := by simp
  rw [hre']
  calc (2 * Real.pi * y) ^ (-c) * (‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ *
        ‖F (s + ((c : ℂ) + (t : ℂ) * I) / (F.gammaData.degree : ℂ))‖)
      ≤ (2 * Real.pi * y) ^ (-c) * (‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ * M) := by
        gcongr
    _ = (2 * Real.pi * y) ^ (-c) * M * ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * I)‖ := by ring

/-- **Uniform decay on horizontal segments.** -/
theorem ExtendedSelbergClass.exists_bound_cuspMellinIntegrand_horizontal (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s : ℂ) {y : ℝ} (hy : 0 < y) (a c : ℝ) :
    ∃ (C T₀ : ℝ) (N : ℕ), 0 ≤ C ∧ 1 ≤ T₀ ∧ ∀ x T : ℝ, a ≤ x → x ≤ c → T₀ ≤ |T| →
      ‖F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ) ((x : ℂ) + (T : ℂ) * I)‖ ≤
        C * |T| ^ N * Real.exp (-(Real.pi * |T| / 2)) := by
  set d := F.gammaData.degree with hddef
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := exists_sharp_bound_norm_Gamma_strip a c
  obtain ⟨CF, NF, hCF, hF⟩ := F.exists_polynomial_bound_strip (s.re + a / d) (s.re + c / d)
  set K : ℝ := (2 * Real.pi * y) ^ (-a) + (2 * Real.pi * y) ^ (-c) with hK
  set D : ℝ := |s.im| + 1 / d with hD
  have hDpos : 0 < D := by positivity
  set T₀ : ℝ := max 1 (d * (|s.im| + 1)) with hT₀
  refine ⟨K * CΓ * CF * D ^ NF, T₀, NΓ + NF, by positivity, le_max_left _ _,
    fun x T hxa hxc hT => ?_⟩
  have hT1 : 1 ≤ |T| := le_trans (le_max_left _ _) hT
  have hTd : d * (|s.im| + 1) ≤ |T| := le_trans (le_max_right _ _) hT
  set w : ℂ := s + ((x : ℂ) + (T : ℂ) * I) / (d : ℂ) with hw
  have hwre : w.re = s.re + x / d := by rw [hw, re_add_div_degree]; simp
  have hwim : w.im = s.im + T / d := by rw [hw, im_add_div_degree]; simp
  have hwim_low : 1 ≤ |w.im| := by
    rw [hwim]
    have h1 : |T| / d ≥ |s.im| + 1 := by rw [ge_iff_le, le_div_iff₀ hd]; linarith
    have h2 : |T / d| = |T| / d := by rw [abs_div, abs_of_pos hd]
    have h3 : |T / d| - |s.im| ≤ |s.im + T / d| := by
      have h5 := abs_sub_abs_le_abs_sub (T / d) (-s.im)
      rw [sub_neg_eq_add, abs_neg, add_comm] at h5
      exact h5
    linarith
  have hwim_up : |w.im| ≤ D * |T| := by
    rw [hwim]
    calc |s.im + T / d| ≤ |s.im| + |T / d| := abs_add_le _ _
      _ = |s.im| + |T| / d := by rw [abs_div, abs_of_pos hd]
      _ ≤ |s.im| * |T| + |T| / d := by nlinarith [abs_nonneg s.im]
      _ = D * |T| := by rw [hD]; ring
  have hFw : ‖F w‖ ≤ CF * |w.im| ^ NF := by
    refine hF w ?_ ?_ hwim_low
    · rw [hwre]; have := div_le_div_of_nonneg_right hxa hd.le; linarith
    · rw [hwre]; have := div_le_div_of_nonneg_right hxc hd.le; linarith
  have hΓb := hΓ ((x : ℂ) + (T : ℂ) * I) (by simp [hxa]) (by simp [hxc]) (by simpa using hT1)
  have him : ((x : ℂ) + (T : ℂ) * I).im = T := by simp
  rw [him] at hΓb
  have hpow : (2 * Real.pi * y) ^ (-x) ≤ K := by
    have hb : 0 < 2 * Real.pi * y := by positivity
    rcases le_total (2 * Real.pi * y) 1 with hb1 | hb1
    · have : (2 * Real.pi * y) ^ (-x) ≤ (2 * Real.pi * y) ^ (-c) :=
        Real.rpow_le_rpow_of_exponent_ge hb hb1 (by linarith)
      have := Real.rpow_nonneg hb.le (-a)
      linarith
    · have : (2 * Real.pi * y) ^ (-x) ≤ (2 * Real.pi * y) ^ (-a) :=
        Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
      have := Real.rpow_nonneg hb.le (-c)
      linarith
  rw [ExtendedSelbergClass.cuspMellinIntegrand, norm_mul, norm_mul, norm_twoPiY_cpow_neg hy]
  have hre' : ((x : ℂ) + (T : ℂ) * I).re = x := by simp
  rw [hre']
  have hwpow : |w.im| ^ NF ≤ D ^ NF * |T| ^ NF := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hwim_up _
  calc (2 * Real.pi * y) ^ (-x) * (‖Complex.Gamma ((x : ℂ) + (T : ℂ) * I)‖ * ‖F w‖)
      ≤ K * ((CΓ * |T| ^ NΓ * Real.exp (-(Real.pi * |T| / 2))) * (CF * (D ^ NF * |T| ^ NF))) := by
        gcongr
        · exact hFw.trans (mul_le_mul_of_nonneg_left hwpow hCF)
    _ = K * CΓ * CF * D ^ NF * |T| ^ (NΓ + NF) * Real.exp (-(Real.pi * |T| / 2)) := by
        rw [pow_add]; ring

theorem tendsto_pow_mul_exp_neg_pi_half (N : ℕ) (C : ℝ) :
    Tendsto (fun T : ℝ => C * T ^ N * Real.exp (-(Real.pi * T / 2))) atTop (𝓝 0) := by
  have hc : 0 < Real.pi / 2 := by positivity
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero N).comp
    (tendsto_id.const_mul_atTop hc)
  have h2 := h.const_mul (C * (Real.pi / 2)⁻¹ ^ N)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards with T
  simp only [Function.comp, id]
  rw [mul_pow, show -(Real.pi / 2 * T) = -(Real.pi * T / 2) by ring]
  have hone : ((Real.pi / 2)⁻¹) ^ N * (Real.pi / 2) ^ N = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ (by positivity), one_pow]
  calc C * (Real.pi / 2)⁻¹ ^ N * ((Real.pi / 2) ^ N * T ^ N * Real.exp (-(Real.pi * T / 2)))
      = C * ((Real.pi / 2)⁻¹ ^ N * (Real.pi / 2) ^ N) * T ^ N *
          Real.exp (-(Real.pi * T / 2)) := by ring
    _ = C * T ^ N * Real.exp (-(Real.pi * T / 2)) := by rw [hone, mul_one]

/-- **The horizontal integrals vanish.** -/
theorem ExtendedSelbergClass.tendsto_hIntegral_cuspMellinIntegrand (F : ExtendedSelbergClass)
    (hd : 0 < F.gammaData.degree) (s : ℂ) {y : ℝ} (hy : 0 < y) {a c : ℝ} (hac : a ≤ c) :
    Tendsto (fun T : ℝ => HIntegral (F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ))
        a c T) atTop (𝓝 0) ∧
      Tendsto (fun T : ℝ => HIntegral (F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ))
        a c (-T)) atTop (𝓝 0) := by
  obtain ⟨C, T₀, N, hC, hT₀, hb⟩ := F.exists_bound_cuspMellinIntegrand_horizontal hd s hy a c
  have hlim := tendsto_pow_mul_exp_neg_pi_half N (C * (c - a))
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → Tendsto (fun T : ℝ =>
      HIntegral (F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ)) a c (σ * T))
      atTop (𝓝 0) := by
    intro σ hσ
    have habs : ∀ T : ℝ, |σ * T| = |T| := by
      intro T; rcases hσ with rfl | rfl <;> simp
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hTabs : T₀ ≤ |σ * T| := by rw [habs, abs_of_nonneg (by linarith)]; exact hT
    rw [HIntegral]
    have hbound : ∀ x ∈ Set.uIoc a c, ‖F.cuspMellinIntegrand s (((2 * Real.pi * y : ℝ)) : ℂ)
        ((x : ℂ) + ((σ * T : ℝ) : ℂ) * I)‖ ≤
          C * |σ * T| ^ N * Real.exp (-(Real.pi * |σ * T| / 2)) := by
      intro x hx
      rw [Set.uIoc_of_le hac] at hx
      exact hb x (σ * T) hx.1.le hx.2 hTabs
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [habs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T), abs_of_nonneg (by linarith : 0 ≤ c - a)]
      at h
    calc _ ≤ C * T ^ N * Real.exp (-(Real.pi * T / 2)) * (c - a) := h
      _ = C * (c - a) * T ^ N * Real.exp (-(Real.pi * T / 2)) := by ring
  refine ⟨(key 1 (Or.inl rfl)).congr fun T => by simp, (key (-1) (Or.inr rfl)).congr fun T => ?_⟩
  simp

end

end RHTower
