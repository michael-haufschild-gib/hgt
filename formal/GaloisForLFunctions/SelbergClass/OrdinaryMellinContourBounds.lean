import GaloisForLFunctions.SelbergClass.OrdinaryMellinLeftDecay

/-!
# The fixed right line and horizontal sides of the ordinary Mellin contour

Absolute Dirichlet convergence bounds the line at two. Polynomial strip growth
and the Mellin Gamma factor make both horizontal sides vanish.
-/

noncomputable section
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

theorem integrable_ordinaryMellinIntegrand_right (F : ExtendedSelbergClass)
    {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => ordinaryMellinIntegrand F 0 (x : ℂ) (2 + (t : ℂ) * I)) := by
  obtain ⟨M, hM, hMb⟩ := F.exists_bound_re_ge (σ := 2) (by norm_num)
  have hcont : Continuous (fun t : ℝ => ordinaryMellinIntegrand F 0 (x : ℂ) (2 + (t : ℂ) * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hΓ : ∀ k : ℕ, (2 : ℂ) + (t : ℂ) * I ≠ -(k : ℂ) := by
      intro k h
      have he := congrArg Complex.re h
      simp at he
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    have hne : (0 : ℂ) + (2 + (t : ℂ) * I) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      norm_num at this
    exact ContinuousAt.comp (g := ordinaryMellinIntegrand F 0 (x : ℂ))
      (f := fun t : ℝ => 2 + (t : ℂ) * I) (x := t)
      (analyticAt_ordinaryMellinIntegrand F 0 (Complex.ofReal_ne_zero.mpr hx.ne')
        hΓ hne).continuousAt (by fun_prop)
  have hΓint := (gamma_verticalIntegrable_of_pos (c := 2) (by norm_num)).norm
  apply Integrable.mono' (hΓint.const_mul (x ^ (-2 : ℝ) * M)) hcont.aestronglyMeasurable
  filter_upwards with t
  simp only [ordinaryMellinIntegrand, zero_add, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
  have hre : (2 + (t : ℂ) * I).re = 2 := by simp
  rw [hre]
  calc _ ≤ x ^ (-2 : ℝ) * (‖Complex.Gamma (2 + (t : ℂ) * I)‖ * M) := by
          gcongr
          exact hMb _ hre.ge
    _ = _ := by
      push_cast
      ring

private theorem exists_bound_ordinaryMellinIntegrand_horizontal
    (F : ExtendedSelbergClass) {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ v T : ℝ, a ≤ v → v ≤ b → 1 ≤ |T| →
      ‖ordinaryMellinIntegrand F 0 (x : ℂ) ((v : ℂ) + (T : ℂ) * I)‖ ≤
        C * |T| ^ N * Real.exp (-(Real.pi * |T| / 2)) := by
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := exists_sharp_bound_norm_Gamma_strip a b
  obtain ⟨CF, NF, hCF, hF⟩ := F.exists_polynomial_bound_strip a b
  set K : ℝ := x ^ (-a) + x ^ (-b) with hK
  refine ⟨K * CΓ * CF, NΓ + NF, by positivity, fun v T hva hvb hT => ?_⟩
  have hpow : x ^ (-v) ≤ K := by
    rcases le_total x 1 with hx1 | hx1
    · have := Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith : -b ≤ -v)
      have := Real.rpow_nonneg hx.le (-a)
      dsimp only [K]
      linarith
    · have := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : -v ≤ -a)
      have := Real.rpow_nonneg hx.le (-b)
      dsimp only [K]
      linarith
  have hΓb := hΓ ((v : ℂ) + (T : ℂ) * I) (by simpa using hva)
    (by simpa using hvb) (by simpa using hT)
  have hFb := hF ((v : ℂ) + (T : ℂ) * I) (by simpa using hva)
    (by simpa using hvb) (by simpa using hT)
  have him : ((v : ℂ) + (T : ℂ) * I).im = T := by simp
  rw [him] at hΓb hFb
  simp only [ordinaryMellinIntegrand, zero_add, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
  have hre : ((v : ℂ) + (T : ℂ) * I).re = v := by simp
  rw [hre]
  calc _ ≤ K * ((CΓ * |T| ^ NΓ * Real.exp (-(Real.pi * |T| / 2))) * (CF * |T| ^ NF)) := by
          gcongr
    _ = _ := by rw [pow_add]; ring

/-- Both horizontal sides vanish at unbounded heights. -/
theorem tendsto_hIntegral_ordinaryMellinIntegrand (F : ExtendedSelbergClass)
    {x : ℝ} (hx : 0 < x) {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun T : ℝ => HIntegral (ordinaryMellinIntegrand F 0 (x : ℂ)) a b T) atTop (𝓝 0) ∧
    Tendsto (fun T : ℝ => HIntegral (ordinaryMellinIntegrand F 0 (x : ℂ)) a b (-T)) atTop (𝓝 0) := by
  obtain ⟨C, N, hC, hb⟩ := exists_bound_ordinaryMellinIntegrand_horizontal F hx a b
  have hlim := tendsto_pow_mul_exp_neg_pi_half N (C * (b - a))
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → Tendsto (fun T : ℝ =>
      HIntegral (ordinaryMellinIntegrand F 0 (x : ℂ)) a b (σ * T)) atTop (𝓝 0) := by
    intro σ hσ
    have habs : ∀ T : ℝ, |σ * T| = |T| := by
      intro T
      rcases hσ with rfl | rfl <;> simp
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    have hTabs : 1 ≤ |σ * T| := by rw [habs, abs_of_nonneg (by linarith)]; exact hT
    rw [HIntegral]
    have hbound : ∀ v ∈ Set.uIoc a b,
        ‖ordinaryMellinIntegrand F 0 (x : ℂ) ((v : ℂ) + ((σ * T : ℝ) : ℂ) * I)‖ ≤
          C * |σ * T| ^ N * Real.exp (-(Real.pi * |σ * T| / 2)) := by
      intro v hv
      rw [Set.uIoc_of_le hab] at hv
      exact hb v (σ * T) hv.1.le hv.2 hTabs
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [habs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ T), abs_of_nonneg (sub_nonneg.mpr hab)] at h
    exact h.trans_eq (by ring)
  exact ⟨(key 1 (Or.inl rfl)).congr fun T => by simp,
    (key (-1) (Or.inr rfl)).congr fun T => by simp⟩

end GaloisForLFunctions.SelbergClass
