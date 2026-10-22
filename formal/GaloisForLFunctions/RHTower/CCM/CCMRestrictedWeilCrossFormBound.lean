import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMMixedPolarFactorization

/-!
# An `L¹` bound for the restricted Weil form between smooth sources

For smooth interior sources `u, v` at aperture `a`, the restricted Weil form is
`Q_a(u, v) = P_a(c) - W_∞(c)`. Here `c(h) = ∫ v(y + h) conj(u(y)) dy` is the cross-correlation,
`P_a` the polar-prime functional and `W_∞` the sharp archimedean distribution
(`ccmRestrictedWeilForm_ccmComplexSmooth_eq_polarPrimeFull_sub_archimedean`). Each term is
controlled by `N = ∫|u|` times a quantity attached to `v` alone:

* the pole lag integral `P₀ ≥ sup_y ∫_0^{2a} (|v(y+h)| + |v(y-h)|) 2cosh(h/2) dh`;
* the prime lag sum `S₀ ≥ sup_y Σ_k w_k (|v(y + log k)| + |v(y - log k)|)`;
* the archimedean part, through `A ≥ sup|v|` and `A' ≥ sup|v'|`. For every `δ ∈ (0,1]`,
  `|W_∞^♯(F)| ≤ A_F(8 + (3/2) log(1/δ)) + δ(A_F + A'_F)/2` for every test with `|F| ≤ A_F` that is
  `A'_F`-Lipschitz (`norm_ccmArchimedeanWeilSharpDistribution_le`). The evenized cross-correlation
  has `A_F = 2AN` and `A'_F = 2A'N`.

Main statement: `norm_ccmRestrictedWeilForm_smooth_le`.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The sharp archimedean distribution -/

theorem exp_half_sub_one_le {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) : Real.exp (h / 2) - 1 ≤ h := by
  have hb := Real.exp_bound_div_one_sub_of_interval (x := h / 2) (by linarith) (by linarith)
  have hpos : 0 < 1 - h / 2 := by linarith
  have : 1 / (1 - h / 2) ≤ 1 + h := by
    rw [div_le_iff₀ hpos]; nlinarith
  linarith

theorem two_mul_le_exp_sub_exp_neg {h : ℝ} (h0 : 0 ≤ h) : 2 * h ≤ Real.exp h - Real.exp (-h) := by
  have hmono : MonotoneOn (fun x : ℝ => Real.exp x - Real.exp (-x) - 2 * x) (Ici 0) := by
    have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.exp x - Real.exp (-x) - 2 * x)
        (Real.exp x + Real.exp (-x) - 2) x := by
      intro x
      have e1 : HasDerivAt (fun y : ℝ => Real.exp y) (Real.exp x) x := Real.hasDerivAt_exp x
      have e2 : HasDerivAt (fun y : ℝ => Real.exp (-y)) (Real.exp (-x) * (-1)) x :=
        (hasDerivAt_neg x).exp
      have e3 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
      exact ((e1.sub e2).sub e3).congr_deriv (by ring)
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun x _ => (hd x).continuousAt.continuousWithinAt
    · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
    · intro x _
      rw [(hd x).deriv]
      have h1 := Real.add_one_le_exp x
      have h2 := Real.add_one_le_exp (-x)
      linarith
  have := hmono (self_mem_Ici) (show h ∈ Ici 0 from h0) h0
  simp only [Real.exp_zero, neg_zero, sub_self, mul_zero] at this
  linarith

theorem log_four_pi_add_euler_lt_four :
    Real.log (4 * Real.pi) + Real.eulerMascheroniConstant < 4 := by
  have hlog : Real.log (4 * Real.pi) < 3 := by
    rw [Real.log_lt_iff_lt_exp (by positivity)]
    have hpi := Real.pi_lt_d2
    have h3 : (20 : ℝ) < Real.exp 3 := by
      have he := Real.exp_one_gt_d9
      calc (20 : ℝ) < 2.7182818283 ^ 3 := by norm_num
        _ ≤ Real.exp 1 ^ 3 := by gcongr
        _ = Real.exp 3 := by rw [← Real.exp_nat_mul]; norm_num
    linarith
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

theorem log_four_pi_add_euler_pos :
    0 < Real.log (4 * Real.pi) + Real.eulerMascheroniConstant := by
  have h1 : 0 < Real.log (4 * Real.pi) := Real.log_pos (by nlinarith [Real.pi_gt_three])
  linarith [Real.one_half_lt_eulerMascheroniConstant]

/-- **Quantitative bound on the sharp archimedean distribution.** If `|F| ≤ A` and `F` is
`A'`-Lipschitz, then for every `δ ∈ (0,1]`,
`|W_∞^♯(F)| ≤ A (8 + (3/2) log(1/δ)) + δ (A + A')/2`. -/
theorem norm_ccmArchimedeanWeilSharpDistribution_le (F : CCMCompactSchwartzLogTest)
    {A A' δ : ℝ} (hA : ∀ h, ‖F h‖ ≤ A) (hLip : ∀ h h', ‖F h - F h'‖ ≤ A' * |h - h'|)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖ccmArchimedeanWeilSharpDistribution F‖ ≤
      A * (8 + 3 / 2 * Real.log (1 / δ)) + δ * (A + A') / 2 := by
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) (hA 0)
  have hA'0 : 0 ≤ A' := by
    have h1 := hLip 1 0
    have h2 : (0 : ℝ) ≤ A' * |1 - 0| := le_trans (norm_nonneg _) h1
    simpa using h2
  -- the constant term
  have hconst : ‖F 0 / 2 * (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℂ)‖ ≤
      2 * A := by
    have hc : ‖(Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℂ)‖ ≤ 4 := by
      have : (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℂ) =
          ((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos log_four_pi_add_euler_pos]
      exact log_four_pi_add_euler_lt_four.le
    rw [norm_mul, norm_div, Complex.norm_ofNat]
    calc ‖F 0‖ / 2 * ‖(Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℂ)‖
        ≤ A / 2 * 4 := by
          apply mul_le_mul (div_le_div_of_nonneg_right (hA 0) (by norm_num)) hc (norm_nonneg _)
          positivity
      _ = 2 * A := by ring
  -- pointwise bounds on the integrand
  set I := ccmArchimedeanWeilSharpIntegrand F with hIdef
  have hden : ∀ {h : ℝ}, 0 < h → 0 < Real.exp h - Real.exp (-h) := fun {h} hh => by
    have := two_mul_le_exp_sub_exp_neg hh.le; linarith
  have hnormI : ∀ {h : ℝ}, 0 < h →
      ‖I h‖ = ‖ccmArchimedeanWeilSharpNumerator F h‖ / (Real.exp h - Real.exp (-h)) := by
    intro h hh
    rw [hIdef, ccmArchimedeanWeilSharpIntegrand, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hden hh)]
  have hnumNear : ∀ {h : ℝ}, 0 < h → h ≤ 1 →
      ‖ccmArchimedeanWeilSharpNumerator F h‖ ≤ h * (A + A') := by
    intro h hh hh1
    unfold ccmArchimedeanWeilSharpNumerator
    have hsplit : (Real.exp (h / 2) : ℂ) * F h - F 0 =
        ((Real.exp (h / 2) - 1 : ℝ) : ℂ) * F h + (F h - F 0) := by push_cast; ring
    have he0 : 0 ≤ Real.exp (h / 2) - 1 := by have := Real.add_one_le_exp (h / 2); linarith
    have he := exp_half_sub_one_le hh.le hh1
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he0]
    have h1 : (Real.exp (h / 2) - 1) * ‖F h‖ ≤ h * A :=
      mul_le_mul he (hA h) (norm_nonneg _) hh.le
    have h2 : ‖F h - F 0‖ ≤ A' * h := by
      have := hLip h 0; rwa [sub_zero, abs_of_pos hh] at this
    nlinarith
  have hnumFar : ∀ h, ‖ccmArchimedeanWeilSharpNumerator F h‖ ≤ (Real.exp (h / 2) + 1) * A := by
    intro h
    unfold ccmArchimedeanWeilSharpNumerator
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have := hA h; have := hA 0
    nlinarith [Real.exp_pos (h / 2)]
  have hb1 : ∀ h ∈ Ioc (0 : ℝ) δ, ‖I h‖ ≤ (A + A') / 2 := by
    intro h hh
    rw [hnormI hh.1, div_le_iff₀ (hden hh.1)]
    have := hnumNear hh.1 (le_trans hh.2 hδ1)
    have := two_mul_le_exp_sub_exp_neg hh.1.le
    nlinarith
  have hb2 : ∀ h ∈ Ioc δ 1, ‖I h‖ ≤ 3 / 2 * A * h⁻¹ := by
    intro h hh
    have hh0 : 0 < h := lt_trans hδ hh.1
    rw [hnormI hh0, div_le_iff₀ (hden hh0)]
    have hn := hnumFar h
    have he : Real.exp (h / 2) ≤ 2 := by
      have : Real.exp (h / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith [hh.2])
      have h12 : Real.exp (1 / 2) ≤ 2 := by
        have hb := Real.exp_bound_div_one_sub_of_interval (x := (1 / 2 : ℝ)) (by norm_num)
          (by norm_num)
        have h2 : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
        linarith
      linarith
    have h2h := two_mul_le_exp_sub_exp_neg hh0.le
    have hinv : 3 / 2 * A * h⁻¹ * (2 * h) = 3 * A := by field_simp
    have : (Real.exp (h / 2) + 1) * A ≤ 3 * A := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2h (show 0 ≤ 3 / 2 * A * h⁻¹ by positivity)]
  have hb3 : ∀ h ∈ Ioi (1 : ℝ), ‖I h‖ ≤ 4 * A * Real.exp (-(1 / 2) * h) := by
    intro h hh
    have hh0 : (0 : ℝ) < h := lt_trans one_pos hh
    rw [hnormI hh0, div_eq_mul_inv]
    have hinv := inv_exp_sub_exp_neg_le (le_of_lt hh)
    have hn := hnumFar h
    have he1 : 1 ≤ Real.exp (h / 2) := Real.one_le_exp (by linarith)
    have hn' : ‖ccmArchimedeanWeilSharpNumerator F h‖ ≤ 2 * Real.exp (h / 2) * A := by nlinarith
    calc ‖ccmArchimedeanWeilSharpNumerator F h‖ * (Real.exp h - Real.exp (-h))⁻¹
        ≤ (2 * Real.exp (h / 2) * A) * (2 * Real.exp (-h)) :=
          mul_le_mul hn' hinv (inv_nonneg.mpr (hden hh0).le) (by positivity)
      _ = 4 * A * (Real.exp (h / 2) * Real.exp (-h)) := by ring
      _ = 4 * A * Real.exp (-(1 / 2) * h) := by rw [← Real.exp_add]; congr 2; ring
  -- integrate the bounds over the three pieces
  have hInt := ccmArchimedeanWeilSharpIntegrand_integrableOn_Ioi F
  have hIntN : IntegrableOn (fun h => ‖I h‖) (Ioi 0) := hInt.norm
  have hsplit1 : Ioi (0 : ℝ) = Ioc 0 δ ∪ Ioi δ := (Ioc_union_Ioi_eq_Ioi hδ.le).symm
  have hsplit2 : Ioi δ = Ioc δ 1 ∪ Ioi (1 : ℝ) := (Ioc_union_Ioi_eq_Ioi hδ1).symm
  have hdisj1 : Disjoint (Ioc (0 : ℝ) δ) (Ioi δ) :=
    Set.disjoint_left.mpr fun x hx hx' => not_lt.mpr hx.2 hx'
  have hdisj2 : Disjoint (Ioc δ (1 : ℝ)) (Ioi 1) :=
    Set.disjoint_left.mpr fun x hx hx' => not_lt.mpr hx.2 hx'
  have hsub1 : Ioc (0 : ℝ) δ ⊆ Ioi 0 := fun x hx => hx.1
  have hsub2 : Ioi δ ⊆ Ioi (0 : ℝ) := fun x hx => lt_trans hδ hx
  have hsub3 : Ioc δ (1 : ℝ) ⊆ Ioi δ := fun x hx => hx.1
  have hsub4 : Ioi (1 : ℝ) ⊆ Ioi δ := fun x hx => lt_of_le_of_lt hδ1 hx
  have hsum : ∫ h in Ioi (0 : ℝ), ‖I h‖ =
      (∫ h in Ioc (0 : ℝ) δ, ‖I h‖) + (∫ h in Ioc δ (1 : ℝ), ‖I h‖) + ∫ h in Ioi (1 : ℝ), ‖I h‖ := by
    rw [hsplit1, setIntegral_union hdisj1 measurableSet_Ioi (hIntN.mono_set hsub1)
      (hIntN.mono_set hsub2), hsplit2, setIntegral_union hdisj2 measurableSet_Ioi
      ((hIntN.mono_set hsub2).mono_set hsub3) ((hIntN.mono_set hsub2).mono_set hsub4)]
    ring
  have hI1 : ∫ h in Ioc (0 : ℝ) δ, ‖I h‖ ≤ δ * ((A + A') / 2) := by
    calc ∫ h in Ioc (0 : ℝ) δ, ‖I h‖ ≤ ∫ _h in Ioc (0 : ℝ) δ, (A + A') / 2 :=
          setIntegral_mono_on (hIntN.mono_set hsub1) (integrableOn_const (by simp))
            measurableSet_Ioc hb1
      _ = δ * ((A + A') / 2) := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le hδ.le, smul_eq_mul, sub_zero]
  have hinvInt : IntegrableOn (fun h : ℝ => h⁻¹) (Ioc δ 1) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_inv₀.mono fun x hx => (lt_of_lt_of_le hδ hx.1).ne'
  have hI2 : ∫ h in Ioc δ (1 : ℝ), ‖I h‖ ≤ 3 / 2 * A * Real.log (1 / δ) := by
    calc ∫ h in Ioc δ (1 : ℝ), ‖I h‖ ≤ ∫ h in Ioc δ (1 : ℝ), 3 / 2 * A * h⁻¹ :=
          setIntegral_mono_on ((hIntN.mono_set hsub2).mono_set hsub3) (hinvInt.const_mul _)
            measurableSet_Ioc hb2
      _ = 3 / 2 * A * Real.log (1 / δ) := by
          rw [integral_const_mul, ← intervalIntegral.integral_of_le hδ1,
            integral_inv_of_pos hδ one_pos]
  have hI3 : ∫ h in Ioi (1 : ℝ), ‖I h‖ ≤ 6 * A := by
    have hexpInt := integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 1
    calc ∫ h in Ioi (1 : ℝ), ‖I h‖ ≤ ∫ h in Ioi (1 : ℝ), 4 * A * Real.exp (-(1 / 2) * h) :=
          setIntegral_mono_on ((hIntN.mono_set hsub2).mono_set hsub4) (hexpInt.const_mul _)
            measurableSet_Ioi hb3
      _ = 4 * A * (2 * Real.exp (-(1 / 2))) := by
          rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) 1]
          congr 1; field_simp
      _ ≤ 6 * A := by
          have : Real.exp (-(1 / 2)) ≤ 2 / 3 := by
            have h1 : Real.exp (1 / 2) ≥ 1 + 1 / 2 := by linarith [Real.add_one_le_exp (1 / 2 : ℝ)]
            have h2 : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
              rw [← Real.exp_add]; simp
            nlinarith [Real.exp_pos (-(1 / 2 : ℝ))]
          nlinarith
  rw [ccmArchimedeanWeilSharpDistribution]
  refine (norm_add_le _ _).trans ?_
  have hint := norm_integral_le_integral_norm (μ := volume.restrict (Ioi (0 : ℝ))) I
  have hlog : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  calc ‖F 0 / 2 * (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : ℂ)‖ +
        ‖∫ h in Ioi (0 : ℝ), I h‖
      ≤ 2 * A + (δ * ((A + A') / 2) + 3 / 2 * A * Real.log (1 / δ) + 6 * A) := by
        refine add_le_add hconst (hint.trans ?_)
        rw [hsum]; linarith
    _ = A * (8 + 3 / 2 * Real.log (1 / δ)) + δ * (A + A') / 2 := by ring

/-! ## The cross-correlation -/

section Cross

variable {a : SuzukiPositiveAperture} (u v : CCMComplexSmoothInteriorSource a)

theorem CCMComplexSmoothInteriorSource.continuous' : Continuous (u : ℝ → ℂ) :=
  u.smooth.continuous

theorem CCMComplexSmoothInteriorSource.integrable' : Integrable (u : ℝ → ℂ) :=
  u.continuous'.integrable_of_hasCompactSupport u.hasCompactSupport

theorem integrable_norm_mul_norm_shift (h : ℝ) :
    Integrable fun y : ℝ => ‖u y‖ * ‖v (y + h)‖ := by
  obtain ⟨C, hC⟩ := v.continuous'.bounded_above_of_compact_support v.hasCompactSupport
  refine (u.integrable'.norm.mul_const C).mono'
    ((u.continuous'.norm.mul (v.continuous'.comp (continuous_id.add continuous_const)).norm
      ).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

/-- `c(h) = ∫ v(y + h) conj(u(y)) dy`. -/
theorem ccmComplexSmoothCrossCorrelation_eq_shift (h : ℝ) :
    ccmComplexSmoothCrossCorrelation u v h = ∫ y : ℝ, v (y + h) * star (u y) := by
  rw [ccmComplexSmoothCrossCorrelation_apply]
  rw [← integral_add_right_eq_self (fun x => v.toFun x * star (u.toFun (x - h))) h]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [add_sub_cancel_right]

theorem norm_ccmComplexSmoothCrossCorrelation_le (h : ℝ) :
    ‖ccmComplexSmoothCrossCorrelation u v h‖ ≤ ∫ y : ℝ, ‖u y‖ * ‖v (y + h)‖ := by
  rw [ccmComplexSmoothCrossCorrelation_eq_shift]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  dsimp only
  rw [norm_mul, norm_star, mul_comm]

theorem norm_ccmComplexSmoothCrossCorrelation_le_sup {A : ℝ} (hA : ∀ x, ‖v x‖ ≤ A) (h : ℝ) :
    ‖ccmComplexSmoothCrossCorrelation u v h‖ ≤ A * ∫ y : ℝ, ‖u y‖ := by
  refine (norm_ccmComplexSmoothCrossCorrelation_le u v h).trans ?_
  rw [← integral_const_mul]
  refine integral_mono (integrable_norm_mul_norm_shift u v h) (u.integrable'.norm.const_mul A)
    fun y => ?_
  have := hA (y + h)
  nlinarith [norm_nonneg (u y)]

theorem norm_ccmComplexSmoothCrossCorrelation_sub_le {A' : ℝ} (hA' : ∀ x, ‖deriv v x‖ ≤ A')
    (h h' : ℝ) :
    ‖ccmComplexSmoothCrossCorrelation u v h - ccmComplexSmoothCrossCorrelation u v h'‖ ≤
      A' * |h - h'| * ∫ y : ℝ, ‖u y‖ := by
  have hvd : Differentiable ℝ (v : ℝ → ℂ) := v.smooth.differentiable (by simp)
  have hmv : ∀ p q : ℝ, ‖v p - v q‖ ≤ A' * |p - q| := by
    intro p q
    have := (convex_univ).norm_image_sub_le_of_norm_deriv_le (f := (v : ℝ → ℂ)) (C := A')
      (fun x _ => hvd x) (fun x _ => hA' x) (mem_univ q) (mem_univ p)
    simpa [Real.norm_eq_abs] using this
  have hi : ∀ t, Integrable fun y : ℝ => v (y + t) * star (u y) := by
    intro t
    refine (integrable_norm_mul_norm_shift u v t).mono'
      ((v.continuous'.comp (continuous_id.add continuous_const)).mul
        u.continuous'.star).aestronglyMeasurable (ae_of_all _ fun y => ?_)
    rw [norm_mul, norm_star, mul_comm]
  rw [ccmComplexSmoothCrossCorrelation_eq_shift, ccmComplexSmoothCrossCorrelation_eq_shift,
    ← integral_sub (hi h) (hi h'), ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (ae_of_all _ fun _ => norm_nonneg _) (u.integrable'.norm.const_mul _) (ae_of_all _ fun y => ?_))
  dsimp only
  rw [← sub_mul, norm_mul, norm_star]
  have := hmv (y + h) (y + h')
  rw [show y + h - (y + h') = h - h' by ring] at this
  exact mul_le_mul_of_nonneg_right this (norm_nonneg _)

end Cross

/-! ## The polar-prime functional -/

theorem criticalMellinAtomWeight_nonneg (k : ℕ) : 0 ≤ criticalMellinAtomWeight k := by
  unfold criticalMellinAtomWeight
  exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) ArithmeticFunction.vonMangoldt_nonneg

/-- **Polar-prime part.** `|P_a(c)| ≤ N (P₀ + S₀)` in terms of the pole lag integral and the
prime lag sum of `v`. -/
theorem norm_ccmRestrictedPolarPrimeFull_cross_le {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) {P₀ S₀ : ℝ}
    (hP : ∀ y : ℝ, |y| ≤ a.1 → ∫ h in Ioc (0 : ℝ) (2 * a.1),
      (‖v (y + h)‖ + ‖v (y - h)‖) * (2 * Real.cosh (h / 2)) ≤ P₀)
    (hS : ∀ y : ℝ, |y| ≤ a.1 → ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
      criticalMellinAtomWeight k * (‖v (y + Real.log k)‖ + ‖v (y - Real.log k)‖) ≤ S₀) :
    ‖ccmRestrictedPolarPrimeFull a.1 (ccmComplexSmoothCrossCorrelation u v)‖ ≤
      (∫ y : ℝ, ‖u y‖) * (P₀ + S₀) := by
  set c := ccmComplexSmoothCrossCorrelation u v with hc
  set N : ℝ := ∫ y : ℝ, ‖u y‖ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  have hP0 : 0 ≤ P₀ := le_trans (setIntegral_nonneg measurableSet_Ioc fun h hh =>
    mul_nonneg (by positivity) (by have := Real.cosh_pos (h / 2); linarith))
      (hP 0 (by simp [a.property.le]))
  have hu0 : ∀ y : ℝ, ¬ |y| ≤ a.1 → u y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have := u.tsupport_subset hmem
    exact hy (abs_le.mpr ⟨this.1.le, this.2.le⟩)
  -- the shifted correlation integrals
  have hcn : ∀ h, ‖c h‖ ≤ ∫ y : ℝ, ‖u y‖ * ‖v (y + h)‖ :=
    norm_ccmComplexSmoothCrossCorrelation_le u v
  have hcn' : ∀ h, ‖c (-h)‖ ≤ ∫ y : ℝ, ‖u y‖ * ‖v (y - h)‖ := by
    intro h
    have := hcn (-h)
    simpa [sub_eq_add_neg] using this
  have hi1 := integrable_norm_mul_norm_shift u v
  have hi2 : ∀ h, Integrable fun y : ℝ => ‖u y‖ * ‖v (y - h)‖ := by
    intro h; simpa [sub_eq_add_neg] using hi1 (-h)
  obtain ⟨Cv, hCv⟩ := v.continuous'.bounded_above_of_compact_support v.hasCompactSupport
  -- pole part
  set w : ℝ → ℝ := fun h => 2 * Real.cosh (h / 2) with hw
  have hw0 : ∀ h, 0 ≤ w h := fun h => by have := Real.cosh_pos (h / 2); simp only [hw]; linarith
  have hwc : Continuous w := by simp only [hw]; fun_prop
  set f : ℝ → ℝ → ℝ := fun h y => ‖u y‖ * ((‖v (y + h)‖ + ‖v (y - h)‖) * w h) with hf
  have hfint : Integrable (Function.uncurry f) ((volume.restrict (Ioc 0 (2 * a.1))).prod volume) := by
    have hwi : Integrable (fun h => 2 * Cv * w h) (volume.restrict (Ioc 0 (2 * a.1))) :=
      ((hwc.continuousOn.integrableOn_Icc (a := 0) (b := 2 * a.1)).mono_set
        Ioc_subset_Icc_self).const_mul _
    have hdom := hwi.mul_prod u.integrable'.norm
    refine hdom.mono' ?_ (ae_of_all _ fun p => ?_)
    · have hc1 : Continuous fun p : ℝ × ℝ => ‖u p.2‖ :=
        u.continuous'.norm.comp continuous_snd
      have hc2 : Continuous fun p : ℝ × ℝ => (‖v (p.2 + p.1)‖ + ‖v (p.2 - p.1)‖) * w p.1 :=
        (((v.continuous'.comp (continuous_snd.add continuous_fst)).norm.add
          (v.continuous'.comp (continuous_snd.sub continuous_fst)).norm).mul
          (hwc.comp continuous_fst))
      exact (hc1.mul hc2).aestronglyMeasurable
    · obtain ⟨h, y⟩ := p
      simp only [Function.uncurry_apply_pair, hf, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (norm_nonneg _) (mul_nonneg (by positivity) (hw0 h)))]
      have h1 := hCv (y + h); have h2 := hCv (y - h)
      have := hw0 h
      have hun := norm_nonneg (u y)
      nlinarith [mul_nonneg hun this]
  have hpole : ‖∫ h in Ioc (0 : ℝ) (2 * a.1), (c h + c (-h)) * (2 * Real.cosh (h / 2) : ℂ)‖ ≤
      N * P₀ := by
    calc ‖∫ h in Ioc (0 : ℝ) (2 * a.1), (c h + c (-h)) * (2 * Real.cosh (h / 2) : ℂ)‖
        ≤ ∫ h in Ioc (0 : ℝ) (2 * a.1), ∫ y : ℝ, f h y := by
          refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
            (ae_of_all _ fun _ => norm_nonneg _) hfint.integral_prod_left (ae_of_all _ fun h => ?_))
          have hwh : ‖(2 * Real.cosh (h / 2) : ℂ)‖ = w h := by
            rw [show (2 * Real.cosh (h / 2) : ℂ) = ((2 * Real.cosh (h / 2) : ℝ) : ℂ) by push_cast; ring,
              Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 h)]
          dsimp only
          rw [norm_mul, hwh]
          have hsum : ∫ y : ℝ, f h y =
              ((∫ y : ℝ, ‖u y‖ * ‖v (y + h)‖) + ∫ y : ℝ, ‖u y‖ * ‖v (y - h)‖) * w h := by
            rw [← integral_add (hi1 h) (hi2 h), ← integral_mul_const]
            refine integral_congr_ae (ae_of_all _ fun y => ?_)
            simp only [hf]; ring
          rw [hsum]
          exact mul_le_mul_of_nonneg_right ((norm_add_le _ _).trans (add_le_add (hcn h) (hcn' h)))
            (hw0 h)
      _ = ∫ y : ℝ, ∫ h in Ioc (0 : ℝ) (2 * a.1), f h y := integral_integral_swap hfint
      _ ≤ ∫ y : ℝ, ‖u y‖ * P₀ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun y => setIntegral_nonneg measurableSet_Ioc
            fun h _ => ?_) (u.integrable'.norm.mul_const _) (ae_of_all _ fun y => ?_)
          · simp only [hf]; exact mul_nonneg (norm_nonneg _) (mul_nonneg (by positivity) (hw0 h))
          · simp only [hf]
            rw [integral_const_mul]
            by_cases hy : |y| ≤ a.1
            · exact mul_le_mul_of_nonneg_left (hP y hy) (norm_nonneg _)
            · rw [hu0 y hy, norm_zero, zero_mul, zero_mul]
      _ = N * P₀ := by rw [integral_mul_const]
  -- prime part
  set K := Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊ with hK
  have hprime : ‖∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) *
      (c (Real.log k) + c (-Real.log k))‖ ≤ N * S₀ := by
    calc ‖∑ k ∈ K, (criticalMellinAtomWeight k : ℂ) * (c (Real.log k) + c (-Real.log k))‖
        ≤ ∑ k ∈ K, criticalMellinAtomWeight k *
            ((∫ y : ℝ, ‖u y‖ * ‖v (y + Real.log k)‖) + ∫ y : ℝ, ‖u y‖ * ‖v (y - Real.log k)‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (criticalMellinAtomWeight_nonneg k)]
          exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans
            (add_le_add (hcn _) (hcn' _))) (criticalMellinAtomWeight_nonneg k)
      _ = ∫ y : ℝ, ‖u y‖ * ∑ k ∈ K, criticalMellinAtomWeight k *
            (‖v (y + Real.log k)‖ + ‖v (y - Real.log k)‖) := by
          have hstep : ∀ k ∈ K, criticalMellinAtomWeight k *
              ((∫ y : ℝ, ‖u y‖ * ‖v (y + Real.log k)‖) + ∫ y : ℝ, ‖u y‖ * ‖v (y - Real.log k)‖) =
              ∫ y : ℝ, criticalMellinAtomWeight k *
                (‖u y‖ * ‖v (y + Real.log k)‖ + ‖u y‖ * ‖v (y - Real.log k)‖) := by
            intro k _
            rw [integral_const_mul, integral_add (hi1 _) (hi2 _)]
          have hint : ∀ k ∈ K, Integrable (fun y : ℝ => criticalMellinAtomWeight k *
              (‖u y‖ * ‖v (y + Real.log k)‖ + ‖u y‖ * ‖v (y - Real.log k)‖)) := fun k _ =>
            ((hi1 _).add (hi2 _)).const_mul _
          rw [Finset.sum_congr rfl hstep, ← integral_finsetSum K hint]
          refine integral_congr_ae (ae_of_all _ fun y => ?_)
          dsimp only
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ ∫ y : ℝ, ‖u y‖ * S₀ := by
          refine integral_mono_of_nonneg (ae_of_all _ fun y => mul_nonneg (norm_nonneg _)
            (Finset.sum_nonneg fun k _ => mul_nonneg (criticalMellinAtomWeight_nonneg k)
              (by positivity))) (u.integrable'.norm.mul_const _) (ae_of_all _ fun y => ?_)
          dsimp only
          by_cases hy : |y| ≤ a.1
          · exact mul_le_mul_of_nonneg_left (hS y hy) (norm_nonneg _)
          · rw [hu0 y hy, norm_zero, zero_mul, zero_mul]
      _ = N * S₀ := by rw [integral_mul_const]
  unfold ccmRestrictedPolarPrimeFull
  refine (norm_sub_le _ _).trans ?_
  calc _ ≤ N * P₀ + N * S₀ := add_le_add hpole hprime
    _ = N * (P₀ + S₀) := by ring

/-! ## The restricted Weil form -/

/-- **`L¹` bound for the restricted Weil form between smooth sources.** For every `δ ∈ (0,1]`,
`|Q_a(u, v)| ≤ N (P₀ + S₀ + 2A(8 + (3/2) log(1/δ)) + δ(A + A'))`, `N = ∫|u|`. -/
theorem norm_ccmRestrictedWeilForm_smooth_le {a : SuzukiPositiveAperture}
    (u v : CCMComplexSmoothInteriorSource a) {P₀ S₀ A A' δ : ℝ}
    (hP : ∀ y : ℝ, |y| ≤ a.1 → ∫ h in Ioc (0 : ℝ) (2 * a.1),
      (‖v (y + h)‖ + ‖v (y - h)‖) * (2 * Real.cosh (h / 2)) ≤ P₀)
    (hS : ∀ y : ℝ, |y| ≤ a.1 → ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a.1)⌋₊,
      criticalMellinAtomWeight k * (‖v (y + Real.log k)‖ + ‖v (y - Real.log k)‖) ≤ S₀)
    (hA : ∀ x, ‖v x‖ ≤ A) (hA' : ∀ x, ‖deriv v x‖ ≤ A') (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖ccmRestrictedWeilForm a u.toCCMFormVector v.toCCMFormVector‖ ≤
      (∫ y : ℝ, ‖u y‖) * (P₀ + S₀ + 2 * A * (8 + 3 / 2 * Real.log (1 / δ)) + δ * (A + A')) := by
  set N : ℝ := ∫ y : ℝ, ‖u y‖ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  rw [ccmRestrictedWeilForm_ccmComplexSmooth_eq_polarPrimeFull_sub_archimedean]
  refine (norm_sub_le _ _).trans ?_
  have hpp := norm_ccmRestrictedPolarPrimeFull_cross_le u v hP hS
  set F := ccmCompactSchwartzLogEvenization (ccmComplexSmoothCrossCorrelationTest u v) with hF
  have hFapply : ∀ h, F h = ccmComplexSmoothCrossCorrelation u v h +
      ccmComplexSmoothCrossCorrelation u v (-h) := fun h => by
    simp [hF, ccmCompactSchwartzLogEvenization]; rfl
  have hFA : ∀ h, ‖F h‖ ≤ 2 * A * N := by
    intro h
    rw [hFapply]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_ccmComplexSmoothCrossCorrelation_le_sup u v hA h
    have h2 := norm_ccmComplexSmoothCrossCorrelation_le_sup u v hA (-h)
    linarith
  have hFL : ∀ h h', ‖F h - F h'‖ ≤ 2 * A' * N * |h - h'| := by
    intro h h'
    rw [hFapply, hFapply]
    have hrw : ccmComplexSmoothCrossCorrelation u v h + ccmComplexSmoothCrossCorrelation u v (-h) -
        (ccmComplexSmoothCrossCorrelation u v h' + ccmComplexSmoothCrossCorrelation u v (-h')) =
        (ccmComplexSmoothCrossCorrelation u v h - ccmComplexSmoothCrossCorrelation u v h') +
        (ccmComplexSmoothCrossCorrelation u v (-h) - ccmComplexSmoothCrossCorrelation u v (-h')) := by
      ring
    rw [hrw]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_ccmComplexSmoothCrossCorrelation_sub_le u v hA' h h'
    have h2 := norm_ccmComplexSmoothCrossCorrelation_sub_le u v hA' (-h) (-h')
    rw [show -h - -h' = -(h - h') by ring, abs_neg] at h2
    linarith
  have harch := norm_ccmArchimedeanWeilSharpDistribution_le F hFA hFL hδ hδ1
  have harch' : ‖ccmArchimedeanWeilDistribution (ccmComplexSmoothCrossCorrelationTest u v)‖ ≤
      N * (2 * A * (8 + 3 / 2 * Real.log (1 / δ)) + δ * (A + A')) := by
    refine harch.trans (le_of_eq ?_)
    ring
  calc _ ≤ N * (P₀ + S₀) + N * (2 * A * (8 + 3 / 2 * Real.log (1 / δ)) + δ * (A + A')) :=
        add_le_add hpp harch'
    _ = N * (P₀ + S₀ + 2 * A * (8 + 3 / 2 * Real.log (1 / δ)) + δ * (A + A')) := by ring

end

end RHTower
