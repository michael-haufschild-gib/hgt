import GaloisForLFunctions.RHTower.ThetaPowerStripRigidity
import GaloisForLFunctions.RHTower.FiniteZeroSubquadraticTwoRayDecay
import GaloisForLFunctions.RHTower.ThetaCuspChargeHardyRigidity

/-!
# Zeros outside the critical strip above the cusp-order wall

For `a > 0` the axis tail `T_a(x) = e^{x/2} F_a(i e^{2x}) / 2` of `F_a = θ₃h^{a/4}` decays
doubly exponentially, since `|F_a(iy)| ≤ C e^{-πay/4}` for `y ≥ 1` and `T_a` is even.  Hence the
transform `Λ_a(w) = ∫ e^{-iwx} T_a(x) dx` is entire of order at most `3/2`, and by
Riemann–Lebesgue it tends to zero along both real rays.  An entire function of order below two
with this two-ray decay has infinitely many zeros.

For `a > 1/2` only finitely many of them lie in the closed strip `|Im w| ≤ 1/2`, so infinitely
many zeros satisfy `|Im w| > 1/2`: in the variable `s = 1/2 - iw` they lie outside the closed
critical strip `0 ≤ Re s ≤ 1`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

variable {a : ℝ}

/-- `x/2 - r e^{2x} ≤ 81/(4r) - x³ - x` for `r > 0`, `x ≥ 0`. -/
theorem half_sub_rate_exp_le {r x : ℝ} (hr : 0 < r) (hx : 0 ≤ x) :
    x / 2 - r * Real.exp (2 * x) ≤ 81 / (4 * r) - x ^ 3 - x := by
  have he := Real.sum_le_exp_of_nonneg hx 4
  norm_num [Finset.sum_range_succ] at he
  set u : ℝ := Real.exp x with hu
  have hu0 : 0 < u := Real.exp_pos x
  have h2 : Real.exp (2 * x) = u ^ 2 := by
    rw [hu, show 2 * x = x + x by ring, Real.exp_add]; ring
  have hsq : 0 ≤ r * (u - 9 / (2 * r)) ^ 2 := by positivity
  have hexp : r * (u - 9 / (2 * r)) ^ 2 = r * u ^ 2 - 9 * u + 81 / (4 * r) := by
    field_simp; ring
  rw [h2]
  nlinarith [sq_nonneg x, pow_nonneg hx 3]

theorem modTail_thetaPowerForm_neg (a x : ℝ) :
    modTail (thetaPowerForm a) 0 (-x) = modTail (thetaPowerForm a) 0 x := by
  have h := thetaPowerTail_even a (x : ℂ) (by
    rw [Complex.ofReal_im, abs_zero]; positivity)
  rwa [← Complex.ofReal_neg, chargeTailC_ofReal, chargeTailC_ofReal] at h

/-- **Cubic-exponential envelope of the axis tail.** -/
theorem exists_thetaPowerTail_cubic (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ,
      ‖modTail (thetaPowerForm a) 0 x‖ ≤ K * Real.exp (-|x| ^ 3 - |x|) := by
  set C : ℝ := thetaPowerCuspConstant a with hC
  set r : ℝ := π * a / 4 with hr
  have hr0 : 0 < r := by positivity
  have hC0 : 0 ≤ C := by
    have h := norm_thetaPowerForm_le_cusp ha.le (τ := Complex.I) (by simp)
    exact nonneg_of_mul_nonneg_left (le_trans (norm_nonneg _) h) (Real.exp_pos _)
  refine ⟨C / 2 * Real.exp (81 / (4 * r)), by positivity, ?_⟩
  have hpos : ∀ x : ℝ, 0 ≤ x → ‖modTail (thetaPowerForm a) 0 x‖ ≤
      C / 2 * Real.exp (81 / (4 * r)) * Real.exp (-x ^ 3 - x) := by
    intro x hx
    have hy : 1 ≤ (modAxisPoint x).im := by
      rw [modAxisPoint_im]; exact Real.one_le_exp (by linarith)
    have hF := norm_thetaPowerForm_le_cusp ha.le hy
    rw [modAxisPoint_im] at hF
    have hkey := half_sub_rate_exp_le hr0 hx
    unfold modTail
    rw [sub_zero, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_two]
    calc Real.exp (x / 2) * ‖thetaPowerForm a (modAxisPoint x)‖ / 2
        ≤ Real.exp (x / 2) * (C * Real.exp (-(π * a / 4) * Real.exp (2 * x))) / 2 := by gcongr
      _ = C / 2 * Real.exp (x / 2 - r * Real.exp (2 * x)) := by
          rw [Real.exp_sub, hr, show -(π * a / 4) * Real.exp (2 * x) =
            -(π * a / 4 * Real.exp (2 * x)) by ring, Real.exp_neg]
          field_simp
      _ ≤ C / 2 * Real.exp (81 / (4 * r) - x ^ 3 - x) := by gcongr
      _ = C / 2 * Real.exp (81 / (4 * r)) * Real.exp (-x ^ 3 - x) := by
          rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  intro x
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]; exact hpos x hx
  · have h := hpos (-x) (by linarith)
    rw [modTail_thetaPowerForm_neg] at h
    rw [abs_of_nonpos hx]; exact h

theorem continuous_modTail_thetaPowerForm (a : ℝ) :
    Continuous (modTail (thetaPowerForm a) 0) :=
  continuous_iff_continuousAt.mpr fun x =>
    (hasDerivAt_modTail 0 (differentiableOn_thetaPowerForm a) x).continuousAt

theorem norm_cexp_neg_I_mul_mul (w : ℂ) (x : ℝ) :
    ‖Complex.exp (-Complex.I * w * x)‖ = Real.exp (w.im * x) := by
  rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]

/-- The integrand of `Λ_a(w)` on `|Im w| ≤ ρ` is dominated by `K e^{(1+ρ)^{3/2}} e^{-|x|}`. -/
theorem norm_thetaPowerXiC_integrand_le {K ρ : ℝ} (hK : 0 ≤ K) (hρ : 0 ≤ ρ)
    (hT : ∀ x : ℝ, ‖modTail (thetaPowerForm a) 0 x‖ ≤ K * Real.exp (-|x| ^ 3 - |x|))
    {w : ℂ} (hw : |w.im| ≤ ρ) (x : ℝ) :
    ‖Complex.exp (-Complex.I * w * x) * modTail (thetaPowerForm a) 0 x‖ ≤
      K * Real.exp ((1 + ρ) ^ (3 / 2 : ℝ)) * Real.exp (-(1 * |x|)) := by
  rw [norm_mul, norm_cexp_neg_I_mul_mul]
  have h1 : Real.exp (w.im * x) ≤ Real.exp (ρ * |x|) :=
    Real.exp_le_exp.mpr (by
      calc w.im * x ≤ |w.im * x| := le_abs_self _
        _ = |w.im| * |x| := abs_mul _ _
        _ ≤ ρ * |x| := mul_le_mul_of_nonneg_right hw (abs_nonneg x))
  have h2 : ρ * |x| - |x| ^ 3 ≤ (1 + ρ) ^ (3 / 2 : ℝ) := linear_sub_cube_le_rpow hρ (abs_nonneg x)
  calc Real.exp (w.im * x) * ‖modTail (thetaPowerForm a) 0 x‖
      ≤ Real.exp (ρ * |x|) * (K * Real.exp (-|x| ^ 3 - |x|)) :=
        mul_le_mul h1 (hT x) (norm_nonneg _) (Real.exp_pos _).le
    _ = K * Real.exp (ρ * |x| - |x| ^ 3) * Real.exp (-(1 * |x|)) := by
        rw [mul_comm, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]; congr 2; ring
    _ ≤ K * Real.exp ((1 + ρ) ^ (3 / 2 : ℝ)) * Real.exp (-(1 * |x|)) := by
        gcongr

/-- **`Λ_a` is entire** for `a > 0`. -/
theorem differentiable_thetaPowerXiC (ha : 0 < a) : Differentiable ℂ (thetaPowerXiC a) := by
  obtain ⟨K, hK0, hT⟩ := exists_thetaPowerTail_cubic ha
  have hTc := continuous_modTail_thetaPowerForm a
  intro w₀
  set ρ : ℝ := |w₀.im| + 1 with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set E : ℝ := Real.exp ((1 + ρ) ^ (3 / 2 : ℝ)) with hE
  set g : ℂ → ℝ → ℂ := fun w x => Complex.exp (-Complex.I * w * x) *
    modTail (thetaPowerForm a) 0 x with hg
  set g' : ℂ → ℝ → ℂ := fun w x => (-Complex.I * x) * g w x with hg'
  have hmeas : ∀ w : ℂ, AEStronglyMeasurable (g w) volume := fun w =>
    ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-Complex.I * w * x)).mul hTc).aestronglyMeasurable
  have hdomC : ∀ w : ℂ, |w.im| ≤ ρ → ∀ x : ℝ, ‖g w x‖ ≤ K * E * Real.exp (-(1 * |x|)) :=
    fun w hw x => norm_thetaPowerXiC_integrand_le hK0 hρ0 hT hw x
  have hint : Integrable (g w₀) :=
    Integrable.mono' ((integrable_exp_neg_mul_abs' one_pos).const_mul (K * E)) (hmeas w₀)
      (Filter.Eventually.of_forall fun x => hdomC w₀ (by rw [hρ]; linarith) x)
  set bound : ℝ → ℝ := fun x => K * E * 2 * Real.exp (-((1 / 2) * |x|)) with hbound
  have hboundInt : Integrable bound :=
    (integrable_exp_neg_mul_abs' (by norm_num : (0:ℝ) < 1 / 2)).const_mul _
  have hdom : ∀ᵐ x : ℝ, ∀ w ∈ Metric.ball w₀ 1, ‖g' w x‖ ≤ bound x := by
    filter_upwards with x
    intro w hw
    have hdist : ‖w - w₀‖ < 1 := by rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
    have him : |w.im - w₀.im| ≤ ‖w - w₀‖ := by
      simpa only [Complex.sub_im] using Complex.abs_im_le_norm (w - w₀)
    have hwρ : |w.im| ≤ ρ := by
      calc |w.im| = |w₀.im + (w.im - w₀.im)| := by ring_nf
        _ ≤ |w₀.im| + |w.im - w₀.im| := abs_add_le _ _
        _ ≤ ρ := by rw [hρ]; linarith
    have h1 := hdomC w hwρ x
    simp only [hg']
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hxexp : |x| ≤ 2 * Real.exp ((1 / 2) * |x|) := by
      have := Real.add_one_le_exp ((1 / 2) * |x|); linarith
    have hKE : 0 ≤ K * E := by positivity
    calc |x| * ‖g w x‖ ≤ (2 * Real.exp ((1 / 2) * |x|)) * (K * E * Real.exp (-(1 * |x|))) :=
          mul_le_mul hxexp h1 (norm_nonneg _) (by positivity)
      _ = bound x := by
          rw [hbound]
          have e : Real.exp ((1 / 2) * |x|) * Real.exp (-(1 * |x|)) =
              Real.exp (-((1 / 2) * |x|)) := by rw [← Real.exp_add]; congr 1; ring
          calc 2 * Real.exp ((1 / 2) * |x|) * (K * E * Real.exp (-(1 * |x|)))
              = K * E * 2 * (Real.exp ((1 / 2) * |x|) * Real.exp (-(1 * |x|))) := by ring
            _ = _ := by rw [e]
  have hderiv : ∀ᵐ x : ℝ, ∀ w ∈ Metric.ball w₀ 1, HasDerivAt (fun w => g w x) (g' w x) w := by
    filter_upwards with x
    intro w _
    simp only [hg, hg']
    have h := ((hasDerivAt_id w).const_mul (-Complex.I)).mul_const (x : ℂ)
    have h2 := (h.cexp).mul_const (modTail (thetaPowerForm a) 0 x)
    refine h2.congr_deriv ?_
    simp only [id]
    ring
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := g) (F' := g') (x₀ := w₀) (bound := bound)
    (Metric.ball_mem_nhds w₀ one_pos) (Filter.Eventually.of_forall hmeas) hint
    ((((by fun_prop : Continuous fun x : ℝ => -Complex.I * (x : ℂ)).mul
      ((by fun_prop : Continuous fun x : ℝ => Complex.exp (-Complex.I * w₀ * x)).mul hTc))).aestronglyMeasurable)
    hdom hboundInt hderiv
  exact hres.2.differentiableAt

/-- **Order-`3/2` growth of `Λ_a`.** -/
theorem norm_thetaPowerXiC_growth (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ,
      ‖thetaPowerXiC a z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨K, hK, hT⟩ := exists_thetaPowerTail_cubic ha
  refine ⟨2 * K + 2, by positivity, fun z => ?_⟩
  set Y : ℝ := |z.im|
  have hY : 0 ≤ Y := abs_nonneg _
  set E : ℝ := Real.exp ((1 + Y) ^ (3 / 2 : ℝ)) with hE
  have hmaj : Integrable (fun x : ℝ => K * E * Real.exp (-(1 * |x|))) :=
    (integrable_exp_neg_mul_abs' one_pos).const_mul _
  have hint : ‖thetaPowerXiC a z‖ ≤ 2 * K * E := by
    unfold thetaPowerXiC
    calc ‖∫ x : ℝ, Complex.exp (-Complex.I * z * x) * modTail (thetaPowerForm a) 0 x‖
        ≤ ∫ x : ℝ, ‖Complex.exp (-Complex.I * z * x) * modTail (thetaPowerForm a) 0 x‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ x : ℝ, K * E * Real.exp (-(1 * |x|)) :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _) hmaj
            (Eventually.of_forall fun x => norm_thetaPowerXiC_integrand_le hK hY hT le_rfl x)
      _ = 2 * K * E := by rw [integral_const_mul, integral_exp_neg_mul_abs_eq one_pos]; ring
  have hYz : 1 + Y ≤ 1 + ‖z‖ := by linarith [Complex.abs_im_le_norm z]
  have hr : (1 + Y) ^ (3 / 2 : ℝ) ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hYz (by norm_num)
  have hr1 : 1 ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [norm_nonneg z]) (by norm_num)
  refine le_trans hint ?_
  have h2K : 2 * K ≤ Real.exp (2 * K) := by have := Real.add_one_le_exp (2 * K); linarith
  calc 2 * K * E ≤ Real.exp (2 * K) * Real.exp ((1 + ‖z‖) ^ (3 / 2 : ℝ)) :=
        mul_le_mul h2K (Real.exp_le_exp.mpr hr) (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp (2 * K + (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by rw [Real.exp_add]
    _ ≤ Real.exp ((2 * K + 2) * (1 + ‖z‖) ^ (3 / 2 : ℝ)) := by
        apply Real.exp_le_exp.mpr; nlinarith

/-- Riemann–Lebesgue along the positive real ray. -/
theorem tendsto_thetaPowerXiC_atTop (a : ℝ) :
    Tendsto (fun r : ℝ => ‖thetaPowerXiC a (r : ℂ)‖) atTop (𝓝 0) := by
  set k : ℝ → ℂ := modTail (thetaPowerForm a) 0 with hk
  have hRL := Real.tendsto_integral_exp_smul_cocompact k
  have hlin : Tendsto (fun r : ℝ => r / (2 * π)) atTop (cocompact ℝ) :=
    (tendsto_id.atTop_div_const (by positivity)).mono_right atTop_le_cocompact
  have h := (hRL.comp hlin).norm
  rw [norm_zero] at h
  refine h.congr (fun r => ?_)
  simp only [Function.comp]
  congr 1
  unfold thetaPowerXiC
  congr 1; funext v
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  congr 1; congr 1
  push_cast; field_simp

theorem tendsto_thetaPowerXiC_atTop_neg (a : ℝ) :
    Tendsto (fun r : ℝ => ‖thetaPowerXiC a ((-r : ℝ) : ℂ)‖) atTop (𝓝 0) := by
  refine (tendsto_thetaPowerXiC_atTop a).congr (fun r => ?_)
  rw [Complex.ofReal_neg, thetaPowerXiC_neg]

/-- **Infinitely many zeros.** For `a > 0` the entire function `Λ_a` has infinitely many zeros. -/
theorem thetaPowerXiC_zeros_infinite (ha : 0 < a) :
    {w : ℂ | thetaPowerXiC a w = 0}.Infinite := by
  obtain ⟨C, hC, hg⟩ := norm_thetaPowerXiC_growth ha
  exact zeroSet_infinite_of_subquadratic_twoRayDecay (differentiable_thetaPowerXiC ha)
    (by norm_num : (0:ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) < 2) hC hg
    (tendsto_thetaPowerXiC_atTop a) (tendsto_thetaPowerXiC_atTop_neg a)

/-- **Zeros outside the critical strip above the wall.** For `a > 1/2`, infinitely many zeros of
`Λ_a` satisfy `|Im w| > 1/2`; in `s = 1/2 - iw` they lie outside `0 ≤ Re s ≤ 1`. -/
theorem thetaPowerXiC_offStrip_zeros_infinite (ha : 1 / 2 < a) :
    {w : ℂ | 1 / 2 < |w.im| ∧ thetaPowerXiC a w = 0}.Infinite := by
  intro hoff
  apply thetaPowerXiC_zeros_infinite (by linarith : 0 < a)
  refine ((thetaPowerXiC_strip_zeros_finite ha).union hoff).subset fun w hw => ?_
  by_cases h : |w.im| ≤ 1 / 2
  · exact Or.inl ⟨h, hw⟩
  · exact Or.inr ⟨lt_of_not_ge h, hw⟩

end RHTower
