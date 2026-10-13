import GaloisForLFunctions.RHTower.DeBruijnNegativeTimeDirichletModel
import GaloisForLFunctions.RHTower.DeBruijnBarrierZerosSimple

/-!
# Newman's conjecture: `H_t` has infinitely many non-real zeros for every `t < 0`

Fix `τ > 0`. For a zero `w₀` of the Gaussian-damped zeta series `F_τ` and heights `T → ∞`, put
`L_T = ½ log(T/2π) + iπ/4`, `s_T(w) = w + iT + 2τL_T` and `a_T = 2 − Re w₀ − 2τ Re L_T`. The
model error bound of `DeBruijnNegativeTimeDirichletModel`, the lower bound for the archimedean factor
and the choice `V_T = √(16τT(log T + 3))` give

`‖A_τ(s_T(w)) / N_T(s_T(w)) − F_τ(w + iT)‖ → 0`   uniformly on `|w − w₀| ≤ ρ`

(`eventually_norm_negHeatS_div_sub_le`), where `N_T(s) = G(s + a_T) e^{−a_T L_T − τL_T²}`. Almost
periodicity of `F_τ` supplies heights with `F_τ(w + iT) ≈ F_τ(w)`, and the minimum modulus principle
gives a zero of `A_τ` near `s_T(w₀)`, whose real part `Re w₀ + τ log(T/2π)` exceeds `½`. Hence
`H_{−τ}` has non-real zeros of arbitrarily large real part
(`riemannHeat_neg_nonreal_zeros_infinite`), and their depth grows logarithmically:
`−Im z ≥ τ log(Re z) − C` along zeros with `Re z → ∞` (`exists_riemannHeat_neg_zero_deep`).
More precisely, every zero `w₀` of `F_τ` is reproduced within any `ε` by zeros of `H_{−τ}` near
`−i(s_T(w₀) − ½)` at arbitrarily large `T` (`exists_riemannHeat_neg_zero_near_model`).
-/

open Complex MeasureTheory Filter Topology Set Metric

namespace RHTower.DeBruijn

noncomputable section

/-! ## Asymptotics of the explicit bound -/

/-- The cut-off `V_T = √(16τT(log T + 3))`. -/
def cutoffV (τ T : ℝ) : ℝ := Real.sqrt (16 * τ * T * (Real.log T + 3))

theorem cutoffV_sq {τ T : ℝ} (hτ : 0 < τ) (hT : 1 ≤ T) :
    cutoffV τ T ^ 2 / (8 * τ) = 2 * T * (Real.log T + 3) := by
  have hl : 0 ≤ Real.log T := Real.log_nonneg hT
  rw [cutoffV, Real.sq_sqrt (by positivity)]
  field_simp
  ring

theorem tendsto_const_div_atTop (c : ℝ) : Tendsto (fun T : ℝ => c / T) atTop (𝓝 0) := by
  have := tendsto_inv_atTop_zero.const_mul c
  rw [mul_zero] at this
  exact this.congr fun T => (div_eq_mul_inv c T).symm

theorem tendsto_cutoffV_div {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (fun T => cutoffV τ T / T) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => Real.log T ^ 1 / (1 * T + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h3 : Tendsto (fun T : ℝ => 16 * τ * ((Real.log T + 3) / T)) atTop (𝓝 0) := by
    have := (h1.add (tendsto_const_div_atTop 3)).const_mul (16 * τ)
    simp only [pow_one, one_mul, add_zero, mul_zero] at this
    refine this.congr' ((eventually_gt_atTop 0).mono fun T hT => ?_)
    dsimp only
    rw [add_div]
  have h4 := h3.sqrt
  rw [Real.sqrt_zero] at h4
  refine h4.congr' ((eventually_ge_atTop 1).mono fun T hT => ?_)
  have hT0 : 0 < T := by linarith
  have hl : 0 ≤ Real.log T := Real.log_nonneg hT
  have hV : 0 ≤ cutoffV τ T := Real.sqrt_nonneg _
  dsimp only
  rw [← Real.sqrt_sq (div_nonneg hV hT0.le), div_pow, cutoffV, Real.sq_sqrt (by positivity)]
  congr 1
  field_simp

theorem tendsto_eta_bound {τ : ℝ} (hτ : 0 < τ) (c : ℝ) :
    Tendsto (fun T => (12 + c + cutoffV τ T) / T) atTop (𝓝 0) := by
  have := (tendsto_const_div_atTop (12 + c)).add (tendsto_cutoffV_div hτ)
  rw [add_zero] at this
  refine this.congr' ((eventually_gt_atTop 0).mono fun T hT => ?_)
  dsimp only
  ring

/-- The growth `e^{(T + c)(log(T + c) + 2)}` of `1/‖G‖` is beaten by `e^{−V_T²/(8τ)}`. -/
theorem tendsto_exp_tail {τ : ℝ} (hτ : 0 < τ) {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun T => Real.exp (-(cutoffV τ T ^ 2 / (8 * τ)) +
      (T + c) * (Real.log (T + c) + 2))) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp (tendsto_atBot_mono' atTop ?_
    (tendsto_atBot_add_const_right atTop c tendsto_neg_atTop_atBot))
  filter_upwards [eventually_ge_atTop (max c 1 + 1)] with T hT
  have hT1 : 1 ≤ T := by linarith [le_max_right c 1]
  have hTc : c ≤ T := by linarith [le_max_left c 1]
  have hT0 : 0 < T := by linarith
  rw [cutoffV_sq hτ hT1]
  have hl : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog : Real.log (T + c) ≤ Real.log T + 1 := by
    have : Real.log (T + c) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hT0.ne'] at this
    have := Real.log_two_lt_d9
    linarith
  have h1 : (T + c) * (Real.log (T + c) + 2) ≤ (T + c) * (Real.log T + 3) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (T + c) * (Real.log T + 3) ≤ 2 * T * (Real.log T + 3) - (T - c) * 3 := by
    nlinarith
  linarith

/-! ## Spheres around zeros -/

/-- An entire function that is not identically zero is bounded below on small circles. -/
theorem exists_sphere_lower_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) {p : ℂ}
    (hp : f p ≠ 0) (w₀ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ δ : ℝ, 0 < ρ ∧ ρ ≤ ε ∧ 0 < δ ∧ ∀ w ∈ sphere w₀ ρ, δ ≤ ‖f w‖ := by
  rcases (hf.analyticAt w₀).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    exact hp ((hf.differentiableOn.analyticOnNhd isOpen_univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ w₀) h (mem_univ p))
  · obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.mem_nhdsWithin_iff.mp h
    set ρ := min (ρ₀ / 2) ε
    have hρ : 0 < ρ := lt_min (by positivity) hε
    have hne : ∀ w ∈ sphere w₀ ρ, f w ≠ 0 := by
      intro w hw
      refine hball ⟨?_, ?_⟩
      · rw [mem_ball, mem_sphere.mp hw]
        exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
      · intro hww
        rw [mem_singleton_iff.mp hww, mem_sphere, dist_self] at hw
        linarith
    obtain ⟨w₁, hw₁, hmin⟩ := (isCompact_sphere w₀ ρ).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr hρ.le) hf.continuous.norm.continuousOn
    exact ⟨ρ, ‖f w₁‖, hρ, min_le_right _ _, norm_pos_iff.mpr (hne w₁ hw₁), fun w hw => hmin hw⟩

/-! ## Differentiability at negative times and a local minimum modulus principle -/

theorem SuperExpKernel.mul_exp_sq_any {g : ℝ → ℝ} (hg : SuperExpKernel g) (t : ℝ) :
    SuperExpKernel (fun x => g x * Real.exp (t * x ^ 2)) where
  continuous := hg.continuous.mul (by fun_prop)
  even x := by simp only [even_two.neg_pow, hg.even]
  nonneg x := mul_nonneg (hg.nonneg x) (Real.exp_pos _).le
  pos_zero := by simpa using hg.pos_zero
  decay := by
    obtain ⟨A, B, b, c, hA, hB, hb, hc, hdec⟩ := hg.decay
    refine ⟨A, B, b, c + |t|, hA, hB, hb, by positivity, fun x => ?_⟩
    calc g x * Real.exp (t * x ^ 2) ≤ A * Real.exp (-(B * Real.exp (b * |x|)) + c * x ^ 2) *
          Real.exp (|t| * x ^ 2) :=
          mul_le_mul (hdec x) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self t)
            (sq_nonneg x))) (Real.exp_pos _).le (mul_nonneg hA (Real.exp_pos _).le)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; ring_nf

theorem differentiable_riemannHeat_any (t : ℝ) : Differentiable ℂ (riemannHeat t) :=
  (riemannKernel_superExp.mul_exp_sq_any t).differentiable

/-- If `f` is holomorphic near the closed disc and `|f(c)| < |f|` on its boundary circle, then `f`
vanishes in the disc. -/
theorem exists_zero_of_norm_lt_sphere_on {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (closedBall c ρ)) (h : ∀ z ∈ sphere c ρ, ‖f c‖ < ‖f z‖) :
    ∃ z ∈ ball c ρ, f z = 0 := by
  by_contra hne
  simp only [not_exists, not_and] at hne
  have hcl : ∀ z ∈ closedBall c ρ, f z ≠ 0 := by
    intro z hz
    rcases eq_or_lt_of_le (mem_closedBall.mp hz) with h1 | h1
    · exact norm_pos_iff.mp ((norm_nonneg _).trans_lt (h z (mem_sphere.mpr h1)))
    · exact hne z (mem_ball.mpr h1)
  obtain ⟨z₁, hz₁, hmin⟩ := (isCompact_sphere c ρ).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr hρ.le)
    (hf.continuousOn.norm.mono sphere_subset_closedBall)
  have hg : DiffContOnCl ℂ (fun z => (f z)⁻¹) (ball c ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball c hρ.ne']
    exact hf.inv hcl
  have hbd := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hg
    (C := ‖f z₁‖⁻¹) (fun z hz => by
      rw [frontier_ball c hρ.ne'] at hz
      rw [norm_inv]
      exact inv_anti₀ (norm_pos_iff.mpr (hcl z₁ (sphere_subset_closedBall hz₁))) (hmin hz))
    (subset_closure (mem_ball_self hρ))
  rw [norm_inv] at hbd
  have h1 := h z₁ hz₁
  have hc : 0 < ‖f c‖ := norm_pos_iff.mpr (hcl c (mem_closedBall_self hρ.le))
  have := (inv_le_inv₀ hc (hc.trans h1)).mp hbd
  linarith

/-! ## The disc approximation -/

/-- The line shift `a_T = 2 − Re w₀ − 2τ Re L_T`. -/
def lineShift (τ : ℝ) (w₀ : ℂ) (T : ℝ) : ℝ := 2 - w₀.re - 2 * τ * (horizontalSlope T).re

/-- The point `s_T(w) = w + iT + 2τL_T`. -/
def discPoint (τ T : ℝ) (w : ℂ) : ℂ := w + T * I + 2 * τ * horizontalSlope T

/-- The normaliser `N_T(s) = G(s + a_T) e^{−a_T L_T − τL_T²}`. -/
def normaliser (τ : ℝ) (w₀ : ℂ) (T : ℝ) (s : ℂ) : ℂ :=
  archG (s + lineShift τ w₀ T) *
    Complex.exp (-(lineShift τ w₀ T * horizontalSlope T) - τ * horizontalSlope T ^ 2)

theorem discPoint_sub (τ T : ℝ) (w : ℂ) :
    discPoint τ T w - 2 * τ * horizontalSlope T = w + T * I := by
  rw [discPoint]; ring

theorem discPoint_add_lineShift (τ T : ℝ) (w₀ w : ℂ) :
    discPoint τ T w + lineShift τ w₀ T =
      ((2 + w.re - w₀.re : ℝ) : ℂ) + ((w.im + T + τ * (Real.pi / 2) : ℝ) : ℂ) * I := by
  apply Complex.ext <;> simp [discPoint, lineShift, horizontalSlope] <;> ring

theorem norm_exp_normaliser (τ : ℝ) (w₀ : ℂ) (T : ℝ) :
    ‖Complex.exp (-(lineShift τ w₀ T * horizontalSlope T) - τ * horizontalSlope T ^ 2)‖ =
      Real.exp (-(lineShift τ w₀ T * (horizontalSlope T).re) -
        τ * ((horizontalSlope T).re ^ 2 - (Real.pi / 4) ^ 2)) := by
  rw [Complex.norm_exp]
  congr 1
  have him : (horizontalSlope T).im = Real.pi / 4 := by simp [horizontalSlope]
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, pow_two, him]
  ring

/-- **The approximation on discs.** For `0 < ρ ≤ ½` and `ε > 0`, eventually in `T`,
`‖A_τ(s_T(w)) − N_T(s_T(w)) F_τ(w + iT)‖ ≤ ε ‖N_T(s_T(w))‖` on `|w − w₀| ≤ ρ`. -/
theorem eventually_norm_negHeatS_sub_le {τ : ℝ} (hτ : 0 < τ) (w₀ : ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hρ' : ρ ≤ 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∀ w ∈ closedBall w₀ ρ,
      ‖negHeatS τ (discPoint τ T w) -
          normaliser τ w₀ T (discPoint τ T w) * gaussDirichlet τ (w + T * I)‖ ≤
        ε * ‖normaliser τ w₀ T (discPoint τ T w)‖ := by
  obtain ⟨m, hm, hlow⟩ := exists_norm_archG_lower
  set c₀ := |w₀.im| + ρ + τ * (Real.pi / 2) with hc₀
  have hc₀0 : 0 ≤ c₀ := by positivity
  set cτ := (4 * Real.pi * τ) ^ (-(1 / 2 : ℝ))
  set K₁ := ∫ u, |u| * Real.exp (-(1 / (4 * τ) * u ^ 2) + (Real.pi / 4 + 1) * |u|)
  set K₂ := ∫ u, Real.exp (-(1 / (8 * τ) * u ^ 2) + 0 * |u|)
  set K₃ := ∫ u, Real.exp (-(1 / (8 * τ) * u ^ 2) + Real.pi / 4 * |u|)
  set M₂ := ∫ x, riemannKernelReal x * Real.exp (2 * |x|)
  set B := (2 - w₀.re) ^ 2 / (4 * τ)
  set K := cτ * Real.exp B
  have hK₁ : 0 ≤ K₁ := integral_nonneg fun u => by positivity
  have hK₂ : 0 ≤ K₂ := integral_nonneg fun u => by positivity
  have hK₃ : 0 ≤ K₃ := integral_nonneg fun u => by positivity
  have hM₂ : 0 ≤ M₂ := integral_nonneg fun x => by have := riemannKernelReal_pos x; positivity
  have hK : 0 ≤ K := by positivity
  -- eventual conditions
  have hη := tendsto_eta_bound hτ c₀
  have hexp := tendsto_exp_tail hτ hc₀0
  have e1 : ∀ᶠ T in atTop, (12 + c₀ + cutoffV τ T) / T ≤ 1 / 2 :=
    hη.eventually (eventually_le_nhds (by norm_num))
  have e2 : ∀ᶠ T in atTop, K * 3 * K₁ * ((12 + c₀ + cutoffV τ T) / T) ≤ ε / 2 := by
    have h := hη.const_mul (K * 3 * K₁)
    rw [mul_zero] at h
    exact h.eventually (eventually_le_nhds (by positivity : 0 < ε / 2))
  have e3 : ∀ᶠ T in atTop, K * (M₂ * K₂ / m + 3 * K₃) *
      Real.exp (-(cutoffV τ T ^ 2 / (8 * τ)) + (T + c₀) * (Real.log (T + c₀) + 2)) ≤ ε / 2 := by
    have h := hexp.const_mul (K * (M₂ * K₂ / m + 3 * K₃))
    rw [mul_zero] at h
    exact h.eventually (eventually_le_nhds (by positivity : 0 < ε / 2))
  filter_upwards [e1, e2, e3, eventually_ge_atTop (48 + c₀)] with T h1 h2 h3 hT w hw
  have hT48 : 48 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  set V := cutoffV τ T
  have hV0 : 0 ≤ V := Real.sqrt_nonneg _
  set s := discPoint τ T w
  set a := lineShift τ w₀ T
  set L := horizontalSlope T
  have hwre : |w.re - w₀.re| ≤ ρ := by
    have := (Complex.abs_re_le_norm (w - w₀)).trans (mem_closedBall_iff_norm.mp hw)
    simpa using this
  have hwim : |w.im - w₀.im| ≤ ρ := by
    have := (Complex.abs_im_le_norm (w - w₀)).trans (mem_closedBall_iff_norm.mp hw)
    simpa using this
  set σ₁ := 2 + w.re - w₀.re
  set X₁ := w.im + T + τ * (Real.pi / 2)
  have hσ₁ : 3 / 2 ≤ σ₁ := by have := (abs_le.mp hwre).1; simp only [σ₁]; linarith
  have hσ₁' : σ₁ ≤ 5 / 2 := by have := (abs_le.mp hwre).2; simp only [σ₁]; linarith
  have hX₁T : |X₁ - T| ≤ c₀ := by
    have e : X₁ - T = w.im + τ * (Real.pi / 2) := by simp only [X₁]; ring
    rw [e]
    have h1 : |w.im| ≤ |w₀.im| + ρ := by
      have := abs_sub_abs_le_abs_sub w.im w₀.im
      linarith
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by positivity : 0 ≤ τ * (Real.pi / 2))]
    linarith
  have hsum : 12 + c₀ + V ≤ T / 2 := by
    rw [div_le_iff₀ hT0] at h1; linarith
  have hV : |X₁ - T| + V ≤ T / 2 := by linarith
  have hηle : (12 + |X₁ - T| + V) / T ≤ 1 := by
    rw [div_le_one hT0]; linarith
  have hw₁ : s + a = (σ₁ : ℂ) + X₁ * I := discPoint_add_lineShift τ T w₀ w
  have hE := norm_negHeatS_sub_model_le hτ hσ₁ hσ₁' hT48 hV0 hV hηle hw₁
  rw [discPoint_sub] at hE
  -- the normaliser
  set G₁ := archG (s + a)
  have hN : ‖normaliser τ w₀ T s‖ = ‖G₁‖ * Real.exp (-(a * L.re) - τ * (L.re ^ 2 - (Real.pi / 4) ^ 2)) := by
    rw [normaliser, norm_mul, norm_exp_normaliser]
  have hX₁24 : 24 ≤ X₁ := by have := (abs_le.mp hX₁T).1; linarith
  have hG₁low : m * Real.exp (-((X₁ - 24) * (Real.log X₁ + 2))) ≤ ‖G₁‖ := by
    have := hlow σ₁ ⟨hσ₁, hσ₁'⟩ X₁ hX₁24
    rwa [← hw₁] at this
  have hG₁pos : 0 < ‖G₁‖ := lt_of_lt_of_le (by positivity) hG₁low
  have hinvG : 1 / ‖G₁‖ ≤ Real.exp ((T + c₀) * (Real.log (T + c₀) + 2)) / m := by
    rw [div_le_div_iff₀ hG₁pos hm, one_mul]
    have hX₁le : X₁ ≤ T + c₀ := by have := (abs_le.mp hX₁T).2; linarith
    have hP : (X₁ - 24) * (Real.log X₁ + 2) ≤ (T + c₀) * (Real.log (T + c₀) + 2) := by
      have hl1 : 0 ≤ Real.log X₁ + 2 := by have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ X₁); linarith
      have hl2 : Real.log X₁ ≤ Real.log (T + c₀) := Real.log_le_log (by linarith) hX₁le
      calc (X₁ - 24) * (Real.log X₁ + 2) ≤ (T + c₀) * (Real.log X₁ + 2) := by
            gcongr; linarith
        _ ≤ (T + c₀) * (Real.log (T + c₀) + 2) := by gcongr
    have := hG₁low
    calc m ≤ ‖G₁‖ * Real.exp ((X₁ - 24) * (Real.log X₁ + 2)) := by
          have e : m = m * Real.exp (-((X₁ - 24) * (Real.log X₁ + 2))) *
              Real.exp ((X₁ - 24) * (Real.log X₁ + 2)) := by
            rw [mul_assoc, ← Real.exp_add]; simp
          rw [e]; gcongr
      _ ≤ Real.exp ((T + c₀) * (Real.log (T + c₀) + 2)) * ‖G₁‖ := by rw [mul_comm]; gcongr
  -- the exponent identity
  have hB : a ^ 2 / (4 * τ) + a * L.re + τ * L.re ^ 2 = B := by
    simp only [a, lineShift, B, L]
    field_simp
    ring
  -- assemble
  set η := (12 + |X₁ - T| + V) / T
  set ηb := (12 + c₀ + V) / T
  have hηη : η ≤ ηb := by
    apply div_le_div_of_nonneg_right _ hT0.le; linarith
  set P := (T + c₀) * (Real.log (T + c₀) + 2)
  have hP0 : 0 ≤ P := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + c₀); positivity
  have hEexp : Real.exp (-(V ^ 2 / (8 * τ))) ≤ Real.exp (-(V ^ 2 / (8 * τ)) + P) :=
    Real.exp_le_exp.mpr (by linarith)
  refine hE.trans ?_
  rw [hN]
  have hfac : cτ * Real.exp (a ^ 2 / (4 * τ)) =
      K * (Real.exp (-(a * L.re) - τ * (L.re ^ 2 - (Real.pi / 4) ^ 2)) *
        Real.exp (-(τ * (Real.pi / 4) ^ 2))) := by
    simp only [K]
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add, ← hB]
    congr 2
    ring
  rw [hfac]
  set Ez := Real.exp (-(a * L.re) - τ * (L.re ^ 2 - (Real.pi / 4) ^ 2))
  have hEz : 0 < Ez := Real.exp_pos _
  have hsmall : Real.exp (-(τ * (Real.pi / 4) ^ 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have : 0 ≤ τ * (Real.pi / 4) ^ 2 := by positivity
    linarith)
  -- reduce to the bracket
  have hbracket : K * (3 * ‖G₁‖ * η * K₁ + Real.exp (-(V ^ 2 / (8 * τ))) * (M₂ * K₂ + 3 * ‖G₁‖ * K₃))
      ≤ ε * ‖G₁‖ := by
    have hA : K * (3 * ‖G₁‖ * η * K₁) ≤ ‖G₁‖ * (ε / 2) := by
      calc K * (3 * ‖G₁‖ * η * K₁) = ‖G₁‖ * (K * 3 * K₁ * η) := by ring
        _ ≤ ‖G₁‖ * (K * 3 * K₁ * ηb) := by gcongr
        _ ≤ ‖G₁‖ * (ε / 2) := by gcongr
    have hB2 : K * (Real.exp (-(V ^ 2 / (8 * τ))) * (M₂ * K₂ + 3 * ‖G₁‖ * K₃)) ≤
        ‖G₁‖ * (ε / 2) := by
      have hM : M₂ * K₂ ≤ ‖G₁‖ * (M₂ * K₂ * (Real.exp P / m)) := by
        have := mul_le_mul_of_nonneg_left hinvG (by positivity : 0 ≤ M₂ * K₂)
        rw [mul_one_div] at this
        rw [div_le_iff₀ hG₁pos] at this
        linarith
      calc K * (Real.exp (-(V ^ 2 / (8 * τ))) * (M₂ * K₂ + 3 * ‖G₁‖ * K₃))
          ≤ K * (Real.exp (-(V ^ 2 / (8 * τ))) *
              (‖G₁‖ * (M₂ * K₂ * (Real.exp P / m)) + 3 * ‖G₁‖ * K₃)) := by gcongr
        _ = ‖G₁‖ * (K * Real.exp (-(V ^ 2 / (8 * τ))) *
              (M₂ * K₂ * Real.exp P / m + 3 * K₃)) := by ring
        _ ≤ ‖G₁‖ * (K * (M₂ * K₂ / m + 3 * K₃) * Real.exp (-(V ^ 2 / (8 * τ)) + P)) := by
            apply mul_le_mul_of_nonneg_left _ hG₁pos.le
            rw [Real.exp_add]
            have h3' : 3 * K₃ ≤ 3 * K₃ * Real.exp P := le_mul_of_one_le_right (by positivity)
              (Real.one_le_exp hP0)
            have e : M₂ * K₂ * Real.exp P / m = M₂ * K₂ / m * Real.exp P := by ring
            rw [e]
            have hKe : 0 ≤ K * Real.exp (-(V ^ 2 / (8 * τ))) := by positivity
            calc K * Real.exp (-(V ^ 2 / (8 * τ))) * (M₂ * K₂ / m * Real.exp P + 3 * K₃)
                ≤ K * Real.exp (-(V ^ 2 / (8 * τ))) *
                    (M₂ * K₂ / m * Real.exp P + 3 * K₃ * Real.exp P) :=
                  mul_le_mul_of_nonneg_left (by linarith) hKe
              _ = K * (M₂ * K₂ / m + 3 * K₃) * (Real.exp (-(V ^ 2 / (8 * τ))) * Real.exp P) := by
                  ring
        _ ≤ ‖G₁‖ * (ε / 2) := by gcongr
    calc K * (3 * ‖G₁‖ * η * K₁ + Real.exp (-(V ^ 2 / (8 * τ))) * (M₂ * K₂ + 3 * ‖G₁‖ * K₃))
        = K * (3 * ‖G₁‖ * η * K₁) +
          K * (Real.exp (-(V ^ 2 / (8 * τ))) * (M₂ * K₂ + 3 * ‖G₁‖ * K₃)) := by ring
      _ ≤ ‖G₁‖ * (ε / 2) + ‖G₁‖ * (ε / 2) := add_le_add hA hB2
      _ = ε * ‖G₁‖ := by ring
  calc K * (Ez * Real.exp (-(τ * (Real.pi / 4) ^ 2))) *
        (3 * ‖G₁‖ * η * K₁ + Real.exp (-(V ^ 2 / (8 * τ))) * (M₂ * K₂ + 3 * ‖G₁‖ * K₃))
      ≤ Ez * (K * (3 * ‖G₁‖ * η * K₁ +
          Real.exp (-(V ^ 2 / (8 * τ))) * (M₂ * K₂ + 3 * ‖G₁‖ * K₃))) := by
        have hbr0 : 0 ≤ 3 * ‖G₁‖ * η * K₁ +
            Real.exp (-(V ^ 2 / (8 * τ))) * (M₂ * K₂ + 3 * ‖G₁‖ * K₃) := by
          have : 0 ≤ η := by positivity
          positivity
        calc K * (Ez * Real.exp (-(τ * (Real.pi / 4) ^ 2))) * _
            ≤ K * (Ez * 1) * _ := by gcongr
          _ = _ := by ring
    _ ≤ Ez * (ε * ‖G₁‖) := by gcongr
    _ = ε * (‖G₁‖ * Ez) := by ring

/-! ## Newman's conjecture -/

theorem differentiable_discPoint (τ T : ℝ) : Differentiable ℂ (discPoint τ T) := by
  unfold discPoint; fun_prop

theorem differentiable_negHeatS (τ : ℝ) : Differentiable ℂ (negHeatS τ) := by
  unfold negHeatS
  exact (differentiable_riemannHeat_any (-τ)).comp (by fun_prop)

/-- **Every zero of `F_τ` reappears in `H_{−τ}` along a relatively dense set of heights.**  For a
zero `w₀` of the Gaussian-damped series `F_τ` and every `ε > 0`, there is a gap `L` such that every
window `[R, R + L]`, `R ≥ R₀`, contains a height `T` with a zero of `H_{−τ}` within `ε` of the model
point `−i(s_T(w₀) − ½)`, `s_T(w) = w + iT + 2τL_T`.  The heights are almost periods of `F_τ`. -/
theorem exists_riemannHeat_neg_zero_near_model_dense {τ : ℝ} (hτ : 0 < τ) {w₀ : ℂ}
    (hw₀ : gaussDirichlet τ w₀ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ L R₀ : ℝ, 0 < L ∧ ∀ R : ℝ, R₀ ≤ R → ∃ T : ℝ, R ≤ T ∧ T ≤ R + L ∧
      ∃ z : ℂ, riemannHeat (-τ) z = 0 ∧ ‖z - -I * (discPoint τ T w₀ - 1 / 2)‖ ≤ ε := by
  have hF := differentiable_gaussDirichlet hτ
  have hp : gaussDirichlet τ ((1 : ℝ) : ℂ) ≠ 0 := by
    intro h
    have := one_lt_gaussDirichlet_ofReal hτ 1
    rw [h, norm_zero] at this
    linarith
  obtain ⟨ρ, δ, hρ, hρε, hδ, hsph⟩ := exists_sphere_lower_of_entire hF hp w₀
    (ε := min ε (1 / 2)) (by positivity)
  have hρ' : ρ ≤ 1 / 2 := hρε.trans (min_le_right _ _)
  obtain ⟨L₀, hL₀, hap⟩ := isStripAlmostPeriodic_gaussDirichlet hτ w₀.re 1 ρ (by linarith)
    (δ / 5) (by positivity)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp
    (eventually_norm_negHeatS_sub_le hτ w₀ hρ hρ' (ε := δ / 5) (by positivity))
  have hτπ : 0 ≤ τ * (Real.pi / 2) := by positivity
  refine ⟨L₀, max T₁ (|w₀.im| + 1), hL₀, fun R hR => ?_⟩
  obtain ⟨T', ⟨hT'R, hT'L⟩, hT'ap⟩ := hap R
  have hT'T₁ : T₁ ≤ T' := (le_max_left _ _).trans (hR.trans hT'R)
  have hT'w : |w₀.im| + 1 ≤ T' := (le_max_right _ _).trans (hR.trans hT'R)
  have happrox := hT₁ T' hT'T₁
  set s : ℂ → ℂ := discPoint τ T'
  set N : ℂ → ℂ := normaliser τ w₀ T'
  have hsre : ∀ w, (s w + lineShift τ w₀ T').re = 2 + w.re - w₀.re := fun w => by
    rw [discPoint_add_lineShift]; simp
  have hsim : ∀ w, (s w + lineShift τ w₀ T').im = w.im + T' + τ * (Real.pi / 2) := fun w => by
    rw [discPoint_add_lineShift]; simp
  have hball_re : ∀ w ∈ closedBall w₀ ρ, |w.re - w₀.re| ≤ ρ := fun w hw => by
    have := (Complex.abs_re_le_norm (w - w₀)).trans (mem_closedBall_iff_norm.mp hw)
    simpa using this
  have hball_im : ∀ w ∈ closedBall w₀ ρ, |w.im - w₀.im| ≤ ρ := fun w hw => by
    have := (Complex.abs_im_le_norm (w - w₀)).trans (mem_closedBall_iff_norm.mp hw)
    simpa using this
  have hNne : ∀ w ∈ closedBall w₀ ρ, N (s w) ≠ 0 := by
    intro w hw
    have hr := hball_re w hw
    have hi := hball_im w hw
    refine mul_ne_zero (archG_ne_zero ?_ ?_) (Complex.exp_ne_zero _)
    · rw [hsre]; have := (abs_le.mp hr).1; linarith
    · intro h
      have := congrArg Complex.im h
      rw [hsim] at this
      simp at this
      have := (abs_le.mp hi).1
      have := neg_abs_le w₀.im
      linarith
  have hNd : DifferentiableOn ℂ (fun w => N (s w)) (closedBall w₀ ρ) := by
    intro w hw
    have hr := hball_re w hw
    have hre : 0 < (s w + lineShift τ w₀ T').re := by
      rw [hsre]; have := (abs_le.mp hr).1; linarith
    have h1 : DifferentiableAt ℂ (fun w => archG (s w + lineShift τ w₀ T')) w :=
      (differentiableAt_archG hre).comp w (f := fun w => s w + (lineShift τ w₀ T' : ℂ))
        (((differentiable_discPoint τ T') w).add_const _)
    exact (h1.mul (differentiableAt_const _)).differentiableWithinAt
  set h : ℂ → ℂ := fun w => negHeatS τ (s w) / N (s w)
  have hhd : DifferentiableOn ℂ h (closedBall w₀ ρ) := by
    refine DifferentiableOn.div ?_ hNd hNne
    exact ((differentiable_negHeatS τ).comp (differentiable_discPoint τ T')).differentiableOn
  have herr : ∀ w ∈ closedBall w₀ ρ, ‖h w - gaussDirichlet τ (w + T' * I)‖ ≤ δ / 5 := by
    intro w hw
    have hN0 : 0 < ‖N (s w)‖ := norm_pos_iff.mpr (hNne w hw)
    have hsplit : h w - gaussDirichlet τ (w + T' * I) =
        (negHeatS τ (s w) - N (s w) * gaussDirichlet τ (w + T' * I)) / N (s w) := by
      simp only [h]
      field_simp [hNne w hw]
    rw [hsplit, norm_div, div_le_iff₀ hN0]
    exact happrox w hw
  have hap' : ∀ w ∈ closedBall w₀ ρ,
      ‖gaussDirichlet τ (w + T' * I) - gaussDirichlet τ w‖ ≤ δ / 5 :=
    fun w hw => hT'ap w (hball_re w hw)
  have hsphere : ∀ w ∈ sphere w₀ ρ, ‖h w₀‖ < ‖h w‖ := by
    intro w hw
    have hwc : w ∈ closedBall w₀ ρ := sphere_subset_closedBall hw
    have hc : w₀ ∈ closedBall w₀ ρ := mem_closedBall_self hρ.le
    have h1 := herr w hwc
    have h2 := hap' w hwc
    have h3 := hsph w hw
    have h4 := herr w₀ hc
    have h5 := hap' w₀ hc
    rw [hw₀, sub_zero] at h5
    have hc_bound : ‖h w₀‖ ≤ 2 * δ / 5 := by
      have := norm_sub_le (h w₀ - gaussDirichlet τ (w₀ + T' * I))
        (-gaussDirichlet τ (w₀ + T' * I))
      rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at this
      linarith
    have hw_bound : 3 * δ / 5 ≤ ‖h w‖ := by
      have e : gaussDirichlet τ w = (gaussDirichlet τ w - gaussDirichlet τ (w + T' * I)) +
          (gaussDirichlet τ (w + T' * I) - h w) + h w := by ring
      have := norm_add₃_le (a := gaussDirichlet τ w - gaussDirichlet τ (w + T' * I))
        (b := gaussDirichlet τ (w + T' * I) - h w) (c := h w)
      rw [← e] at this
      have r1 := norm_sub_rev (gaussDirichlet τ w) (gaussDirichlet τ (w + T' * I))
      have r2 := norm_sub_rev (gaussDirichlet τ (w + T' * I)) (h w)
      linarith
    linarith
  obtain ⟨wz, hwz, hzero⟩ := exists_zero_of_norm_lt_sphere_on hρ hhd hsphere
  have hwzc : wz ∈ closedBall w₀ ρ := ball_subset_closedBall hwz
  have hA : negHeatS τ (s wz) = 0 := by
    rcases div_eq_zero_iff.mp hzero with h0 | h0
    · exact h0
    · exact absurd h0 (hNne wz hwzc)
  refine ⟨T', hT'R, hT'L, -I * (s wz - 1 / 2), hA, ?_⟩
  have e : -I * (s wz - 1 / 2) - -I * (discPoint τ T' w₀ - 1 / 2) = -I * (wz - w₀) := by
    simp only [s, discPoint]; ring
  rw [e, norm_mul, norm_neg, Complex.norm_I, one_mul]
  exact (le_of_lt (mem_ball_iff_norm.mp hwz)).trans (hρε.trans (min_le_left _ _))

/-- **Every zero of `F_τ` reappears in `H_{−τ}` at arbitrarily large heights.**  For a zero `w₀`
of the Gaussian-damped series `F_τ` and every `ε > 0`, there are heights `T ≥ R` with a zero of
`H_{−τ}` within `ε` of the model point `−i(s_T(w₀) − ½)`, where `s_T(w) = w + iT + 2τL_T`. -/
theorem exists_riemannHeat_neg_zero_near_model {τ : ℝ} (hτ : 0 < τ) {w₀ : ℂ}
    (hw₀ : gaussDirichlet τ w₀ = 0) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ T : ℝ, R ≤ T ∧ ∃ z : ℂ, riemannHeat (-τ) z = 0 ∧
      ‖z - -I * (discPoint τ T w₀ - 1 / 2)‖ ≤ ε := by
  obtain ⟨L, R₀, -, h⟩ := exists_riemannHeat_neg_zero_near_model_dense hτ hw₀ hε
  obtain ⟨T, hT, -, hz⟩ := h (max R R₀) (le_max_right _ _)
  exact ⟨T, (le_max_left _ _).trans hT, hz⟩

/-- **Non-real zeros at logarithmic depth.** For every `τ > 0` there is `C` such that `H_{−τ}` has
zeros `z` of arbitrarily large real part with `τ log(Re z) ≤ −Im z + C`: the model point of a zero
`w₀` of `F_τ` has imaginary part `½ − Re w₀ − τ log(T/2π)`. -/
theorem exists_riemannHeat_neg_zero_deep {τ : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, ∀ R : ℝ, ∃ z : ℂ, riemannHeat (-τ) z = 0 ∧ R ≤ z.re ∧
      τ * Real.log z.re ≤ -z.im + C := by
  obtain ⟨w₀, hw₀⟩ := exists_gaussDirichlet_eq_zero hτ
  refine ⟨τ * Real.log 2 + τ * Real.log (2 * Real.pi) + |w₀.re| + 1, fun R => ?_⟩
  have hτπ : 0 ≤ τ * (Real.pi / 2) := by positivity
  obtain ⟨T, hT, z, hz, hzm⟩ := exists_riemannHeat_neg_zero_near_model hτ hw₀
    (ε := 1 / 2) (by norm_num) (|R| + |w₀.im| + τ * (Real.pi / 2) + 1)
  have hTpos : 0 < T := by linarith [abs_nonneg R, abs_nonneg w₀.im]
  -- the model point sits at height `≈ T` and depth `Re w₀ + τ log(T/2π) − ½`
  have hre_m : (-I * (discPoint τ T w₀ - 1 / 2)).re = w₀.im + T + τ * (Real.pi / 2) := by
    simp [discPoint, horizontalSlope, Complex.mul_re]; ring
  have him_m : -(-I * (discPoint τ T w₀ - 1 / 2)).im =
      w₀.re + τ * Real.log (T / (2 * Real.pi)) - 1 / 2 := by
    have e : (-I * (discPoint τ T w₀ - 1 / 2)).im = -((discPoint τ T w₀).re - 1 / 2) := by
      simp [Complex.mul_im]
    have hsre : (discPoint τ T w₀).re = w₀.re + 2 * τ * (horizontalSlope T).re := by
      simp [discPoint]
    rw [e, hsre, horizontalSlope_re]; ring
  have hre := abs_le.mp ((Complex.abs_re_le_norm _).trans hzm)
  have him := abs_le.mp ((Complex.abs_im_le_norm _).trans hzm)
  rw [Complex.sub_re, hre_m] at hre
  rw [Complex.sub_im] at him
  have hRz : R ≤ z.re := by linarith [le_abs_self R, neg_abs_le w₀.im, hre.1]
  refine ⟨z, hz, hRz, ?_⟩
  have hzhi : z.re ≤ 2 * T := by linarith [le_abs_self w₀.im, abs_nonneg R, hre.2]
  have hlog1 : Real.log z.re ≤ Real.log 2 + Real.log T := by
    rw [← Real.log_mul (by norm_num) hTpos.ne']
    exact Real.log_le_log (by linarith [abs_nonneg R, neg_abs_le w₀.im, hre.1]) hzhi
  have hlog2 : Real.log (T / (2 * Real.pi)) = Real.log T - Real.log (2 * Real.pi) :=
    Real.log_div hTpos.ne' (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hlog1 hτ.le
  rw [mul_add] at hmul
  have hsub := mul_sub τ (Real.log T) (Real.log (2 * Real.pi))
  rw [hlog2] at him_m
  linarith [neg_abs_le w₀.re, him.2]

/-- **Non-real zeros far out.** For every `τ > 0` and `R`, `H_{−τ}` has a zero `z` with
`Im z < 0` and `Re z ≥ R`. -/
theorem exists_riemannHeat_neg_zero_im_neg {τ : ℝ} (hτ : 0 < τ) (R : ℝ) :
    ∃ z : ℂ, riemannHeat (-τ) z = 0 ∧ z.im < 0 ∧ R ≤ z.re := by
  obtain ⟨C, hC⟩ := exists_riemannHeat_neg_zero_deep hτ
  obtain ⟨z, hz, hR, hlog⟩ := hC (max R (Real.exp ((C + 1) / τ)))
  refine ⟨z, hz, ?_, (le_max_left _ _).trans hR⟩
  have h1 : (C + 1) / τ ≤ Real.log z.re := by
    rw [← Real.log_exp ((C + 1) / τ)]
    exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hR)
  rw [div_le_iff₀ hτ] at h1
  linarith [mul_comm τ (Real.log z.re)]

/-- **Newman's conjecture (zeros).** For every `τ > 0`, `H_{−τ}` has infinitely many non-real
zeros. -/
theorem riemannHeat_neg_nonreal_zeros_infinite {τ : ℝ} (hτ : 0 < τ) :
    {z : ℂ | riemannHeat (-τ) z = 0 ∧ z.im ≠ 0}.Infinite := by
  intro hfin
  obtain ⟨R, hR⟩ := (hfin.image Complex.re).bddAbove
  obtain ⟨z, hz, him, hre⟩ := exists_riemannHeat_neg_zero_im_neg hτ (R + 1)
  have := hR ⟨z, ⟨hz, him.ne⟩, rfl⟩
  linarith

/-- **Newman's conjecture.** At every negative heat time `t < 0`, `H_t` has a non-real zero; hence
`newmanConstant ≥ 0` is the de Bruijn–Newman constant on the whole real line, and RH holds iff it
vanishes. -/
theorem not_real_rooted_of_neg {t : ℝ} (ht : t < 0) :
    ∃ z : ℂ, riemannHeat t z = 0 ∧ z.im ≠ 0 := by
  obtain ⟨z, hz, him, -⟩ := exists_riemannHeat_neg_zero_im_neg (τ := -t) (by linarith) 0
  rw [neg_neg] at hz
  exact ⟨z, hz, him.ne⟩

end

end RHTower.DeBruijn
