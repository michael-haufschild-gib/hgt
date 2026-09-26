import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Saddle-arc control for Cauchy coefficient integrals

For a function `f` holomorphic and zero-free near a positive real point `R`, the Cauchy integral
for its Taylor coefficients on the circle `|x| = R` is controlled near `θ = 0` by the scaled
logarithmic derivative `F(w) = w f'(w)/f(w)`.  Writing the normalised arc value
`G(θ) = f(Re^{iθ}) e^{−iλθ}/f(R)` with `λ = F(R)`, one has `G' = G · i(F(Re^{iθ}) − λ)`, hence

```
G(θ) = exp ∫₀^θ i (F(Re^{is}) − λ) ds.
```

If `F` is real on the real axis and `|F(w) − F(R)| ≤ M` on a disc of radius `r` about `R`, two Cauchy
estimates bound `F''` by `32M/r²` on the half disc, and a first-order expansion of `F` at `R` gives,
for `0 ≤ θ ≤ r/(2R)` and `F₁ = F'(R)`,

```
|G(θ)| ≤ exp(−F₁R(1−cos θ) + 32MR²θ³/(3r²)),
Re G(θ) ≥ exp(−F₁R(1−cos θ) − 32MR²θ³/(3r²)) · cos(|F₁|Rθ³/6 + 32MR²θ³/(3r²)).
```

The first is the Gaussian decay of the integrand away from the saddle; the second is the positivity
of its real part near the saddle, with the phase error cubic in `θ`.
-/

open Complex Real intervalIntegral MeasureTheory Metric

namespace HTGeometry

noncomputable section

/-- Solutions of `G' = G·Q` with `G 0 = 1` and continuous `Q` are `exp ∫₀^θ Q`. -/
theorem eq_exp_integral_of_hasDerivAt_mul {G Q : ℝ → ℂ} (hQ : Continuous Q)
    (hG : ∀ θ, HasDerivAt G (G θ * Q θ) θ) (h0 : G 0 = 1) (θ : ℝ) :
    G θ = Complex.exp (∫ s in (0 : ℝ)..θ, Q s) := by
  set A : ℝ → ℂ := fun θ => ∫ s in (0 : ℝ)..θ, Q s with hAdef
  have hA : ∀ θ, HasDerivAt A (Q θ) θ := fun θ =>
    intervalIntegral.integral_hasDerivAt_right (hQ.intervalIntegrable _ _)
      hQ.aestronglyMeasurable.stronglyMeasurableAtFilter hQ.continuousAt
  set H : ℝ → ℂ := fun θ => G θ * Complex.exp (-A θ) with hHdef
  have hH : ∀ θ, HasDerivAt H 0 θ := by
    intro θ
    have h1 := (hA θ).neg.cexp
    have h2 := (hG θ).mul h1
    exact h2.congr_deriv (by ring)
  have hconst : ∀ θ, H θ = H 0 := fun θ => is_const_of_deriv_eq_zero
    (fun x => (hH x).differentiableAt) (fun x => (hH x).deriv) θ 0
  have hH0 : H 0 = 1 := by simp [hHdef, hAdef, h0]
  have hθ : G θ * Complex.exp (-A θ) = 1 := by
    have := hconst θ; rw [hH0] at this; exact this
  calc G θ = G θ * Complex.exp (-A θ) * Complex.exp (A θ) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp (A θ) := by rw [hθ, one_mul]

/-- `|∫₀^θ u| ≤ β θ³/3` when `|u(s)| ≤ β s²` on `[0, θ]`. -/
theorem abs_integral_le_of_abs_le_mul_sq {u : ℝ → ℝ} {β θ : ℝ} (hθ : 0 ≤ θ)
    (hu : ContinuousOn u (Set.Icc 0 θ))
    (hb : ∀ s ∈ Set.Icc 0 θ, |u s| ≤ β * s ^ 2) :
    |∫ s in (0 : ℝ)..θ, u s| ≤ β * θ ^ 3 / 3 := by
  calc |∫ s in (0 : ℝ)..θ, u s| ≤ ∫ s in (0 : ℝ)..θ, |u s| := abs_integral_le_integral_abs hθ
    _ ≤ ∫ s in (0 : ℝ)..θ, β * s ^ 2 :=
        integral_mono_on hθ (hu.abs.intervalIntegrable_of_Icc hθ)
          ((continuous_const.mul (continuous_pow 2)).intervalIntegrable _ _) hb
    _ = β * θ ^ 3 / 3 := by
        rw [intervalIntegral.integral_const_mul, integral_pow]; ring

/-- **Cauchy estimate relative to a base value.** -/
theorem norm_deriv_le_of_norm_sub_le {F : ℂ → ℂ} {U : Set ℂ} (hF : DifferentiableOn ℂ F U)
    {c w : ℂ} {ρ M : ℝ} (hρ : 0 < ρ) (hball : closedBall w ρ ⊆ U)
    (hM : ∀ z ∈ sphere w ρ, ‖F z - F c‖ ≤ M) : ‖deriv F w‖ ≤ M / ρ := by
  have hd : DiffContOnCl ℂ (fun z => F z - F c) (ball w ρ) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball w hρ.ne']
    exact (hF.mono hball).sub_const _
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hd hM
  rwa [deriv_sub_const] at h

/-- **Second-order Taylor bound on a segment.** -/
theorem norm_sub_sub_deriv_mul_le {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) {c z : ℂ} {K : ℝ} (hseg : segment ℝ c z ⊆ U)
    (hK : ∀ w ∈ segment ℝ c z, ‖deriv (deriv F) w‖ ≤ K) :
    ‖F z - F c - deriv F c * (z - c)‖ ≤ K * ‖z - c‖ ^ 2 := by
  have hF' : DifferentiableOn ℂ (deriv F) U := hF.deriv hU
  have hconv : Convex ℝ (segment ℝ c z) := convex_segment c z
  have hc : c ∈ segment ℝ c z := left_mem_segment ℝ c z
  have hz : z ∈ segment ℝ c z := right_mem_segment ℝ c z
  -- `F'` is `K`-Lipschitz on the segment
  have hlip : ∀ w ∈ segment ℝ c z, ‖deriv F w - deriv F c‖ ≤ K * ‖w - c‖ := fun w hw =>
    hconv.norm_image_sub_le_of_norm_deriv_le
      (fun x hx => (hF'.differentiableAt (hU.mem_nhds (hseg hx)))) hK hc hw
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK c hc)
  have hwz : ∀ w ∈ segment ℝ c z, ‖w - c‖ ≤ ‖z - c‖ := by
    intro w hw
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hw
    have : a • c + b • z - c = b • (z - c) := by
      calc a • c + b • z - c = a • c + b • z - (a + b) • c := by rw [hab, one_smul]
        _ = b • (z - c) := by rw [add_smul, smul_sub]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    have : b ≤ 1 := by linarith
    calc b * ‖z - c‖ ≤ 1 * ‖z - c‖ := by gcongr
      _ = ‖z - c‖ := one_mul _
  set φ : ℂ → ℂ := fun w => F w - deriv F c * w with hφ
  have hφd : ∀ w ∈ segment ℝ c z, HasDerivAt φ (deriv F w - deriv F c) w := by
    intro w hw
    have h1 := (hF.differentiableAt (hU.mem_nhds (hseg hw))).hasDerivAt
    have h2 := (hasDerivAt_id' w).const_mul (deriv F c)
    exact (h1.sub h2).congr_deriv (by ring)
  have hbound : ∀ w ∈ segment ℝ c z, ‖deriv φ w‖ ≤ K * ‖z - c‖ := by
    intro w hw
    rw [(hφd w hw).deriv]
    exact (hlip w hw).trans (by gcongr; exact hwz w hw)
  have := hconv.norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hφd w hw).differentiableAt) hbound hc hz
  have e : φ z - φ c = F z - F c - deriv F c * (z - c) := by simp [hφ]; ring
  rw [e] at this
  calc _ ≤ K * ‖z - c‖ * ‖z - c‖ := this
    _ = K * ‖z - c‖ ^ 2 := by ring

/-- Local version on an open interval around `0`: solutions of `G' = G·Q` with `G 0 = 1` are
`exp ∫₀^θ Q`. -/
theorem eq_exp_integral_of_hasDerivAt_mul_Ioo {G Q : ℝ → ℂ} {a b : ℝ} (ha : a < 0) (hb : 0 < b)
    (hQ : ContinuousOn Q (Set.Ioo a b))
    (hG : ∀ θ ∈ Set.Ioo a b, HasDerivAt G (G θ * Q θ) θ) (h0 : G 0 = 1) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo a b) :
    G θ = Complex.exp (∫ s in (0 : ℝ)..θ, Q s) := by
  have h0mem : (0 : ℝ) ∈ Set.Ioo a b := ⟨ha, hb⟩
  have hsub : ∀ x ∈ Set.Ioo a b, Set.uIcc 0 x ⊆ Set.Ioo a b := fun x hx =>
    (Set.ordConnected_Ioo).uIcc_subset h0mem hx
  set A : ℝ → ℂ := fun θ => ∫ s in (0 : ℝ)..θ, Q s with hAdef
  have hA : ∀ x ∈ Set.Ioo a b, HasDerivAt A (Q x) x := fun x hx =>
    intervalIntegral.integral_hasDerivAt_right ((hQ.mono (hsub x hx)).intervalIntegrable)
      (hQ.stronglyMeasurableAtFilter isOpen_Ioo x hx)
      (hQ.continuousAt (isOpen_Ioo.mem_nhds hx))
  set H : ℝ → ℂ := fun θ => G θ * Complex.exp (-A θ) with hHdef
  have hH : ∀ x ∈ Set.Ioo a b, HasDerivAt H 0 x := by
    intro x hx
    have h1 := (hA x hx).neg.cexp
    have h2 := (hG x hx).mul h1
    exact h2.congr_deriv (by ring)
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun x hx => (hH x hx).differentiableAt.differentiableWithinAt)
    (fun x hx => (hH x hx).deriv) hθ h0mem
  have hH0 : H 0 = 1 := by simp [hHdef, hAdef, h0]
  have hθ' : G θ * Complex.exp (-A θ) = 1 := by
    have := hconst; rw [hH0] at this; exact this
  calc G θ = G θ * Complex.exp (-A θ) * Complex.exp (A θ) := by
        rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Complex.exp (A θ) := by rw [hθ', one_mul]

/-- `‖e^{is} − 1‖ ≤ |s|`. -/
theorem norm_exp_ofReal_mul_I_sub_one_le_abs (s : ℝ) : ‖Complex.exp ((s : ℂ) * I) - 1‖ ≤ |s| := by
  have e : Complex.exp ((s : ℂ) * I) - 1 = ((Real.cos s - 1 : ℝ) : ℂ) + ((Real.sin s : ℝ) : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]; push_cast; ring
  rw [e, Complex.norm_add_mul_I, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  have h1 := Real.one_sub_sq_div_two_le_cos (x := s)
  have h2 := Real.sin_sq_add_cos_sq s
  nlinarith

/-- The derivative along the circle `θ ↦ R e^{iθ}`. -/
theorem hasDerivAt_comp_circle {f : ℂ → ℂ} {R θ : ℝ}
    (hf : DifferentiableAt ℂ f ((R : ℂ) * Complex.exp ((θ : ℂ) * I))) :
    HasDerivAt (fun θ : ℝ => f ((R : ℂ) * Complex.exp ((θ : ℂ) * I)))
      (deriv f ((R : ℂ) * Complex.exp ((θ : ℂ) * I))
        * ((R : ℂ) * Complex.exp ((θ : ℂ) * I) * I)) θ := by
  have hz : HasDerivAt (fun θ : ℝ => (R : ℂ) * Complex.exp ((θ : ℂ) * I))
      ((R : ℂ) * Complex.exp ((θ : ℂ) * I) * I) θ := by
    have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * I) I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const I
    have h2 := (h1.cexp).const_mul (R : ℂ)
    exact h2.congr_deriv (by ring)
  exact hf.hasDerivAt.comp θ hz

/-- The scaled logarithmic derivative `w f'(w)/f(w)`. -/
def scaledLogDeriv (f : ℂ → ℂ) (w : ℂ) : ℂ := w * deriv f w / f w

/-- The normalised integrand of the Cauchy coefficient integral on the circle `|x| = R`, with the
phase `e^{−iλθ}` removed. -/
def saddleArc (f : ℂ → ℂ) (R lam θ : ℝ) : ℂ :=
  f ((R : ℂ) * Complex.exp ((θ : ℂ) * I)) * Complex.exp (-((lam * θ : ℝ) : ℂ) * I) / f (R : ℂ)

theorem re_intervalIntegral {Q : ℝ → ℂ} {a b : ℝ} (h : IntervalIntegrable Q volume a b) :
    (∫ s in a..b, Q s).re = ∫ s in a..b, (Q s).re := by
  have := Complex.reCLM.intervalIntegral_comp_comm h
  simpa using this.symm

theorem im_intervalIntegral {Q : ℝ → ℂ} {a b : ℝ} (h : IntervalIntegrable Q volume a b) :
    (∫ s in a..b, Q s).im = ∫ s in a..b, (Q s).im := by
  have := Complex.imCLM.intervalIntegral_comp_comm h
  simpa using this.symm

/-- **Saddle-arc control.**  Let `f` be holomorphic and zero-free on an open set `U` containing the
closed disc of radius `r` about the positive real point `R`, with `F(w) = w f'(w)/f(w)` real on the
real axis and `|F(w) − F(R)| ≤ M` on that disc.  Put `λ = F(R)`, `F₁ = F'(R)` and
`K = 32M/r²`.  Then for `0 ≤ θ ≤ r/(2R)` the normalised arc value
`G(θ) = f(Re^{iθ}) e^{−iλθ}/f(R)` satisfies

* `|G(θ)| ≤ exp(−F₁R(1−cos θ) + KR²θ³/3)`;
* `Re G(θ) ≥ exp(−F₁R(1−cos θ) − KR²θ³/3) · cos(|F₁|Rθ³/6 + KR²θ³/3)` when the cosine's
  argument is at most `π/2`.

The proof writes `G = exp ∫₀^θ i(F(Re^{is}) − λ) ds`, expands `F` to first order at `R` with the
second derivative controlled by two Cauchy estimates, and integrates. -/
theorem saddleArc_bounds {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hf0 : ∀ w ∈ U, f w ≠ 0) {R r M : ℝ} (hR : 0 < R) (hr : 0 < r)
    (hball : closedBall (R : ℂ) r ⊆ U)
    (hM : ∀ w ∈ closedBall (R : ℂ) r, ‖scaledLogDeriv f w - scaledLogDeriv f R‖ ≤ M)
    (hreal : ∀ x : ℝ, (x : ℂ) ∈ U → (scaledLogDeriv f x).im = 0)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : R * θ ≤ r / 2) :
    ‖saddleArc f R (scaledLogDeriv f R).re θ‖
        ≤ Real.exp (-((deriv (scaledLogDeriv f) R).re * R * (1 - Real.cos θ))
          + 32 * M / r ^ 2 * R ^ 2 * θ ^ 3 / 3)
      ∧ (|(deriv (scaledLogDeriv f) R).re| * R * θ ^ 3 / 6 + 32 * M / r ^ 2 * R ^ 2 * θ ^ 3 / 3
          ≤ Real.pi / 2 →
        Real.exp (-((deriv (scaledLogDeriv f) R).re * R * (1 - Real.cos θ))
          - 32 * M / r ^ 2 * R ^ 2 * θ ^ 3 / 3)
          * Real.cos (|(deriv (scaledLogDeriv f) R).re| * R * θ ^ 3 / 6
            + 32 * M / r ^ 2 * R ^ 2 * θ ^ 3 / 3)
        ≤ (saddleArc f R (scaledLogDeriv f R).re θ).re) := by
  set F := scaledLogDeriv f with hFdef
  set K := 32 * M / r ^ 2 with hK
  have hRmem : (R : ℂ) ∈ U := hball (mem_closedBall_self hr.le)
  have hM0 : 0 ≤ M := by simpa using hM R (mem_closedBall_self hr.le)
  -- regularity of `F`
  have hFd : DifferentiableOn ℂ F U := by
    have := (differentiableOn_id.mul (hf.deriv hU)).div hf hf0
    exact this
  have hF'd : DifferentiableOn ℂ (deriv F) U := hFd.deriv hU
  -- first Cauchy estimate on the disc of radius `3r/4`
  have hD1 : ∀ v ∈ closedBall (R : ℂ) (3 * r / 4), ‖deriv F v‖ ≤ 4 * M / r := by
    intro v hv
    have hsub : closedBall v (r / 4) ⊆ closedBall (R : ℂ) r := by
      intro z hz
      rw [mem_closedBall] at hz hv ⊢
      linarith [dist_triangle z v (R : ℂ)]
    have := norm_deriv_le_of_norm_sub_le hFd (c := (R : ℂ)) (by positivity : (0 : ℝ) < r / 4)
      (hsub.trans hball) (fun z hz => hM z (hsub (sphere_subset_closedBall hz)))
    calc ‖deriv F v‖ ≤ M / (r / 4) := this
      _ = 4 * M / r := by field_simp
  -- second Cauchy estimate on the disc of radius `r/2`
  have hD2 : ∀ w ∈ closedBall (R : ℂ) (r / 2), ‖deriv (deriv F) w‖ ≤ K := by
    intro w hw
    have hsub : closedBall w (r / 4) ⊆ closedBall (R : ℂ) (3 * r / 4) := by
      intro z hz
      rw [mem_closedBall] at hz hw ⊢
      linarith [dist_triangle z w (R : ℂ)]
    have hwmem : w ∈ closedBall (R : ℂ) (3 * r / 4) := by
      rw [mem_closedBall] at hw ⊢; linarith
    have hsub' : closedBall (R : ℂ) (3 * r / 4) ⊆ U :=
      (closedBall_subset_closedBall (by linarith)).trans hball
    have := norm_deriv_le_of_norm_sub_le hF'd (c := w) (M := 8 * M / r)
      (by positivity : (0 : ℝ) < r / 4) (hsub.trans hsub')
      (fun z hz => by
        have h1 := hD1 z (hsub (sphere_subset_closedBall hz))
        have h2 := hD1 w hwmem
        calc ‖deriv F z - deriv F w‖ ≤ ‖deriv F z‖ + ‖deriv F w‖ := norm_sub_le _ _
          _ ≤ 4 * M / r + 4 * M / r := add_le_add h1 h2
          _ = 8 * M / r := by ring)
    calc ‖deriv (deriv F) w‖ ≤ 8 * M / r / (r / 4) := this
      _ = K := by rw [hK]; field_simp; ring
  -- `F` is real at `R`, and so is `F'(R)`
  have hFR : (F (R : ℂ)).im = 0 := hreal R hRmem
  have hF1 : (deriv F (R : ℂ)).im = 0 := by
    have hd : HasDerivAt F (deriv F (R : ℂ)) (R : ℂ) :=
      (hFd.differentiableAt (hU.mem_nhds hRmem)).hasDerivAt
    have h2 : HasDerivAt (fun y : ℝ => (F (y : ℂ)).im) (deriv F (R : ℂ)).im R := by
      have := (hd.const_mul (-I)).real_of_complex
      have e : (fun x : ℝ => (-I * F (x : ℂ)).re) = fun x : ℝ => (F (x : ℂ)).im := by
        funext x; simp
      rw [e] at this
      exact this.congr_deriv (by simp)
    have hev : (fun y : ℝ => (F (y : ℂ)).im) =ᶠ[nhds R] fun _ => (0 : ℝ) := by
      have hopen : IsOpen ((fun y : ℝ => (y : ℂ)) ⁻¹' U) := hU.preimage Complex.continuous_ofReal
      filter_upwards [hopen.mem_nhds (show R ∈ (fun y : ℝ => (y : ℂ)) ⁻¹' U from hRmem)] with y hy
      exact hreal y hy
    have h3 : HasDerivAt (fun y : ℝ => (F (y : ℂ)).im) 0 R :=
      (hasDerivAt_const R (0 : ℝ)).congr_of_eventuallyEq hev
    exact h2.unique h3
  set F₁ := (deriv F (R : ℂ)).re with hF₁
  set lam := (F (R : ℂ)).re with hlam
  have hFRc : F (R : ℂ) = (lam : ℂ) := by
    apply Complex.ext <;> simp [hlam, hFR]
  have hF1c : deriv F (R : ℂ) = (F₁ : ℂ) := by
    apply Complex.ext <;> simp [hF₁, hF1]
  have hF1abs : |F₁| ≤ M / r := by
    have := norm_deriv_le_of_norm_sub_le hFd (c := (R : ℂ)) hr hball
      (fun z hz => hM z (sphere_subset_closedBall hz))
    rw [hF1c, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  -- the arc
  set z : ℝ → ℂ := fun s => (R : ℂ) * Complex.exp ((s : ℂ) * I) with hz
  have hzR : ∀ s : ℝ, ‖z s - R‖ ≤ R * |s| := by
    intro s
    have : z s - R = (R : ℂ) * (Complex.exp ((s : ℂ) * I) - 1) := by simp [hz]; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    exact mul_le_mul_of_nonneg_left (norm_exp_ofReal_mul_I_sub_one_le_abs s) hR.le
  have hzU : ∀ s ∈ Set.Ioo (-(r / R)) (r / R), z s ∈ U := by
    intro s hs
    apply hball
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hzR s
    have h2 : |s| < r / R := abs_lt.mpr hs
    have h3 : R * |s| < r := by rwa [lt_div_iff₀ hR, mul_comm] at h2
    linarith
  -- the ODE for the normalised arc value
  set Q : ℝ → ℂ := fun s => I * (F (z s) - lam) with hQ
  have hθ2 : θ < r / R := by
    rw [lt_div_iff₀ hR]; nlinarith
  have hQc : ContinuousOn Q (Set.Ioo (-(r / R)) (r / R)) := by
    have hzc : Continuous z := by
      simp only [hz]; fun_prop
    have : ContinuousOn (fun s => F (z s)) (Set.Ioo (-(r / R)) (r / R)) :=
      hFd.continuousOn.comp hzc.continuousOn (fun s hs => hzU s hs)
    exact continuousOn_const.mul (this.sub continuousOn_const)
  have hGd : ∀ s ∈ Set.Ioo (-(r / R)) (r / R),
      HasDerivAt (saddleArc f R lam) (saddleArc f R lam s * Q s) s := by
    intro s hs
    have hzs := hzU s hs
    have hfd : DifferentiableAt ℂ f (z s) := hf.differentiableAt (hU.mem_nhds hzs)
    have h1 := hasDerivAt_comp_circle (R := R) (θ := s) hfd
    have hE : HasDerivAt (fun s : ℝ => Complex.exp (-((lam * s : ℝ) : ℂ) * I))
        (Complex.exp (-((lam * s : ℝ) : ℂ) * I) * (-(lam : ℂ) * I)) s := by
      have h2 : HasDerivAt (fun s : ℝ => -((lam * s : ℝ) : ℂ) * I) (-(lam : ℂ) * I) s := by
        have h3 : HasDerivAt (fun s : ℝ => ((lam * s : ℝ) : ℂ)) (lam : ℂ) s := by
          have := ((hasDerivAt_id s).const_mul lam).ofReal_comp
          simpa using this
        exact (h3.neg.mul_const I)
      exact h2.cexp
    have h4 := (h1.mul hE).div_const (f (R : ℂ))
    have hfz : f (z s) ≠ 0 := hf0 _ hzs
    have hfR : f (R : ℂ) ≠ 0 := hf0 _ hRmem
    refine h4.congr_deriv ?_
    have hfz' : f ((R : ℂ) * Complex.exp ((s : ℂ) * I)) ≠ 0 := hfz
    simp only [saddleArc, hQ, hFdef, scaledLogDeriv, hz]
    field_simp
    ring
  have hG0 : saddleArc f R lam 0 = 1 := by
    have hfR : f (R : ℂ) ≠ 0 := hf0 _ hRmem
    simp [saddleArc, hfR]
  have hrep := eq_exp_integral_of_hasDerivAt_mul_Ioo (a := -(r / R)) (b := r / R)
    (by have : 0 < r / R := div_pos hr hR; linarith) (div_pos hr hR) hQc hGd hG0
    (θ := θ) ⟨by have : 0 < r / R := div_pos hr hR; linarith, hθ2⟩
  -- Taylor control of `F` along the arc
  have hTay : ∀ s ∈ Set.Icc 0 θ,
      ‖F (z s) - lam - (F₁ : ℂ) * (z s - R)‖ ≤ K * R ^ 2 * s ^ 2 := by
    intro s hs
    have hsR : ‖z s - R‖ ≤ R * s := by
      have := hzR s; rwa [abs_of_nonneg hs.1] at this
    have hRs : R * s ≤ r / 2 := le_trans (by nlinarith [hs.2]) hθ
    have hseg : segment ℝ (R : ℂ) (z s) ⊆ closedBall (R : ℂ) (r / 2) := by
      apply (convex_closedBall (R : ℂ) (r / 2)).segment_subset
      · exact mem_closedBall_self (by linarith)
      · rw [mem_closedBall, dist_eq_norm]; linarith
    have hsub : closedBall (R : ℂ) (r / 2) ⊆ U :=
      (closedBall_subset_closedBall (by linarith)).trans hball
    have := norm_sub_sub_deriv_mul_le hU hFd (hseg.trans hsub) (fun w hw => hD2 w (hseg hw))
    rw [hFRc, hF1c] at this
    calc _ ≤ K * ‖z s - R‖ ^ 2 := this
      _ ≤ K * (R * s) ^ 2 := by
        have hK0 : 0 ≤ K := by rw [hK]; positivity
        gcongr
      _ = K * R ^ 2 * s ^ 2 := by ring
  -- real and imaginary parts of the exponent
  have hIcc : Set.Icc 0 θ ⊆ Set.Ioo (-(r / R)) (r / R) := by
    intro s hs
    have : 0 < r / R := div_pos hr hR
    exact ⟨by linarith [hs.1], lt_of_le_of_lt hs.2 hθ2⟩
  set D : ℝ → ℂ := fun s => F (z s) - lam with hD
  have hDc : ContinuousOn D (Set.Icc 0 θ) := by
    have hzc : Continuous z := by simp only [hz]; fun_prop
    have : ContinuousOn (fun s => F (z s)) (Set.Icc 0 θ) :=
      hFd.continuousOn.comp hzc.continuousOn (fun s hs => hzU s (hIcc hs))
    exact this.sub continuousOn_const
  have hzre : ∀ s : ℝ, (z s - R).re = R * (Real.cos s - 1) := by
    intro s
    simp only [hz, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
    ring
  have hzim : ∀ s : ℝ, (z s - R).im = R * Real.sin s := by
    intro s
    simp only [hz, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, add_zero, sub_zero]
  have hzre' : ∀ s : ℝ, (z s).re = R * Real.cos s := by
    intro s; simp [hz, Complex.exp_ofReal_mul_I_re]
  have hzim' : ∀ s : ℝ, (z s).im = R * Real.sin s := by
    intro s; simp [hz, Complex.exp_ofReal_mul_I_im]
  set u₁ : ℝ → ℝ := fun s => (D s).re - F₁ * R * (Real.cos s - 1) with hu₁
  set u₂ : ℝ → ℝ := fun s => (D s).im - F₁ * R * Real.sin s with hu₂
  have hu₁b : ∀ s ∈ Set.Icc 0 θ, |u₁ s| ≤ K * R ^ 2 * s ^ 2 := by
    intro s hs
    have h := hTay s hs
    have e : u₁ s = (F (z s) - lam - (F₁ : ℂ) * (z s - R)).re := by
      simp only [hu₁, hD, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      rw [hzre']; ring
    rw [e]; exact (Complex.abs_re_le_norm _).trans h
  have hu₂b : ∀ s ∈ Set.Icc 0 θ, |u₂ s| ≤ K * R ^ 2 * s ^ 2 := by
    intro s hs
    have h := hTay s hs
    have e : u₂ s = (F (z s) - lam - (F₁ : ℂ) * (z s - R)).im := by
      simp only [hu₂, hD, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, add_zero, Complex.ofReal_im, sub_zero]
      rw [hzim']; ring
    rw [e]; exact (Complex.abs_im_le_norm _).trans h
  have hu₁c : ContinuousOn u₁ (Set.Icc 0 θ) :=
    (Complex.continuous_re.comp_continuousOn hDc).sub (by fun_prop)
  have hu₂c : ContinuousOn u₂ (Set.Icc 0 θ) :=
    (Complex.continuous_im.comp_continuousOn hDc).sub (by fun_prop)
  have hI₁ := abs_integral_le_of_abs_le_mul_sq hθ0 hu₁c hu₁b
  have hI₂ := abs_integral_le_of_abs_le_mul_sq hθ0 hu₂c hu₂b
  have hQint : IntervalIntegrable Q volume 0 θ :=
    (hQc.mono (by rw [Set.uIcc_of_le hθ0]; exact hIcc)).intervalIntegrable
  have hu₁int : IntervalIntegrable u₁ volume 0 θ := hu₁c.intervalIntegrable_of_Icc hθ0
  have hu₂int : IntervalIntegrable u₂ volume 0 θ := hu₂c.intervalIntegrable_of_Icc hθ0
  have hcosint : IntervalIntegrable (fun s : ℝ => F₁ * R * (Real.cos s - 1)) volume 0 θ :=
    (by fun_prop : Continuous fun s : ℝ => F₁ * R * (Real.cos s - 1)).intervalIntegrable _ _
  have hsinint : IntervalIntegrable (fun s : ℝ => F₁ * R * Real.sin s) volume 0 θ :=
    (by fun_prop : Continuous fun s : ℝ => F₁ * R * Real.sin s).intervalIntegrable _ _
  have hAim : (∫ s in (0 : ℝ)..θ, Q s).im
      = F₁ * R * (Real.sin θ - θ) + ∫ s in (0 : ℝ)..θ, u₁ s := by
    rw [im_intervalIntegral hQint]
    have e : (fun s => (Q s).im) = fun s => F₁ * R * (Real.cos s - 1) + u₁ s := by
      funext s; simp [hQ, hu₁, hD]
    rw [e, intervalIntegral.integral_add hcosint hu₁int, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub (Real.continuous_cos.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _), integral_cos, intervalIntegral.integral_const]
    simp
  have hAre : (∫ s in (0 : ℝ)..θ, Q s).re
      = -(F₁ * R * (1 - Real.cos θ)) - ∫ s in (0 : ℝ)..θ, u₂ s := by
    rw [re_intervalIntegral hQint]
    have e : (fun s => (Q s).re) = fun s => -(F₁ * R * Real.sin s + u₂ s) := by
      funext s; simp [hQ, hu₂, hD]
    rw [e, intervalIntegral.integral_neg, intervalIntegral.integral_add hsinint hu₂int,
      intervalIntegral.integral_const_mul, integral_sin]
    simp
    ring
  set A := ∫ s in (0 : ℝ)..θ, Q s
  have hsinθ : θ - Real.sin θ ≤ θ ^ 3 / 6 := by
    rcases hθ0.lt_or_eq with h | h
    · have := Real.sin_gt_sub_cube h; linarith
    · rw [← h]; simp
  have hsinθ' : 0 ≤ θ - Real.sin θ := by have := Real.sin_le hθ0; linarith
  have hImA : |A.im| ≤ |F₁| * R * θ ^ 3 / 6 + K * R ^ 2 * θ ^ 3 / 3 := by
    rw [hAim]
    calc |F₁ * R * (Real.sin θ - θ) + ∫ s in (0 : ℝ)..θ, u₁ s|
        ≤ |F₁ * R * (Real.sin θ - θ)| + |∫ s in (0 : ℝ)..θ, u₁ s| := abs_add_le _ _
      _ ≤ |F₁| * R * (θ ^ 3 / 6) + K * R ^ 2 * θ ^ 3 / 3 := by
        gcongr
        rw [abs_mul, abs_mul, abs_of_pos hR, abs_sub_comm, abs_of_nonneg hsinθ']
        gcongr
      _ = |F₁| * R * θ ^ 3 / 6 + K * R ^ 2 * θ ^ 3 / 3 := by ring
  have hReA₁ : A.re ≤ -(F₁ * R * (1 - Real.cos θ)) + K * R ^ 2 * θ ^ 3 / 3 := by
    rw [hAre]; have := (abs_le.mp hI₂).1; linarith
  have hReA₂ : -(F₁ * R * (1 - Real.cos θ)) - K * R ^ 2 * θ ^ 3 / 3 ≤ A.re := by
    rw [hAre]; have := (abs_le.mp hI₂).2; linarith
  rw [hrep]
  refine ⟨?_, fun hπ => ?_⟩
  · rw [Complex.norm_exp]
    have e : -(F₁ * R * (1 - Real.cos θ)) = -((deriv (scaledLogDeriv f) R).re * R
        * (1 - Real.cos θ)) := rfl
    exact Real.exp_le_exp.mpr (by linarith)
  · rw [Complex.exp_re]
    have hb0 : 0 ≤ |F₁| * R * θ ^ 3 / 6 + K * R ^ 2 * θ ^ 3 / 3 := by
      have : 0 ≤ K := by rw [hK]; positivity
      positivity
    have hcos : Real.cos (|F₁| * R * θ ^ 3 / 6 + K * R ^ 2 * θ ^ 3 / 3) ≤ Real.cos A.im := by
      rw [← Real.cos_abs A.im]
      apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
      exact hImA
    have hcos0 : 0 ≤ Real.cos (|F₁| * R * θ ^ 3 / 6 + K * R ^ 2 * θ ^ 3 / 3) :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hπ⟩
    calc Real.exp (-(F₁ * R * (1 - Real.cos θ)) - K * R ^ 2 * θ ^ 3 / 3)
          * Real.cos (|F₁| * R * θ ^ 3 / 6 + K * R ^ 2 * θ ^ 3 / 3)
        ≤ Real.exp A.re * Real.cos (|F₁| * R * θ ^ 3 / 6 + K * R ^ 2 * θ ^ 3 / 3) := by
          gcongr
      _ ≤ Real.exp A.re * Real.cos A.im := by gcongr

end

end HTGeometry
