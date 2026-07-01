/-
# Ray peeling — boundary jumps of `cpow` across the negative cut

Components for the multi-ray binomial-singularity independence closing Hurwitz Lemma 1
(route in `Hurwitz/STATUS.md`): an analytic identity `Σ_t (1−tu)^σ·P_t(u) ≡ 0` off the real
cuts kills every `P_t`, ray by ray, via the boundary JUMP across the outermost cut — the
one-sided limits of `z^σ` onto the negative axis differ by the factor
`e^{iπσ}` vs `e^{−iπσ}`, distinct for `σ ∉ ℤ`, while all inner-ray terms are continuous
across that piece of the cut.  This file provides the analytic bricks:

* `tendsto_log_cut_upper` / `tendsto_log_cut_lower` — one-sided boundary values of `log`;
* `tendsto_cpow_cut_upper` / `tendsto_cpow_cut_lower` — `(x ± iy)^σ → (−x)^σ·e^{±iπσ}`, `x < 0`;
* `jump_factor_ne` — `e^{iπσ} ≠ e^{−iπσ}` for `σ ∉ ℤ`.
-/
import GaloisForLFunctions.Hurwitz.HurwitzZeta

open Complex Filter Topology

namespace HurwitzRayPeeling

/-- The vertical approach path tends to its base point. -/
theorem tendsto_base {x : ℝ} :
    Tendsto (fun y : ℝ => (x : ℂ) + y * Complex.I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
  have hc : Continuous (fun y : ℝ => (x : ℂ) + y * Complex.I) := by fun_prop
  have := hc.tendsto 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
  exact this.mono_left nhdsWithin_le_nhds

/-- The norm along the vertical approach tends to `−x` for `x < 0`. -/
theorem tendsto_norm_base {x : ℝ} (hx : x < 0) :
    Tendsto (fun y : ℝ => ‖(x : ℂ) + y * Complex.I‖) (𝓝[>] 0) (𝓝 (-x)) := by
  have h := (continuous_norm.tendsto ((x : ℂ))).comp tendsto_base
  have h4 : ‖(x : ℂ)‖ = -x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx]
  rwa [h4] at h

/-- The complex log of `x + iy` tends to `log(−x) + iπ` as `y ↓ 0`, for `x < 0`. -/
theorem tendsto_log_cut_upper {x : ℝ} (hx : x < 0) :
    Tendsto (fun y : ℝ => Complex.log ((x : ℂ) + y * Complex.I)) (𝓝[>] 0)
      (𝓝 (((Real.log (-x) : ℝ) : ℂ) + Real.pi * Complex.I)) := by
  have hnorm : Tendsto (fun y : ℝ => Real.log ‖(x : ℂ) + y * Complex.I‖) (𝓝[>] 0)
      (𝓝 (Real.log (-x))) :=
    ((Real.continuousAt_log (by linarith)).tendsto).comp (tendsto_norm_base hx)
  have harg : Tendsto (fun y : ℝ => Complex.arg ((x : ℂ) + y * Complex.I)) (𝓝[>] 0)
      (𝓝 Real.pi) := by
    have hratio : Tendsto (fun y : ℝ => y / ‖(x : ℂ) + y * Complex.I‖) (𝓝[>] 0) (𝓝 0) := by
      have hy0 : Tendsto (fun y : ℝ => y) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have := hy0.div (tendsto_norm_base hx) (by linarith : (-x : ℝ) ≠ 0)
      simpa using this
    have hratio_neg : Tendsto (fun y : ℝ => -y / ‖(x : ℂ) + y * Complex.I‖) (𝓝[>] 0)
        (𝓝 0) := by
      have := hratio.neg
      rw [neg_zero] at this
      refine this.congr fun y => ?_
      rw [neg_div]
    have harcsin := (Real.continuous_arcsin.tendsto 0).comp hratio_neg
    rw [Real.arcsin_zero] at harcsin
    have hlim := harcsin.add_const Real.pi
    rw [zero_add] at hlim
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [Complex.arg_of_re_neg_of_im_nonneg (by simpa using hx) (by simpa using hy.le)]
    have him : (-((x : ℂ) + y * Complex.I)).im = -y := by simp
    rw [him]
    rfl
  have h1 : Tendsto (fun y : ℝ => ((Real.log ‖(x : ℂ) + y * Complex.I‖ : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((Real.log (-x) : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp hnorm
  have h2 : Tendsto (fun y : ℝ => ((Complex.arg ((x : ℂ) + y * Complex.I) : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((Real.pi : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp harg
  have hsum := h1.add (h2.mul_const Complex.I)
  refine hsum.congr' ?_
  filter_upwards with y
  rfl

/-- The complex log of `x − iy` tends to `log(−x) − iπ` as `y ↓ 0`, for `x < 0`. -/
theorem tendsto_log_cut_lower {x : ℝ} (hx : x < 0) :
    Tendsto (fun y : ℝ => Complex.log ((x : ℂ) - y * Complex.I)) (𝓝[>] 0)
      (𝓝 (((Real.log (-x) : ℝ) : ℂ) - Real.pi * Complex.I)) := by
  have hconj : ∀ y : ℝ, (x : ℂ) - y * Complex.I = (starRingEnd ℂ) ((x : ℂ) + y * Complex.I) := by
    intro y
    simp [Complex.ext_iff]
  have hlogconj : ∀ y : ℝ, 0 < y →
      Complex.log ((x : ℂ) - y * Complex.I)
        = (starRingEnd ℂ) (Complex.log ((x : ℂ) + y * Complex.I)) := by
    intro y hy
    have harg : ((x : ℂ) + y * Complex.I).arg ≠ Real.pi := by
      rw [Ne, Complex.arg_eq_pi_iff]
      push Not
      intro _
      have : ((x : ℂ) + y * Complex.I).im = y := by simp
      rw [this]
      linarith
    rw [hconj y]
    exact Complex.log_conj _ harg
  have hup := tendsto_log_cut_upper hx
  have hcc := (continuous_conj.tendsto _).comp hup
  have hval : (starRingEnd ℂ) (((Real.log (-x) : ℝ) : ℂ) + Real.pi * Complex.I)
      = ((Real.log (-x) : ℝ) : ℂ) - Real.pi * Complex.I := by
    rw [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I]
    have : (starRingEnd ℂ) ((Real.pi : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) := Complex.conj_ofReal _
    rw [this]
    ring
  rw [hval] at hcc
  refine hcc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hlogconj y hy).symm

/-- **Upper boundary value of `z^σ` on the negative cut**: `(x+iy)^σ → (−x)^σ·e^{iπσ}` as
`y ↓ 0`, for `x < 0`. -/
theorem tendsto_cpow_cut_upper {x : ℝ} (hx : x < 0) (σ : ℂ) :
    Tendsto (fun y : ℝ => ((x : ℂ) + y * Complex.I) ^ σ) (𝓝[>] 0)
      (𝓝 ((((-x : ℝ) : ℂ)) ^ σ * Complex.exp (Real.pi * Complex.I * σ))) := by
  have hne : ∀ y : ℝ, ((x : ℂ) + y * Complex.I) ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hnex : ((-x : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hlim := (Complex.continuous_exp.tendsto _).comp
    ((tendsto_log_cut_upper hx).const_mul σ)
  have hval : Complex.exp (σ * (((Real.log (-x) : ℝ) : ℂ) + Real.pi * Complex.I))
      = (((-x : ℝ) : ℂ)) ^ σ * Complex.exp (Real.pi * Complex.I * σ) := by
    calc Complex.exp (σ * (((Real.log (-x) : ℝ) : ℂ) + Real.pi * Complex.I))
        = Complex.exp (Complex.log ((-x : ℝ) : ℂ) * σ)
            * Complex.exp (Real.pi * Complex.I * σ) := by
          rw [← Complex.exp_add, ← Complex.ofReal_log (by linarith : (0:ℝ) ≤ -x)]
          congr 1
          ring
      _ = (((-x : ℝ) : ℂ)) ^ σ * Complex.exp (Real.pi * Complex.I * σ) := by
          rw [Complex.cpow_def_of_ne_zero hnex]
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards with y
  simp only [Function.comp_apply]
  rw [Complex.cpow_def_of_ne_zero (hne y)]
  congr 1
  ring

/-- **Lower boundary value of `z^σ` on the negative cut**: `(x−iy)^σ → (−x)^σ·e^{−iπσ}` as
`y ↓ 0`, for `x < 0`. -/
theorem tendsto_cpow_cut_lower {x : ℝ} (hx : x < 0) (σ : ℂ) :
    Tendsto (fun y : ℝ => ((x : ℂ) - y * Complex.I) ^ σ) (𝓝[>] 0)
      (𝓝 ((((-x : ℝ) : ℂ)) ^ σ * Complex.exp (-(Real.pi * Complex.I * σ)))) := by
  have hne : ∀ y : ℝ, ((x : ℂ) - y * Complex.I) ≠ 0 := by
    intro y h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hnex : ((-x : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    linarith
  have hlim := (Complex.continuous_exp.tendsto _).comp
    ((tendsto_log_cut_lower hx).const_mul σ)
  have hval : Complex.exp (σ * (((Real.log (-x) : ℝ) : ℂ) - Real.pi * Complex.I))
      = (((-x : ℝ) : ℂ)) ^ σ * Complex.exp (-(Real.pi * Complex.I * σ)) := by
    calc Complex.exp (σ * (((Real.log (-x) : ℝ) : ℂ) - Real.pi * Complex.I))
        = Complex.exp (Complex.log ((-x : ℝ) : ℂ) * σ)
            * Complex.exp (-(Real.pi * Complex.I * σ)) := by
          rw [← Complex.exp_add, ← Complex.ofReal_log (by linarith : (0:ℝ) ≤ -x)]
          congr 1
          ring
      _ = (((-x : ℝ) : ℂ)) ^ σ * Complex.exp (-(Real.pi * Complex.I * σ)) := by
          rw [Complex.cpow_def_of_ne_zero hnex]
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards with y
  simp only [Function.comp_apply]
  rw [Complex.cpow_def_of_ne_zero (hne y)]
  congr 1
  ring

/-- **The cut jump factor is nonzero off the integers**: `e^{iπσ} ≠ e^{−iπσ}` for `σ ∉ ℤ`. -/
theorem jump_factor_ne (σ : ℂ) (hσ : ∀ k : ℤ, σ ≠ (k : ℂ)) :
    Complex.exp (Real.pi * Complex.I * σ) ≠ Complex.exp (-(Real.pi * Complex.I * σ)) := by
  intro h
  have h2 : Complex.exp (2 * (Real.pi * Complex.I * σ)) = 1 := by
    rw [two_mul, Complex.exp_add]
    nth_rewrite 2 [h]
    rw [← Complex.exp_add,
      show Real.pi * Complex.I * σ + -(Real.pi * Complex.I * σ) = 0 from by ring,
      Complex.exp_zero]
  rw [Complex.exp_eq_one_iff] at h2
  obtain ⟨k, hk⟩ := h2
  apply hσ k
  have hfac : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  have hrearr : (2 * (Real.pi : ℂ) * Complex.I) * σ
      = (2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) := by
    linear_combination hk
  exact mul_left_cancel₀ hfac hrearr

end HurwitzRayPeeling
