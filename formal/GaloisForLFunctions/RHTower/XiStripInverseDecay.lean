import GaloisForLFunctions.RHTower.HedenmalmThetaSourceSpectrumExact
import GaloisForLFunctions.RHTower.CausalThetaHalfLaplace
import GaloisForLFunctions.RHTower.ThetaCuspComplexStrip

/-!
# Inverse-linear decay of `Ξ` on horizontal strips

One integration by parts in the Fourier–Laplace representation `Ξ(w) = ∫ e^{-iwx} k(x) dx` of the
theta source gives `‖w Ξ(w)‖ ≤ M_B` whenever `|Im w| ≤ B`, for every `B`. Hence `Ξ(u + iv) → 0` as
`|u| → ∞`, uniformly on every bounded horizontal strip.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- **Inverse-linear decay on every horizontal strip.** For each `B` there is `M` with
`‖w Ξ(w)‖ ≤ M` whenever `|Im w| ≤ B`: integrate `Ξ(w) = ∫ e^{-iwx} k(x) dx` by parts once. -/
theorem exists_norm_mul_XiC_le (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, |w.im| ≤ B → ‖w * XiC w‖ ≤ M := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_deriv_thetaCuspFullSource_le (B + 1)
  have hE := integrable_exp_neg_abs_line
  refine ⟨C * ∫ x : ℝ, Real.exp (-|x|), mul_nonneg hC0 (integral_nonneg fun _ => (Real.exp_pos _).le),
    fun w hw => ?_⟩
  set u : ℝ → ℂ := fun x => cexp (-I * w * x)
  set u' : ℝ → ℂ := fun x => (-I * w) * cexp (-I * w * x)
  set v : ℝ → ℂ := fun x => (thetaCuspFullSource x : ℂ)
  set v' : ℝ → ℂ := fun x => ((deriv thetaCuspFullSource x : ℝ) : ℂ)
  have hu : ∀ x, HasDerivAt u (u' x) x := fun x => by
    have h := ((hasDerivAt_id (x : ℂ)).const_mul (-I * w)).cexp.comp_ofReal
    simpa [u, u', mul_comm, mul_left_comm, mul_assoc] using h
  have hv : ∀ x, HasDerivAt v (v' x) x := fun x =>
    (differentiable_thetaCuspFullSource x).hasDerivAt.ofReal_comp
  have hnu : ∀ x : ℝ, ‖u x‖ ≤ Real.exp (B * |x|) := fun x => by
    simp only [u, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have : (-I * w * (x : ℂ)).re = w.im * x := by simp
    rw [this]
    calc w.im * x ≤ |w.im * x| := le_abs_self _
      _ = |w.im| * |x| := abs_mul _ _
      _ ≤ B * |x| := mul_le_mul_of_nonneg_right hw (abs_nonneg _)
  have huv : Integrable (u * v) := by
    have h := HedenmalmThetaSource.integrable_thetaCuspFourierLaplaceIntegrand_all w
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp [thetaCuspFourierLaplaceIntegrand, u, v]
  have hu'v : Integrable (u' * v) := by
    refine (huv.const_mul (-I * w)).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply, u, u', v]; ring
  have hbd : ∀ x : ℝ, ‖(u * v') x‖ ≤ C * Real.exp (-|x|) := fun x => by
    simp only [Pi.mul_apply, norm_mul, v', Complex.norm_real, Real.norm_eq_abs]
    calc ‖u x‖ * |deriv thetaCuspFullSource x| ≤ Real.exp (B * |x|) *
          (C * Real.exp (-((B + 1) * |x|))) :=
          mul_le_mul (hnu x) (hC x) (abs_nonneg _) (Real.exp_pos _).le
      _ = C * Real.exp (-|x|) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have huv' : Integrable (u * v') := by
    refine (hE.const_mul C).mono' ?_ (Eventually.of_forall hbd)
    exact (by have := continuous_deriv_thetaCuspFullSource; fun_prop :
      Continuous (u * v')).aestronglyMeasurable
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hu x) (fun x _ => hv x)
    huv' hu'v huv
  have hXi : ∫ x, u x * v x = XiC w := by
    rw [← HedenmalmThetaSource.thetaCuspFourierLaplace_eq_XiC_all, thetaCuspFourierLaplace]
    rfl
  have hkey : ∫ x, u x * v' x = I * w * XiC w := by
    rw [hibp, ← hXi, ← integral_const_mul, ← integral_neg]
    congr 1; ext x; simp only [u', u, v]; ring
  have hnorm : ‖w * XiC w‖ = ‖∫ x, u x * v' x‖ := by
    rw [hkey, mul_assoc, norm_mul (I : ℂ), Complex.norm_I, one_mul]
  rw [hnorm, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono huv'.norm (hE.const_mul C) hbd)

theorem exists_norm_XiC_mul_abs_re_le (B : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, |w.im| ≤ B → ‖XiC w‖ * |w.re| ≤ M := by
  obtain ⟨M, hM, h⟩ := exists_norm_mul_XiC_le B
  refine ⟨M, hM, fun w hw => ?_⟩
  calc ‖XiC w‖ * |w.re| ≤ ‖XiC w‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm w) (norm_nonneg _)
    _ = ‖w * XiC w‖ := by rw [norm_mul, mul_comm]
    _ ≤ M := h w hw

/-- **(4).** `Ξ(u + iv) → 0` as `|u| → ∞`, uniformly for `|v| ≤ B`, on every bounded strip. -/
theorem exists_forall_norm_XiC_lt (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : ℝ, ∀ w : ℂ, |w.im| ≤ B → U ≤ |w.re| → ‖XiC w‖ < ε := by
  obtain ⟨M, hM, h⟩ := exists_norm_XiC_mul_abs_re_le B
  refine ⟨M / ε + 1, fun w hw hU => ?_⟩
  have hpos : 0 < |w.re| := lt_of_lt_of_le (by positivity) hU
  have h1 := h w hw
  have h2 : M < ε * |w.re| := by
    have h3 : M / ε < |w.re| := by linarith
    rwa [div_lt_iff₀ hε, mul_comm] at h3
  by_contra hc
  push Not at hc
  have : ε * |w.re| ≤ ‖XiC w‖ * |w.re| := mul_le_mul_of_nonneg_right hc hpos.le
  linarith

/-- **(4)**, uniform form. -/
theorem tendstoUniformlyOn_XiC_strip (B : ℝ) :
    TendstoUniformlyOn (fun u v : ℝ => XiC ((u : ℂ) + v * I)) (fun _ => 0) (cocompact ℝ)
      (Icc (-B) B) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨U, hU⟩ := exists_forall_norm_XiC_lt B hε
  have hev : ∀ᶠ u : ℝ in cocompact ℝ, U ≤ |u| := by
    have := (tendsto_norm_cocompact_atTop (E := ℝ)).eventually (eventually_ge_atTop U)
    simpa [Real.norm_eq_abs] using this
  filter_upwards [hev] with u hu v hv
  rw [dist_zero_left]
  refine hU _ ?_ ?_
  · simpa [abs_le] using hv
  · simpa using hu

end

end RHTower
