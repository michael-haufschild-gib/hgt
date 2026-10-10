import Mathlib

/-!
# Reciprocal positivity puts the minimum modulus on the positive axis

Let `h` be an entire function with no zeros in the disk `‖z‖ < d`, and suppose every Taylor
coefficient of `1/h` at `0` is a nonnegative real number.  Then on every circle `‖z‖ = ρ < d` the
modulus `‖h‖` is smallest at the positive real point (`norm_apply_norm_le_of_inv_taylor_nonneg`):

  `‖h ρ‖ ≤ ‖h z‖`.

Indeed `1/h(z) = Σ c_n z^n` with `c_n ≥ 0` on the disk, so `‖1/h(z)‖ ≤ Σ c_n ‖z‖^n = 1/h(‖z‖)`.  By
continuity the inequality persists on the boundary circle `‖z‖ = d`.  In particular, if `h` vanishes
somewhere on `‖z‖ = d`, then it vanishes at the positive point `d`
(`apply_eq_zero_of_inv_taylor_nonneg`).  This is the Pringsheim mechanism in its minimum-modulus
form, with no analytic continuation argument.
-/

open Complex Filter Topology Set
open scoped ComplexOrder Nat

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Nonnegative Taylor coefficients bound the modulus by the positive axis.**  If `g` is
holomorphic on `‖z‖ < d` and all its Taylor coefficients at `0` are nonnegative reals, then
`‖g z‖ ≤ ‖g ‖z‖‖` on the disk. -/
theorem norm_le_norm_apply_norm_of_taylor_nonneg {g : ℂ → ℂ} {d : ℝ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 d)) (hpos : ∀ n, 0 ≤ iteratedDeriv n g 0)
    {z : ℂ} (hz : ‖z‖ < d) : ‖g z‖ ≤ ‖g (‖z‖ : ℂ)‖ := by
  have hz' : z ∈ Metric.ball (0 : ℂ) d := by simpa using hz
  have hr' : ((‖z‖ : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) d := by
    simpa [Complex.norm_real, abs_of_nonneg (norm_nonneg z)] using hz
  have h1 := Complex.hasSum_taylorSeries_on_ball hg hz'
  have h2 := Complex.hasSum_taylorSeries_on_ball hg hr'
  simp only [sub_zero, smul_eq_mul] at h1 h2
  set T : ℕ → ℝ := fun n => ‖((n ! : ℂ))⁻¹ * (z ^ n * iteratedDeriv n g 0)‖ with hT
  have hTeq : ∀ n, ((n ! : ℂ))⁻¹ * ((((‖z‖ : ℝ) : ℂ)) ^ n * iteratedDeriv n g 0) = ((T n : ℝ) : ℂ) := by
    intro n
    have hD := hpos n
    have hDre : iteratedDeriv n g 0 = (((iteratedDeriv n g 0).re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [(Complex.nonneg_iff.mp hD).2.symm]
    have hDnn : 0 ≤ (iteratedDeriv n g 0).re := (Complex.nonneg_iff.mp hD).1
    rw [hT]
    simp only
    rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast, hDre, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hDnn]
    push_cast
    ring
  have h2' : HasSum (fun n => ((T n : ℝ) : ℂ)) (g (‖z‖ : ℂ)) := by
    simpa only [hTeq] using h2
  have h2re : HasSum T (g (‖z‖ : ℂ)).re := by
    have := h2'.mapL Complex.reCLM
    simpa using this
  calc ‖g z‖ = ‖∑' n, ((n ! : ℂ))⁻¹ * (z ^ n * iteratedDeriv n g 0)‖ := by rw [h1.tsum_eq]
    _ ≤ ∑' n, T n := norm_tsum_le_tsum_norm h2re.summable
    _ = (g (‖z‖ : ℂ)).re := h2re.tsum_eq
    _ ≤ ‖g (‖z‖ : ℂ)‖ := Complex.re_le_norm _

/-- **Reciprocal positivity: the minimum modulus on each circle sits on the positive axis.**  If
`h` is entire, zero-free on `‖z‖ < d`, and `1/h` has nonnegative Taylor coefficients at `0`, then
`‖h ‖z‖‖ ≤ ‖h z‖` for `‖z‖ < d`. -/
theorem norm_apply_norm_le_of_inv_taylor_nonneg {h : ℂ → ℂ} (hh : Differentiable ℂ h) {d : ℝ}
    (hne : ∀ z : ℂ, ‖z‖ < d → h z ≠ 0)
    (hpos : ∀ n, 0 ≤ iteratedDeriv n (fun z => (h z)⁻¹) 0) {z : ℂ} (hz : ‖z‖ < d) :
    ‖h (‖z‖ : ℂ)‖ ≤ ‖h z‖ := by
  have hg : DifferentiableOn ℂ (fun z => (h z)⁻¹) (Metric.ball 0 d) :=
    hh.differentiableOn.inv fun w hw => hne w (by simpa using hw)
  have hle := norm_le_norm_apply_norm_of_taylor_nonneg hg hpos hz
  have hz0 : h z ≠ 0 := hne z hz
  have hr0 : h (‖z‖ : ℂ) ≠ 0 := hne _ (by
    simpa [Complex.norm_real, abs_of_nonneg (norm_nonneg z)] using hz)
  simp only [norm_inv] at hle
  have hp1 : 0 < ‖h z‖ := norm_pos_iff.mpr hz0
  have hp2 : 0 < ‖h (‖z‖ : ℂ)‖ := norm_pos_iff.mpr hr0
  exact (inv_le_inv₀ hp1 hp2).mp hle

/-- **A boundary zero forces a zero at the positive point.**  If `h` is entire, zero-free on
`‖z‖ < d`, `1/h` has nonnegative Taylor coefficients at `0`, and `h w = 0` with `‖w‖ = d > 0`,
then `h d = 0`. -/
theorem apply_eq_zero_of_inv_taylor_nonneg {h : ℂ → ℂ} (hh : Differentiable ℂ h) {d : ℝ}
    (hd : 0 < d) (hne : ∀ z : ℂ, ‖z‖ < d → h z ≠ 0)
    (hpos : ∀ n, 0 ≤ iteratedDeriv n (fun z => (h z)⁻¹) 0) {w : ℂ} (hw : ‖w‖ = d)
    (hw0 : h w = 0) : h (d : ℂ) = 0 := by
  have hineq : ∀ r ∈ Ioo (0 : ℝ) 1, ‖h ((r * d : ℝ) : ℂ)‖ ≤ ‖h ((r : ℂ) * w)‖ := by
    intro r hr
    have hnorm : ‖(r : ℂ) * w‖ = r * d := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.1, hw]
    have hlt : ‖(r : ℂ) * w‖ < d := by
      rw [hnorm]
      nlinarith [hr.2]
    have := norm_apply_norm_le_of_inv_taylor_nonneg hh hne hpos hlt
    rwa [hnorm] at this
  have hhc : Continuous h := hh.continuous
  have hcont1 : Tendsto (fun r : ℝ => ‖h ((r * d : ℝ) : ℂ)‖) (𝓝[<] 1) (𝓝 ‖h (d : ℂ)‖) := by
    have hc : Continuous fun r : ℝ => ‖h ((r * d : ℝ) : ℂ)‖ :=
      (hhc.comp (Complex.continuous_ofReal.comp (continuous_id.mul continuous_const))).norm
    have := hc.tendsto 1
    simp only [one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hcont2 : Tendsto (fun r : ℝ => ‖h ((r : ℂ) * w)‖) (𝓝[<] 1) (𝓝 ‖h w‖) := by
    have hc : Continuous fun r : ℝ => ‖h ((r : ℂ) * w)‖ :=
      (hhc.comp (Complex.continuous_ofReal.mul continuous_const)).norm
    have := hc.tendsto 1
    simp only [Complex.ofReal_one, one_mul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), ‖h ((r * d : ℝ) : ℂ)‖ ≤ ‖h ((r : ℂ) * w)‖ :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)) fun r hr => hineq r hr
  have hle := le_of_tendsto_of_tendsto hcont1 hcont2 hev
  rw [hw0, norm_zero] at hle
  exact norm_le_zero_iff.mp hle

end

end GaloisForLFunctions.HTGeometry
