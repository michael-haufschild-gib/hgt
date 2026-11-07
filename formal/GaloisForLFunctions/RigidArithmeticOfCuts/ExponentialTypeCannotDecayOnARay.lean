import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Exponential type cannot decay on a ray

An even entire function of exponential type that decays faster than every exponential on the positive real axis vanishes
identically.

The argument is Phragmén–Lindelöf on quadrants. Multiplying by `e^{K z + i C z}` bounds the function on both sides of the first
quadrant, so the decay passes to the ray at angle `π/4`, with every rate `K`. Applying this twice moves the decay to the imaginary axis. Then
the function is bounded on all four quadrants, hence constant by Liouville, hence zero.

This is the analytic core of the coefficient boundary for rotated relations: a coefficient of size `exp(C √|w|)` cannot be small on a
ray where `Q(ϑ w)/Q(w)` is small.
-/

open Complex Filter Topology Asymptotics Set
open scoped ComplexOrder

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

variable {g : ℂ → ℂ} {C : ℝ}

/-- An entire function bounded on the sides of the first quadrant, of exponential type, is bounded on the quadrant. -/
private lemma norm_le_of_quadrant (hg : Differentiable ℂ g) {A B : ℝ}
    (hgrowth : ∀ z, ‖g z‖ ≤ A * Real.exp (B * ‖z‖)) {M : ℝ}
    (hre : ∀ x : ℝ, 0 ≤ x → ‖g x‖ ≤ M) (him : ∀ x : ℝ, 0 ≤ x → ‖g (x * I)‖ ≤ M) {z : ℂ}
    (hz1 : 0 ≤ z.re) (hz2 : 0 ≤ z.im) : ‖g z‖ ≤ M := by
  refine PhragmenLindelof.quadrant_I hg.diffContOnCl ?_ hre him hz1 hz2
  refine ⟨1, by norm_num, B, ?_⟩
  refine IsBigO.of_bound A (Eventually.of_forall fun w => ?_)
  rw [Real.rpow_one, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hgrowth w

/-- Decay on the positive real axis at every rate, for a function of exponential type. -/
def DecaysOnRay (g : ℂ → ℂ) : Prop :=
  ∀ K : ℝ, ∃ M : ℝ, ∀ r : ℝ, 0 ≤ r → ‖g r‖ ≤ M * Real.exp (-(K * r))

/-- **The decay rotates by `π/4`.** -/
theorem DecaysOnRay.rotate (hg : Differentiable ℂ g) (hC : 0 ≤ C)
    (hgrowth : ∀ z, ‖g z‖ ≤ C * Real.exp (C * ‖z‖)) (hdec : DecaysOnRay g) :
    DecaysOnRay fun z => g (z * ((1 + I) / (Real.sqrt 2 : ℂ))) := by
  intro K
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set K₁ : ℝ := max 0 (Real.sqrt 2 * K + C) with hK₁
  have hK₁0 : 0 ≤ K₁ := le_max_left _ _
  obtain ⟨M₀, hM₀⟩ := hdec K₁
  set M : ℝ := max (max M₀ C) 0 with hMdef
  set F : ℂ → ℂ := fun z => g z * Complex.exp ((K₁ : ℂ) * z + I * (C : ℂ) * z) with hF
  have hFd : Differentiable ℂ F := hg.mul (by fun_prop)
  have hexp : ∀ z : ℂ, ‖Complex.exp ((K₁ : ℂ) * z + I * (C : ℂ) * z)‖ = Real.exp (K₁ * z.re - C * z.im) := by
    intro z
    rw [Complex.norm_exp]
    congr 1
    simp
    ring
  have hgrowthF : ∀ z, ‖F z‖ ≤ C * Real.exp ((C + K₁ + C) * ‖z‖) := by
    intro z
    rw [hF, norm_mul, hexp]
    have hre := Complex.abs_re_le_norm z
    have him := Complex.abs_im_le_norm z
    have h1 : K₁ * z.re - C * z.im ≤ (K₁ + C) * ‖z‖ := by
      have h2 : K₁ * z.re ≤ K₁ * ‖z‖ := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hre) hK₁0
      have h3 : -(C * z.im) ≤ C * ‖z‖ := by
        have := mul_le_mul_of_nonneg_left ((neg_le_abs z.im).trans him) hC
        linarith
      linarith
    calc ‖g z‖ * Real.exp (K₁ * z.re - C * z.im)
        ≤ (C * Real.exp (C * ‖z‖)) * Real.exp ((K₁ + C) * ‖z‖) :=
          mul_le_mul (hgrowth z) (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le (by positivity)
      _ = _ := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
  have hboundre : ∀ x : ℝ, 0 ≤ x → ‖F x‖ ≤ M := by
    intro x hx
    rw [hF]
    simp only
    rw [norm_mul, hexp]
    simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have h1 := hM₀ x hx
    have h2 : M₀ * Real.exp (-(K₁ * x)) * Real.exp (K₁ * x) = M₀ := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (K₁ * x)).le
    rw [h2] at h3
    exact h3.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hboundim : ∀ x : ℝ, 0 ≤ x → ‖F (x * I)‖ ≤ M := by
    intro x hx
    rw [hF]
    simp only
    rw [norm_mul, hexp]
    have hre : ((x : ℂ) * I).re = 0 := by simp
    have him : ((x : ℂ) * I).im = x := by simp
    have hnorm : ‖(x : ℂ) * I‖ = x := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hx]
    rw [hre, him]
    have h1 := hgrowth ((x : ℂ) * I)
    rw [hnorm] at h1
    have h2 : C * Real.exp (C * x) * Real.exp (K₁ * 0 - C * x) = C := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (K₁ * 0 - C * x)).le
    rw [h2] at h3
    exact h3.trans ((le_max_right _ _).trans (le_max_left _ _))
  refine ⟨M, fun r hr => ?_⟩
  set z : ℂ := (r : ℂ) * ((1 + I) / (Real.sqrt 2 : ℂ)) with hz
  have hs2C : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs2.ne'
  have hzval : z = ((r / Real.sqrt 2 : ℝ) : ℂ) + ((r / Real.sqrt 2 : ℝ) : ℂ) * I := by
    rw [hz]
    push_cast
    field_simp
  have hzre : z.re = r / Real.sqrt 2 := by
    rw [hzval]
    simp
  have hzim : z.im = r / Real.sqrt 2 := by
    rw [hzval]
    simp
  have hq : 0 ≤ r / Real.sqrt 2 := by positivity
  have hbound := norm_le_of_quadrant hFd hgrowthF hboundre hboundim
    (by rw [hzre]; exact hq) (by rw [hzim]; exact hq)
  rw [hF] at hbound
  simp only at hbound
  rw [norm_mul, hexp, hzre, hzim] at hbound
  have hexpo : K₁ * (r / Real.sqrt 2) - C * (r / Real.sqrt 2) = (K₁ - C) * (r / Real.sqrt 2) := by ring
  rw [hexpo] at hbound
  have hK : K * r ≤ (K₁ - C) * (r / Real.sqrt 2) := by
    have h1 : Real.sqrt 2 * K + C ≤ K₁ := le_max_right _ _
    have h2 : Real.sqrt 2 * K ≤ K₁ - C := by linarith
    have h3 : K * r = (Real.sqrt 2 * K) * (r / Real.sqrt 2) := by
      field_simp
    rw [h3]
    exact mul_le_mul_of_nonneg_right h2 hq
  have hM0 : 0 ≤ M := le_max_right _ _
  have hfinal : ‖g z‖ * Real.exp ((K₁ - C) * (r / Real.sqrt 2)) ≤ M := hbound
  have hpos := Real.exp_pos ((K₁ - C) * (r / Real.sqrt 2))
  have hle : ‖g z‖ ≤ M * Real.exp (-((K₁ - C) * (r / Real.sqrt 2))) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
    exact hfinal
  exact hle.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hM0)

/-- **Exponential type cannot decay on a ray.** An even entire function of exponential type, decaying at every exponential
rate on the positive real axis, vanishes identically. -/
theorem eq_zero_of_decaysOnRay (hg : Differentiable ℂ g) (hC : 0 ≤ C)
    (hgrowth : ∀ z, ‖g z‖ ≤ C * Real.exp (C * ‖z‖)) (heven : ∀ z, g (-z) = g z) (hdec : DecaysOnRay g) :
    g = 0 := by
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2C : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hs2.ne'
  have hsq : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    have := Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    exact_mod_cast this
  set ω : ℂ := (1 + I) / (Real.sqrt 2 : ℂ) with hω
  have hωsq : ω * ω = I := by
    rw [hω, div_mul_div_comm, hsq]
    have hI : I * I = -1 := Complex.I_mul_I
    field_simp
    linear_combination hI
  have hωnorm : ‖ω‖ = 1 := by
    have h1 : ‖ω‖ * ‖ω‖ = 1 := by
      rw [← norm_mul, hωsq, Complex.norm_I]
    nlinarith [norm_nonneg ω, sq_nonneg (‖ω‖ - 1), sq_nonneg (‖ω‖ + 1)]
  -- Rotation by `ω` preserves the type.
  have hstep : ∀ h : ℂ → ℂ, Differentiable ℂ h → (∀ z, ‖h z‖ ≤ C * Real.exp (C * ‖z‖)) →
      Differentiable ℂ (fun z => h (z * ω)) ∧ ∀ z, ‖h (z * ω)‖ ≤ C * Real.exp (C * ‖z‖) := by
    intro h hd hb
    refine ⟨hd.comp (differentiable_id.mul_const ω), fun z => ?_⟩
    have := hb (z * ω)
    rwa [norm_mul, hωnorm, mul_one] at this
  obtain ⟨hg1d, hg1b⟩ := hstep g hg hgrowth
  have hdec1 : DecaysOnRay fun z => g (z * ω) := hdec.rotate hg hC hgrowth
  have hdec2 : DecaysOnRay fun z => (fun w => g (w * ω)) (z * ω) := hdec1.rotate hg1d hC hg1b
  have hdecI : ∀ K : ℝ, ∃ M : ℝ, ∀ r : ℝ, 0 ≤ r → ‖g ((r : ℂ) * I)‖ ≤ M * Real.exp (-(K * r)) := by
    intro K
    obtain ⟨M, hM⟩ := hdec2 K
    refine ⟨M, fun r hr => ?_⟩
    have h1 := hM r hr
    simp only at h1
    rwa [mul_assoc, hωsq] at h1
  -- Boundedness on the sides of the quadrants.
  obtain ⟨M₁, hM₁⟩ := hdec 0
  obtain ⟨M₂, hM₂⟩ := hdecI 0
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one] at hM₁ hM₂
  have hbound1 : ∀ z : ℂ, 0 ≤ z.re → 0 ≤ z.im → ‖g z‖ ≤ max M₁ M₂ := fun z h1 h2 =>
    norm_le_of_quadrant hg hgrowth (fun x hx => (hM₁ x hx).trans (le_max_left _ _))
      (fun x hx => (hM₂ x hx).trans (le_max_right _ _)) h1 h2
  -- The second quadrant is the first rotated by `i`.
  have hgId : Differentiable ℂ fun z => g (z * I) := hg.comp (differentiable_id.mul_const I)
  have hgIb : ∀ z, ‖g (z * I)‖ ≤ C * Real.exp (C * ‖z‖) := fun z => by
    have := hgrowth (z * I)
    rwa [norm_mul, Complex.norm_I, mul_one] at this
  have hbound2 : ∀ z : ℂ, 0 ≤ z.re → 0 ≤ z.im → ‖g (z * I)‖ ≤ max M₁ M₂ := fun z h1 h2 => by
    refine norm_le_of_quadrant hgId hgIb (fun x hx => (hM₂ x hx).trans (le_max_right _ _)) (fun x hx => ?_) h1 h2
    have hval : (x : ℂ) * I * I = -(x : ℂ) := by
      rw [mul_assoc, Complex.I_mul_I]
      ring
    rw [hval, heven]
    exact (hM₁ x hx).trans (le_max_left _ _)
  have hbounded : ∀ z : ℂ, ‖g z‖ ≤ max M₁ M₂ := by
    intro z
    rcases le_total 0 z.re with h1 | h1 <;> rcases le_total 0 z.im with h2 | h2
    · exact hbound1 z h1 h2
    · -- `z = w I` with `w = −z I`: `Re w = Im z ≤ 0`, so use `−w`.
      have hw : g z = g ((I * z) * I) := by
        have : (I * z) * I = -z := by
          rw [mul_comm I z, mul_assoc, Complex.I_mul_I]
          ring
        rw [this, heven]
      rw [hw]
      refine hbound2 _ ?_ ?_
      · simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul]
        linarith
      · simp only [Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul]
        linarith
    · have hw : g z = g ((-(I * z)) * I) := by
        have : (-(I * z)) * I = z := by
          rw [neg_mul, mul_comm I z, mul_assoc, Complex.I_mul_I]
          ring
        rw [this]
      rw [hw]
      refine hbound2 _ ?_ ?_
      · simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul]
        linarith
      · simp only [Complex.neg_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul]
        linarith
    · rw [← heven]
      exact hbound1 (-z) (by simpa using h1) (by simpa using h2)
  -- Liouville, and the decay at infinity.
  have hconst : ∀ z w, g z = g w := fun z w =>
    hg.apply_eq_apply_of_bounded (isBounded_iff_forall_norm_le.mpr ⟨max M₁ M₂, by
      rintro _ ⟨u, rfl⟩
      exact hbounded u⟩) z w
  funext z
  obtain ⟨M, hM⟩ := hdec 1
  have hlim : Tendsto (fun r : ℝ => M * Real.exp (-(1 * r))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun r : ℝ => Real.exp (-(1 * r))) atTop (𝓝 0) := by
      simp only [one_mul]
      exact Real.tendsto_exp_neg_atTop_nhds_zero
    simpa using h1.const_mul M
  have hle : ∀ᶠ r : ℝ in atTop, ‖g z‖ ≤ M * Real.exp (-(1 * r)) := by
    filter_upwards [eventually_ge_atTop 0] with r hr
    rw [hconst z r]
    exact hM r hr
  have h0 : ‖g z‖ ≤ 0 := ge_of_tendsto hlim hle
  simpa using h0

end GaloisForLFunctions.RigidArithmeticOfCuts
