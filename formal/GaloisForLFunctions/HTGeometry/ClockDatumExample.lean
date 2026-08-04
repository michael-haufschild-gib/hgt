import GaloisForLFunctions.HTGeometry.ClockThreeDimensionalDetermination

/-!
# A potential of the coupled class

The theorems of the previous files are stated for potentials carrying a clock datum. This file
exhibits one, so that they are not vacuous:

`V(ξ, η, z) = sin ξ · cos η · cos z`.

It is holomorphic in the transverse variable, bounded on every strip by `cosh` of the half-width,
continuously differentiable in the two null coordinates, and real on the real transverse axis. It
depends on all three variables, and it is neither a slab potential — it varies with the transverse
coordinate — nor a sum of one-variable profiles.

The rectangle is chosen at the end: for any bound and any pair of radii the smallness condition holds
once the side is small enough, and an explicit admissible side is `1/(1 + K)` where `K` is the
constant of the condition.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

/-- **The cosine is bounded on a strip by the hyperbolic cosine of its half-width.** -/
theorem norm_cos_le_cosh {ρ : ℝ} (hρ : 0 ≤ ρ) {z : ℂ} (hz : |z.im| ≤ ρ) :
    ‖Complex.cos z‖ ≤ Real.cosh ρ := by
  have hform : Complex.cos z
      = (Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) / 2 := Complex.ext rfl rfl
  have h1 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp, Complex.mul_I_re]
  have h2 : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp, Complex.mul_I_re, Complex.neg_im, neg_neg]
  have hstep : ‖Complex.cos z‖ ≤ (Real.exp (-z.im) + Real.exp z.im) / 2 := by
    rw [hform, norm_div]
    have hnum : ‖Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)‖
        ≤ Real.exp (-z.im) + Real.exp z.im := by
      refine le_trans (norm_add_le _ _) ?_
      rw [h1, h2]
    have h2norm : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2norm]
    exact div_le_div_of_nonneg_right hnum (by norm_num)
  have hcosh : (Real.exp (-z.im) + Real.exp z.im) / 2 = Real.cosh z.im := by
    rw [Real.cosh_eq]
    ring
  rw [hcosh] at hstep
  refine hstep.trans (Real.cosh_le_cosh.mpr ?_)
  rwa [abs_of_nonneg hρ]

/-! ## The potential and its two null derivatives -/

/-- The example potential `sin ξ · cos η · cos z`. -/
noncomputable def cosPotential : ℝ → ℝ → ℂ → ℂ :=
  fun s t z => ((Real.sin s * Real.cos t : ℝ) : ℂ) * Complex.cos z

/-- Its derivative along the first null coordinate. -/
noncomputable def cosPotentialFst : ℝ → ℝ → ℂ → ℂ :=
  fun s t z => ((Real.cos s * Real.cos t : ℝ) : ℂ) * Complex.cos z

/-- Its derivative along the second null coordinate. -/
noncomputable def cosPotentialSnd : ℝ → ℝ → ℂ → ℂ :=
  fun s t z => ((Real.sin s * -Real.sin t : ℝ) : ℂ) * Complex.cos z

theorem continuous_cosPotential :
    Continuous fun q : (ℝ × ℝ) × ℂ => cosPotential q.1.1 q.1.2 q.2 :=
  (Complex.continuous_ofReal.comp
    ((Real.continuous_sin.comp (continuous_fst.comp continuous_fst)).mul
      (Real.continuous_cos.comp (continuous_snd.comp continuous_fst)))).mul
    (Complex.continuous_cos.comp continuous_snd)

theorem continuous_cosPotentialFst :
    Continuous fun q : (ℝ × ℝ) × ℂ => cosPotentialFst q.1.1 q.1.2 q.2 :=
  (Complex.continuous_ofReal.comp
    ((Real.continuous_cos.comp (continuous_fst.comp continuous_fst)).mul
      (Real.continuous_cos.comp (continuous_snd.comp continuous_fst)))).mul
    (Complex.continuous_cos.comp continuous_snd)

theorem continuous_cosPotentialSnd :
    Continuous fun q : (ℝ × ℝ) × ℂ => cosPotentialSnd q.1.1 q.1.2 q.2 :=
  (Complex.continuous_ofReal.comp
    ((Real.continuous_sin.comp (continuous_fst.comp continuous_fst)).mul
      ((Real.continuous_sin.comp (continuous_snd.comp continuous_fst)).neg))).mul
    (Complex.continuous_cos.comp continuous_snd)

theorem stripPotential_cosPotential (ρ : ℝ) : StripPotential cosPotential ρ where
  cont := continuous_cosPotential.continuousOn
  holo := fun _ _ => (differentiable_const _).mul Complex.differentiable_cos |>.differentiableOn

theorem stripPotentialC1_cosPotential (ρ : ℝ) :
    StripPotentialC1 cosPotential cosPotentialFst cosPotentialSnd ρ where
  base := stripPotential_cosPotential ρ
  hasDerivFst := by
    intro s t z _
    have hreal : HasDerivAt (fun x : ℝ => Real.sin x * Real.cos t)
        (Real.cos s * Real.cos t) s := (Real.hasDerivAt_sin s).mul_const _
    have hcast : HasDerivAt (fun x : ℝ => ((Real.sin x * Real.cos t : ℝ) : ℂ))
        (((Real.cos s * Real.cos t : ℝ) : ℂ)) s :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt s hreal
    exact hcast.mul_const (Complex.cos z)
  hasDerivSnd := by
    intro s t z _
    have hreal : HasDerivAt (fun x : ℝ => Real.sin s * Real.cos x)
        (Real.sin s * -Real.sin t) t := (Real.hasDerivAt_cos t).const_mul _
    have hcast : HasDerivAt (fun x : ℝ => ((Real.sin s * Real.cos x : ℝ) : ℂ))
        (((Real.sin s * -Real.sin t : ℝ) : ℂ)) t :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hreal
    exact hcast.mul_const (Complex.cos z)
  contFst := continuous_cosPotentialFst.continuousOn
  contSnd := continuous_cosPotentialSnd.continuousOn

/-- **The example potential is bounded on every strip.** -/
theorem norm_cosPotential_le {ρ : ℝ} (hρ : 0 ≤ ρ) (s t : ℝ) {z : ℂ} (hz : z ∈ imStrip ρ) :
    ‖cosPotential s t z‖ ≤ Real.cosh ρ := by
  have hz' : |z.im| ≤ ρ := le_of_lt (mem_imStrip.mp hz)
  have hcoef : ‖((Real.sin s * Real.cos t : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (Real.abs_sin_le_one s) (abs_nonneg _) (Real.abs_cos_le_one t)
  have hcos : ‖Complex.cos z‖ ≤ Real.cosh ρ := norm_cos_le_cosh hρ hz'
  have hcosh0 : (0 : ℝ) ≤ Real.cosh ρ := (Real.cosh_pos ρ).le
  rw [cosPotential, norm_mul]
  calc ‖((Real.sin s * Real.cos t : ℝ) : ℂ)‖ * ‖Complex.cos z‖
      ≤ 1 * Real.cosh ρ := mul_le_mul hcoef hcos (norm_nonneg _) (by norm_num)
    _ = Real.cosh ρ := one_mul _

/-- **The example potential is real on the real transverse axis.** -/
theorem cosPotential_im (s t w : ℝ) : (cosPotential s t ((w : ℝ) : ℂ)).im = 0 := by
  rw [cosPotential, ← Complex.ofReal_cos, ← Complex.ofReal_mul, Complex.ofReal_im]

/-! ## The datum -/

/-- **The example potential carries a clock datum**, for every strip and every sufficiently small
rectangle. -/
theorem clockDatum_cosPotential {ρ₀ ρ ρ₁ ρ₂ ρ₃ T : ℝ} (hρ₀ : 0 < ρ₀)
    (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀) (hT : 0 ≤ T)
    (hsmall : (4 + Real.cosh ρ₀ * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    (hρ₁0 : 0 ≤ ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 < ρ₃) (hρ₃ : ρ₃ < ρ₂) :
    ClockDatum cosPotential cosPotentialFst cosPotentialSnd ρ₀ (Real.cosh ρ₀) ρ ρ₁ ρ₂ ρ₃ T where
  pos := hρ₀
  potC1 := stripPotentialC1_cosPotential ρ₀
  massNonneg := (Real.cosh_pos ρ₀).le
  mass := fun s t _ _ _ hz => norm_cosPotential_le hρ₀.le s t hz
  radNonneg := hρ0
  rad := hρ
  sideNonneg := hT
  small := hsmall
  rad₁Nonneg := hρ₁0
  rad₁ := hρ₁
  rad₂Nonneg := hρ₂0
  rad₂ := hρ₂
  rad₃Pos := hρ₃0
  rad₃ := hρ₃

/-- A positive side small enough for the smallness condition. -/
theorem exists_small_side {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    ∃ T : ℝ, 0 < T ∧ A * T ^ 2 * Real.exp 2 / B ^ 2 < 1 := by
  set K : ℝ := A * Real.exp 2 / B ^ 2 with hK
  have hK0 : 0 < K := by
    rw [hK]
    positivity
  refine ⟨1 / (1 + K), by positivity, ?_⟩
  have hBne : B ^ 2 ≠ 0 := by positivity
  have hrw : A * (1 / (1 + K)) ^ 2 * Real.exp 2 / B ^ 2 = K * (1 / (1 + K)) ^ 2 := by
    rw [hK]
    field_simp
  rw [hrw, div_pow, one_pow, mul_one_div, div_lt_one (by positivity)]
  nlinarith [sq_nonneg K, hK0]

/-- **The coupled class is inhabited.** There is a potential carrying a clock datum, real on the
real transverse axis, depending on the transverse coordinate as well as on both null coordinates. -/
theorem exists_clockDatum_coupled :
    ∃ (V Vs Vt : ℝ → ℝ → ℂ → ℂ) (ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ),
      ClockDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T ∧ 0 < T ∧
        (∀ s t : ℝ, ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv) ∧
        (∀ s t w : ℝ, (V s t ((w : ℝ) : ℂ)).im = 0) ∧
        (∃ s t z z', V s t z ≠ V s t z') ∧ (∃ s s' t z, V s t z ≠ V s' t z) := by
  obtain ⟨T, hTpos, hsmall⟩ := exists_small_side
    (A := 4 + Real.cosh 1 * (1 : ℝ) ^ 2 / 4) (B := ((1 : ℝ) - 1 / 2) / 2)
    (by positivity) (by norm_num)
  refine ⟨cosPotential, cosPotentialFst, cosPotentialSnd, 1, Real.cosh 1, 1 / 2, 1 / 4, 1 / 8,
    1 / 16, T, clockDatum_cosPotential one_pos (by norm_num) (by norm_num) hTpos.le hsmall
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    hTpos, fun s t z hz => norm_cosPotential_le zero_le_one s t hz, cosPotential_im, ?_, ?_⟩
  · refine ⟨Real.pi / 2, 0, 0, ((Real.pi : ℝ) : ℂ), ?_⟩
    rw [cosPotential, cosPotential, Real.sin_pi_div_two, Real.cos_zero, Complex.cos_zero,
      Complex.cos_pi]
    norm_num
  · refine ⟨0, Real.pi / 2, 0, 0, ?_⟩
    rw [cosPotential, cosPotential, Real.sin_zero, Real.sin_pi_div_two, Real.cos_zero,
      Complex.cos_zero]
    norm_num

end GaloisForLFunctions.HTGeometry
