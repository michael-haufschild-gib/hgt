import Mathlib
import GaloisForLFunctions.HTGeometry.ComplexScaledGammaIntegral

/-!
# The Mellin transform of the sine

`∫_0^∞ x^{α-1} sin x dx = Γ(α) sin(πα/2)`  for  `0 < α < 1`.

This is the constant in the large-distance asymptotics of the quasi-Riesz coupling coefficients,
equation (12) of Zhong--Malomed--Yan, arXiv:2407.12441.  The integral is only conditionally
convergent, so it is understood as `lim_{R → ∞} ∫_0^R`, and it is not a Lebesgue integral over the
ray.

The proof regularises by `e^{-εx}`.  The regularised integral is absolutely convergent and is the
imaginary part of the complex-scaled Euler integral at the scale `ε - i`, which the corpus already
evaluates as `Γ(α)/(ε - i)^α`; letting `ε → 0` moves the scale to `-i`, where the value is
`Γ(α) e^{iπα/2}`.  What makes the de-regularisation legitimate is a tail bound that is *uniform in
`ε`*: for `α ≤ 1` the weight `x^{α-1}e^{-εx}` is positive and decreasing, so one integration by
parts bounds every tail past `R` by `2R^{α-1}`, with no dependence on `ε`.

## Main results

* `abs_integral_tail_le` — the uniform tail bound `|∫_R^B x^{α-1}e^{-εx} sin x dx| ≤ 2R^{α-1}`.
* `mellinSineReg`, `mellinSineReg_eq` — the regularised integral and its closed form.
* `tendsto_mellinSineReg` — its limit `Γ(α) sin(πα/2)` as `ε → 0⁺`.
* `tendsto_integral_rpow_mul_sin` — the Mellin transform of the sine.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-! ## The regularised weight -/

/-- The regularised weight `x^{α-1} e^{-εx}`. -/
noncomputable def mellinWeight (α ε : ℝ) (x : ℝ) : ℝ := x ^ (α - 1) * Real.exp (-(ε * x))

/-- Its derivative. -/
noncomputable def mellinWeightDeriv (α ε : ℝ) (x : ℝ) : ℝ :=
  (α - 1) * x ^ (α - 1 - 1) * Real.exp (-(ε * x)) + x ^ (α - 1) * (Real.exp (-(ε * x)) * -ε)

theorem hasDerivAt_mellinWeight {α ε : ℝ} {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (mellinWeight α ε) (mellinWeightDeriv α ε x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ (α - 1)) ((α - 1) * x ^ (α - 1 - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl hx)
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (-(ε * y))) (Real.exp (-(ε * x)) * -ε) x := by
    have h3 : HasDerivAt (fun y : ℝ => -(ε * y)) (-ε) x := by
      simpa using (hasDerivAt_id x).const_mul (-ε)
    simpa using h3.exp
  have h := h1.mul h2
  simp only [Pi.mul_def] at h
  exact h

theorem mellinWeight_pos {α ε x : ℝ} (hx : 0 < x) : 0 < mellinWeight α ε x := by
  rw [mellinWeight]
  positivity

theorem mellinWeightDeriv_nonpos {α ε x : ℝ} (hα : α ≤ 1) (hε : 0 ≤ ε) (hx : 0 < x) :
    mellinWeightDeriv α ε x ≤ 0 := by
  rw [mellinWeightDeriv]
  have h1 : (α - 1) * x ^ (α - 1 - 1) * Real.exp (-(ε * x)) ≤ 0 := by
    have hprod : (0:ℝ) ≤ x ^ (α - 1 - 1) * Real.exp (-(ε * x)) := by positivity
    nlinarith [hprod, hα]
  have h2 : x ^ (α - 1) * (Real.exp (-(ε * x)) * -ε) ≤ 0 := by
    have hprod : (0:ℝ) ≤ x ^ (α - 1) * Real.exp (-(ε * x)) := by positivity
    nlinarith [hprod, hε]
  linarith

theorem continuousOn_mellinWeight {α ε : ℝ} {s : Set ℝ} (hs : ∀ x ∈ s, x ≠ 0) :
    ContinuousOn (mellinWeight α ε) s := fun x hx =>
  ((hasDerivAt_mellinWeight (hs x hx)).continuousAt).continuousWithinAt

theorem continuousOn_mellinWeightDeriv {α ε : ℝ} {s : Set ℝ} (hs : ∀ x ∈ s, x ≠ 0) :
    ContinuousOn (mellinWeightDeriv α ε) s := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  have hne := hs x hx
  have hc1 : ContinuousAt (fun y : ℝ => y ^ (α - 1 - 1)) x :=
    Real.continuousAt_rpow_const x _ (Or.inl hne)
  have hc2 : ContinuousAt (fun y : ℝ => y ^ (α - 1)) x :=
    Real.continuousAt_rpow_const x _ (Or.inl hne)
  have hc3 : ContinuousAt (fun y : ℝ => Real.exp (-(ε * y))) x :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousAt
  exact ((continuousAt_const.mul hc1).mul hc3).add (hc2.mul (hc3.mul continuousAt_const))

/-! ## The uniform tail bound -/

/-- **The uniform tail bound.**  For `α ≤ 1` and every regularisation `ε ≥ 0`, the oscillatory tail
past `R` is bounded by twice the weight at `R`, with no dependence on `ε`. -/
theorem abs_integral_tail_le {α ε R B : ℝ} (hα : α ≤ 1) (hε : 0 ≤ ε) (hR : 0 < R) (hRB : R ≤ B) :
    |∫ x in R..B, mellinWeight α ε x * Real.sin x| ≤ 2 * R ^ (α - 1) := by
  have hmem : ∀ x ∈ uIcc R B, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hRB] at hx
    exact ne_of_gt (lt_of_lt_of_le hR hx.1)
  have hmem' : ∀ x ∈ Icc R B, (0:ℝ) < x := fun x hx => lt_of_lt_of_le hR hx.1
  have hcw : ContinuousOn (mellinWeight α ε) (uIcc R B) := continuousOn_mellinWeight hmem
  have hcwd : ContinuousOn (mellinWeightDeriv α ε) (uIcc R B) :=
    continuousOn_mellinWeightDeriv hmem
  have hint1 : IntervalIntegrable (fun x => mellinWeight α ε x * Real.sin x) volume R B :=
    (hcw.mul (Real.continuous_sin.continuousOn)).intervalIntegrable
  have hint2 : IntervalIntegrable (fun x => -Real.cos x * mellinWeightDeriv α ε x) volume R B :=
    ((Real.continuous_cos.neg.continuousOn).mul hcwd).intervalIntegrable
  have hderiv : ∀ x ∈ uIcc R B,
      HasDerivAt (fun y : ℝ => -Real.cos y * mellinWeight α ε y)
        (mellinWeight α ε x * Real.sin x + -Real.cos x * mellinWeightDeriv α ε x) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => -Real.cos y) (Real.sin x) x := by
      have hcos := (Real.hasDerivAt_cos x).neg
      simp only [Pi.neg_def] at hcos
      exact hcos.congr_deriv (by ring)
    have h := h1.mul (hasDerivAt_mellinWeight (α := α) (ε := ε) (hmem x hx))
    simp only [Pi.mul_def] at h
    exact h.congr_deriv (by ring)
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.add hint2)
  rw [intervalIntegral.integral_add hint1 hint2] at hsub
  have hwdint : (∫ x in R..B, mellinWeightDeriv α ε x)
      = mellinWeight α ε B - mellinWeight α ε R :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_mellinWeight (α := α) (ε := ε) (hmem x hx))
      hcwd.intervalIntegrable
  have hbound : ∀ x ∈ Icc R B,
      |(-Real.cos x * mellinWeightDeriv α ε x)| ≤ -mellinWeightDeriv α ε x := by
    intro x hx
    rw [abs_mul, abs_neg]
    have hcos : |Real.cos x| ≤ 1 := Real.abs_cos_le_one x
    have hwdle : mellinWeightDeriv α ε x ≤ 0 := mellinWeightDeriv_nonpos hα hε (hmem' x hx)
    rw [abs_of_nonpos hwdle]
    nlinarith [abs_nonneg (Real.cos x)]
  have hcorr : |∫ x in R..B, -Real.cos x * mellinWeightDeriv α ε x|
      ≤ mellinWeight α ε R - mellinWeight α ε B := by
    calc |∫ x in R..B, -Real.cos x * mellinWeightDeriv α ε x|
        ≤ ∫ x in R..B, |(-Real.cos x * mellinWeightDeriv α ε x)| :=
          intervalIntegral.abs_integral_le_integral_abs hRB
    _ ≤ ∫ x in R..B, -mellinWeightDeriv α ε x :=
          intervalIntegral.integral_mono_on hRB hint2.abs (hcwd.neg).intervalIntegrable hbound
    _ = mellinWeight α ε R - mellinWeight α ε B := by
          rw [intervalIntegral.integral_neg, hwdint]; ring
  have hwB : (0:ℝ) < mellinWeight α ε B := mellinWeight_pos (lt_of_lt_of_le hR hRB)
  have hwR : (0:ℝ) < mellinWeight α ε R := mellinWeight_pos hR
  have hbdy : |(-Real.cos B * mellinWeight α ε B) - (-Real.cos R * mellinWeight α ε R)|
      ≤ mellinWeight α ε B + mellinWeight α ε R := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_mul, abs_neg, abs_neg, abs_of_pos hwB, abs_of_pos hwR]
    have h1 : |Real.cos B| * mellinWeight α ε B ≤ mellinWeight α ε B := by
      nlinarith [Real.abs_cos_le_one B, hwB.le]
    have h2 : |Real.cos R| * mellinWeight α ε R ≤ mellinWeight α ε R := by
      nlinarith [Real.abs_cos_le_one R, hwR.le]
    linarith
  have hmain : (∫ x in R..B, mellinWeight α ε x * Real.sin x)
      = ((-Real.cos B * mellinWeight α ε B) - (-Real.cos R * mellinWeight α ε R))
        - ∫ x in R..B, -Real.cos x * mellinWeightDeriv α ε x := by linarith [hsub]
  rw [hmain]
  have hstep : |((-Real.cos B * mellinWeight α ε B) - (-Real.cos R * mellinWeight α ε R))
      - ∫ x in R..B, -Real.cos x * mellinWeightDeriv α ε x| ≤ 2 * mellinWeight α ε R := by
    refine (abs_sub _ _).trans ?_
    linarith [hbdy, hcorr]
  refine hstep.trans ?_
  have hwR' : mellinWeight α ε R ≤ R ^ (α - 1) := by
    rw [mellinWeight]
    have hexp : Real.exp (-(ε * R)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hp : (0:ℝ) ≤ R ^ (α - 1) := Real.rpow_nonneg hR.le _
    nlinarith [Real.exp_pos (-(ε * R))]
  linarith

/-! ## The regularised Mellin integral -/

/-- The regularised integral `∫_0^∞ x^{α-1} e^{-εx} sin x dx`. -/
noncomputable def mellinSineReg (α ε : ℝ) : ℝ :=
  ∫ x in Ioi (0:ℝ), mellinWeight α ε x * Real.sin x

theorem integrableOn_mellinWeight {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    IntegrableOn (mellinWeight α ε) (Ioi 0) volume := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := α - 1) (b := ε)
    (by linarith) le_rfl hε
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [mellinWeight, Real.rpow_one]
  ring_nf

theorem measurable_mellinWeight (α ε : ℝ) : Measurable (mellinWeight α ε) := by
  rw [show mellinWeight α ε = fun x : ℝ => x ^ (α - 1) * Real.exp (-(ε * x)) from rfl]
  exact (measurable_id.pow_const _).mul
    (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg))

theorem integrableOn_mellinSineIntegrand {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => mellinWeight α ε x * Real.sin x) (Ioi 0) volume := by
  refine (integrableOn_mellinWeight hα hε).mono' ?_ ?_
  · exact ((measurable_mellinWeight α ε).mul Real.measurable_sin).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).2 ?_
    filter_upwards with x hx
    rw [Real.norm_eq_abs, abs_mul]
    have hw : (0:ℝ) < mellinWeight α ε x := mellinWeight_pos hx
    rw [abs_of_pos hw]
    nlinarith [Real.abs_sin_le_one x, hw.le, abs_nonneg (Real.sin x)]

/-- The pointwise identity behind the closed form. -/
theorem mellinSine_pointwise {α ε : ℝ} {t : ℝ} (ht : 0 < t) :
    ((mellinWeight α ε t * Real.sin t : ℝ) : ℂ) * (2 * Complex.I)
      = (t : ℂ) ^ ((α : ℂ) - 1) * Complex.exp (-(((ε : ℂ) - Complex.I) * (t : ℂ)))
        - (t : ℂ) ^ ((α : ℂ) - 1) * Complex.exp (-(((ε : ℂ) + Complex.I) * (t : ℂ))) := by
  have hpow : ((t ^ (α - 1) : ℝ) : ℂ) = (t : ℂ) ^ ((α : ℂ) - 1) := by
    rw [Complex.ofReal_cpow ht.le]
    norm_cast
  have hsin : Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (-((t : ℂ) * Complex.I))
      = 2 * Complex.I * Complex.sin (t : ℂ) := by
    have h := Complex.two_sin (t : ℂ)
    rw [neg_mul] at h
    have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (-Complex.I) * h
      + (Complex.exp ((t : ℂ) * Complex.I) - Complex.exp (-((t : ℂ) * Complex.I))) * hII
  have hsplit1 : -(((ε : ℂ) - Complex.I) * (t : ℂ))
      = -((ε : ℂ) * (t : ℂ)) + (t : ℂ) * Complex.I := by ring
  have hsplit2 : -(((ε : ℂ) + Complex.I) * (t : ℂ))
      = -((ε : ℂ) * (t : ℂ)) + -((t : ℂ) * Complex.I) := by ring
  have hexpc : Complex.exp (((-(ε * t) : ℝ)) : ℂ) = Complex.exp (-((ε : ℂ) * (t : ℂ))) := by
    congr 1
    push_cast
    ring
  rw [hsplit1, hsplit2, Complex.exp_add, Complex.exp_add, mellinWeight,
    Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_sin, hpow, hexpc]
  linear_combination
    (-((t : ℂ) ^ ((α : ℂ) - 1) * Complex.exp (-((ε : ℂ) * (t : ℂ))))) * hsin

/-- **The closed form of the regularised integral.** -/
theorem mellinSineReg_eq {α ε : ℝ} (hα : 0 < α) (hε : 0 < ε) :
    ((mellinSineReg α ε : ℝ) : ℂ) * (2 * Complex.I)
      = Complex.Gamma (α : ℂ) / (((ε : ℂ) - Complex.I) ^ (α : ℂ))
        - Complex.Gamma (α : ℂ) / (((ε : ℂ) + Complex.I) ^ (α : ℂ)) := by
  have hre1 : (0:ℝ) < ((ε : ℂ) - Complex.I).re := by simp [hε]
  have hre2 : (0:ℝ) < ((ε : ℂ) + Complex.I).re := by simp [hε]
  have hare : (0:ℝ) < ((α : ℂ)).re := by simpa using hα
  have hint1 := integrableOn_cpow_mul_cexp (a := (α : ℂ)) (c := (ε : ℂ) - Complex.I) hare hre1
  have hint2 := integrableOn_cpow_mul_cexp (a := (α : ℂ)) (c := (ε : ℂ) + Complex.I) hare hre2
  have hIm : ((mellinSineReg α ε : ℝ) : ℂ)
      = ∫ x in Ioi (0:ℝ), ((mellinWeight α ε x * Real.sin x : ℝ) : ℂ) := by
    rw [mellinSineReg, integral_complex_ofReal]
  rw [hIm, ← MeasureTheory.integral_mul_const]
  rw [← gammaScaledIntegral_eq hare hre1, ← gammaScaledIntegral_eq hare hre2,
    gammaScaledIntegral, gammaScaledIntegral, ← MeasureTheory.integral_sub hint1 hint2]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  exact mellinSine_pointwise (mem_Ioi.mp ht)

/-! ## Removing the regularisation -/

theorem cpow_neg_I (α : ℝ) :
    (-Complex.I) ^ (α : ℂ) = Complex.exp (-((Real.pi : ℂ) / 2 * (α : ℂ)) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (by simp), Complex.log_neg_I]
  congr 1
  ring

theorem cpow_I (α : ℝ) :
    (Complex.I) ^ (α : ℂ) = Complex.exp ((Real.pi : ℂ) / 2 * (α : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero Complex.I_ne_zero, Complex.log_I]
  congr 1
  ring

/-- The boundary value of the regularised closed form. -/
theorem mellinSine_boundary_value (α : ℝ) :
    (Complex.Gamma (α : ℂ) / ((-Complex.I) ^ (α : ℂ))
      - Complex.Gamma (α : ℂ) / ((Complex.I) ^ (α : ℂ))) / (2 * Complex.I)
      = ((Real.Gamma α * Real.sin (Real.pi * α / 2) : ℝ) : ℂ) := by
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by simp [Complex.I_ne_zero]
  set E : ℂ := Complex.exp ((Real.pi : ℂ) / 2 * (α : ℂ) * Complex.I) with hE
  have hcpow1 : (-Complex.I) ^ (α : ℂ) = E⁻¹ := by
    rw [cpow_neg_I, hE, ← Complex.exp_neg]
    congr 1
    ring
  have hcpow2 : (Complex.I) ^ (α : ℂ) = E := by rw [cpow_I]
  have hEinv : E⁻¹ = Complex.exp (-((Real.pi : ℂ) / 2 * (α : ℂ) * Complex.I)) := by
    rw [hE, ← Complex.exp_neg]
  have hsin : E - E⁻¹ = 2 * Complex.I * Complex.sin ((Real.pi : ℂ) / 2 * (α : ℂ)) := by
    have h := Complex.two_sin ((Real.pi : ℂ) / 2 * (α : ℂ))
    rw [neg_mul] at h
    have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
    rw [hEinv, hE]
    linear_combination (-Complex.I) * h
      + (Complex.exp ((Real.pi : ℂ) / 2 * (α : ℂ) * Complex.I)
        - Complex.exp (-((Real.pi : ℂ) / 2 * (α : ℂ) * Complex.I))) * hII
  have hcast : ((Real.Gamma α * Real.sin (Real.pi * α / 2) : ℝ) : ℂ)
      = Complex.Gamma (α : ℂ) * Complex.sin ((Real.pi : ℂ) / 2 * (α : ℂ)) := by
    rw [Complex.ofReal_mul, Complex.Gamma_ofReal, Complex.ofReal_sin]
    congr 2
    push_cast
    ring
  have hgoal : Complex.Gamma (α : ℂ) * E - Complex.Gamma (α : ℂ) / E
      = Complex.Gamma (α : ℂ) * Complex.sin ((Real.pi : ℂ) / 2 * (α : ℂ)) * (2 * Complex.I) := by
    rw [div_eq_mul_inv]
    linear_combination Complex.Gamma (α : ℂ) * hsin
  have hdi : Complex.Gamma (α : ℂ) / E⁻¹ = Complex.Gamma (α : ℂ) * E := by
    rw [div_eq_mul_inv, inv_inv]
  rw [hcpow1, hcpow2, hcast, hdi, hgoal, mul_div_assoc, div_self hI, mul_one]

theorem tendsto_mellinSineReg {α : ℝ} (hα : 0 < α) :
    Tendsto (fun ε : ℝ => mellinSineReg α ε) (𝓝[>] 0)
      (𝓝 (Real.Gamma α * Real.sin (Real.pi * α / 2))) := by
  have hI : (2 : ℂ) * Complex.I ≠ 0 := by simp [Complex.I_ne_zero]
  have hslit1 : (-Complex.I) ∈ Complex.slitPlane := by
    right
    simp
  have hslit2 : (Complex.I) ∈ Complex.slitPlane := by
    right
    simp
  have hc1 : Tendsto (fun ε : ℝ => ((ε : ℂ) - Complex.I)) (𝓝[>] (0:ℝ)) (𝓝 (-Complex.I)) := by
    have hcont : Continuous fun ε : ℝ => ((ε : ℂ) - Complex.I) :=
      Complex.continuous_ofReal.sub continuous_const
    have h0 : Tendsto (fun ε : ℝ => ((ε : ℂ) - Complex.I)) (𝓝 (0:ℝ))
        (𝓝 (((0:ℝ) : ℂ) - Complex.I)) := hcont.tendsto 0
    rw [show ((0:ℝ) : ℂ) - Complex.I = -Complex.I by simp] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hc2 : Tendsto (fun ε : ℝ => ((ε : ℂ) + Complex.I)) (𝓝[>] (0:ℝ)) (𝓝 (Complex.I)) := by
    have hcont : Continuous fun ε : ℝ => ((ε : ℂ) + Complex.I) :=
      Complex.continuous_ofReal.add continuous_const
    have h0 : Tendsto (fun ε : ℝ => ((ε : ℂ) + Complex.I)) (𝓝 (0:ℝ))
        (𝓝 (((0:ℝ) : ℂ) + Complex.I)) := hcont.tendsto 0
    rw [show ((0:ℝ) : ℂ) + Complex.I = Complex.I by simp] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hp1 : Tendsto (fun ε : ℝ => ((ε : ℂ) - Complex.I) ^ (α : ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 ((-Complex.I) ^ (α : ℂ))) := (continuousAt_cpow_const hslit1).tendsto.comp hc1
  have hp2 : Tendsto (fun ε : ℝ => ((ε : ℂ) + Complex.I) ^ (α : ℂ)) (𝓝[>] (0:ℝ))
      (𝓝 ((Complex.I) ^ (α : ℂ))) := (continuousAt_cpow_const hslit2).tendsto.comp hc2
  have hne1 : (-Complex.I) ^ (α : ℂ) ≠ 0 := by
    rw [cpow_neg_I]
    exact Complex.exp_ne_zero _
  have hne2 : (Complex.I) ^ (α : ℂ) ≠ 0 := by
    rw [cpow_I]
    exact Complex.exp_ne_zero _
  have hcx : Tendsto (fun ε : ℝ =>
      (Complex.Gamma (α : ℂ) / (((ε : ℂ) - Complex.I) ^ (α : ℂ))
        - Complex.Gamma (α : ℂ) / (((ε : ℂ) + Complex.I) ^ (α : ℂ))) / (2 * Complex.I))
      (𝓝[>] (0:ℝ)) (𝓝 (((Real.Gamma α * Real.sin (Real.pi * α / 2) : ℝ) : ℂ))) := by
    rw [← mellinSine_boundary_value α]
    exact (((tendsto_const_nhds.div hp1 hne1).sub
      (tendsto_const_nhds.div hp2 hne2)).div_const _)
  have heq : (fun ε : ℝ => (Complex.Gamma (α : ℂ) / (((ε : ℂ) - Complex.I) ^ (α : ℂ))
        - Complex.Gamma (α : ℂ) / (((ε : ℂ) + Complex.I) ^ (α : ℂ))) / (2 * Complex.I))
      =ᶠ[𝓝[>] (0:ℝ)] (fun ε : ℝ => ((mellinSineReg α ε : ℝ) : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← mellinSineReg_eq hα hε, mul_div_assoc, div_self hI, mul_one]
  have hcx' := hcx.congr' heq
  have hre := (Complex.continuous_re.tendsto _).comp hcx'
  simp only [Function.comp_def, Complex.ofReal_re] at hre
  exact hre

/-! ## The Mellin transform of the sine -/

theorem integral_Ioi_split_mellinSine {α ε R : ℝ} (hα : 0 < α) (hε : 0 < ε) (hR : 0 < R) :
    mellinSineReg α ε = (∫ x in (0:ℝ)..R, mellinWeight α ε x * Real.sin x)
      + ∫ x in Ioi R, mellinWeight α ε x * Real.sin x := by
  have hint := integrableOn_mellinSineIntegrand hα hε
  have h1 : IntegrableOn (fun x : ℝ => mellinWeight α ε x * Real.sin x) (Ioc 0 R) volume :=
    hint.mono_set Ioc_subset_Ioi_self
  have h2 : IntegrableOn (fun x : ℝ => mellinWeight α ε x * Real.sin x) (Ioi R) volume :=
    hint.mono_set (Ioi_subset_Ioi hR.le)
  rw [mellinSineReg, ← Ioc_union_Ioi_eq_Ioi hR.le,
    MeasureTheory.setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi h1 h2,
    intervalIntegral.integral_of_le hR.le]

theorem abs_integral_Ioi_tail_le {α ε R : ℝ} (hα0 : 0 < α) (hα : α ≤ 1) (hε : 0 < ε) (hR : 0 < R) :
    |∫ x in Ioi R, mellinWeight α ε x * Real.sin x| ≤ 2 * R ^ (α - 1) := by
  have hint : IntegrableOn (fun x : ℝ => mellinWeight α ε x * Real.sin x) (Ioi R) volume :=
    (integrableOn_mellinSineIntegrand hα0 hε).mono_set (Ioi_subset_Ioi hR.le)
  have hb : Tendsto (fun n : ℕ => R + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ R tendsto_natCast_atTop_atTop
  have htend := MeasureTheory.intervalIntegral_tendsto_integral_Ioi R hint hb
  have habs := (continuous_abs.tendsto _).comp htend
  refine le_of_tendsto habs ?_
  filter_upwards with n
  exact abs_integral_tail_le hα hε.le hR (le_add_of_nonneg_right (Nat.cast_nonneg n))

/-- The de-regularisation estimate on a fixed truncation. -/
theorem abs_sub_mellinSineReg_le {α ε R : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hε : 0 < ε)
    (hR : 0 < R) :
    |(∫ x in (0:ℝ)..R, x ^ (α - 1) * Real.sin x) - mellinSineReg α ε|
      ≤ (1 - Real.exp (-(ε * R))) * (R ^ α / α) + 2 * R ^ (α - 1) := by
  have hbase : IntervalIntegrable (fun x : ℝ => x ^ (α - 1)) volume 0 R :=
    intervalIntegrable_rpow' (by linarith)
  have hI1 : IntervalIntegrable (fun x : ℝ => x ^ (α - 1) * Real.sin x) volume 0 R := by
    refine hbase.mono_fun
      (((measurable_id.pow_const _).mul Real.measurable_sin).aestronglyMeasurable) ?_
    filter_upwards with x
    simp only [Real.norm_eq_abs, abs_mul]
    nlinarith [Real.abs_sin_le_one x, abs_nonneg (x ^ (α - 1)), abs_nonneg (Real.sin x)]
  have hI2 : IntervalIntegrable (fun x : ℝ => mellinWeight α ε x * Real.sin x) volume 0 R := by
    refine hbase.mono_fun
      (((measurable_mellinWeight α ε).mul Real.measurable_sin).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    rw [Set.uIoc_of_le hR.le] at hx
    have hx0 : (0:ℝ) < x := hx.1
    have hp : (0:ℝ) ≤ x ^ (α - 1) := Real.rpow_nonneg hx0.le _
    have hexp0 : (0:ℝ) < Real.exp (-(ε * x)) := Real.exp_pos _
    have hexp1 : Real.exp (-(ε * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    simp only [Real.norm_eq_abs, mellinWeight, abs_mul, abs_of_nonneg hp, abs_of_pos hexp0]
    have hA : (0:ℝ) ≤ x ^ (α - 1) * Real.exp (-(ε * x)) := by positivity
    have hle : x ^ (α - 1) * Real.exp (-(ε * x)) ≤ x ^ (α - 1) := by nlinarith
    nlinarith [Real.abs_sin_le_one x, abs_nonneg (Real.sin x), hA, hle]
  have hsplit := integral_Ioi_split_mellinSine hα0 hε hR
  have hnear : |(∫ x in (0:ℝ)..R, x ^ (α - 1) * Real.sin x)
      - ∫ x in (0:ℝ)..R, mellinWeight α ε x * Real.sin x|
      ≤ (1 - Real.exp (-(ε * R))) * (R ^ α / α) := by
    rw [← intervalIntegral.integral_sub hI1 hI2]
    have hmono : ∀ x ∈ Icc (0:ℝ) R,
        |x ^ (α - 1) * Real.sin x - mellinWeight α ε x * Real.sin x|
          ≤ (1 - Real.exp (-(ε * R))) * x ^ (α - 1) := by
      intro x hx
      have hx0 : (0:ℝ) ≤ x := hx.1
      have hp : (0:ℝ) ≤ x ^ (α - 1) := Real.rpow_nonneg hx0 _
      have hexpx : Real.exp (-(ε * R)) ≤ Real.exp (-(ε * x)) :=
        Real.exp_le_exp.mpr (by nlinarith [hx.2])
      have hexp1 : Real.exp (-(ε * x)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      have hfac : x ^ (α - 1) * Real.sin x - mellinWeight α ε x * Real.sin x
          = x ^ (α - 1) * (1 - Real.exp (-(ε * x))) * Real.sin x := by
        rw [mellinWeight]; ring
      rw [hfac, abs_mul, abs_mul, abs_of_nonneg hp,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - Real.exp (-(ε * x)))]
      have hB : (0:ℝ) ≤ x ^ (α - 1) * (1 - Real.exp (-(ε * x))) :=
        mul_nonneg hp (by linarith)
      have hstep1 : x ^ (α - 1) * (1 - Real.exp (-(ε * x))) * |Real.sin x|
          ≤ x ^ (α - 1) * (1 - Real.exp (-(ε * x))) := by
        nlinarith [Real.abs_sin_le_one x, abs_nonneg (Real.sin x), hB]
      have hstep2 : x ^ (α - 1) * (1 - Real.exp (-(ε * x)))
          ≤ (1 - Real.exp (-(ε * R))) * x ^ (α - 1) := by
        nlinarith [hp, hexpx]
      linarith
    calc |∫ x in (0:ℝ)..R, (x ^ (α - 1) * Real.sin x - mellinWeight α ε x * Real.sin x)|
        ≤ ∫ x in (0:ℝ)..R, |x ^ (α - 1) * Real.sin x - mellinWeight α ε x * Real.sin x| :=
          intervalIntegral.abs_integral_le_integral_abs hR.le
    _ ≤ ∫ x in (0:ℝ)..R, (1 - Real.exp (-(ε * R))) * x ^ (α - 1) :=
          intervalIntegral.integral_mono_on hR.le (hI1.sub hI2).abs (hbase.const_mul _) hmono
    _ = (1 - Real.exp (-(ε * R))) * (R ^ α / α) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith)),
            Real.zero_rpow (by linarith)]
          ring_nf
  have htail := abs_integral_Ioi_tail_le hα0 hα1.le hε hR
  have hrw : (∫ x in (0:ℝ)..R, x ^ (α - 1) * Real.sin x)
      - ((∫ x in (0:ℝ)..R, mellinWeight α ε x * Real.sin x)
        + ∫ x in Ioi R, mellinWeight α ε x * Real.sin x)
      = ((∫ x in (0:ℝ)..R, x ^ (α - 1) * Real.sin x)
        - ∫ x in (0:ℝ)..R, mellinWeight α ε x * Real.sin x)
        - ∫ x in Ioi R, mellinWeight α ε x * Real.sin x := by ring
  rw [hsplit, hrw]
  refine (abs_sub _ _).trans ?_
  linarith [hnear, htail]

/-- **The Mellin transform of the sine.**  For `0 < α < 1`,
`∫_0^∞ x^{α-1} sin x dx = Γ(α) sin(πα/2)`, the improper integral being the limit of its
truncations. -/
theorem tendsto_integral_rpow_mul_sin {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    Tendsto (fun R : ℝ => ∫ x in (0:ℝ)..R, x ^ (α - 1) * Real.sin x) atTop
      (𝓝 (Real.Gamma α * Real.sin (Real.pi * α / 2))) := by
  have hkey : ∀ R : ℝ, 0 < R →
      |(∫ x in (0:ℝ)..R, x ^ (α - 1) * Real.sin x)
        - Real.Gamma α * Real.sin (Real.pi * α / 2)| ≤ 2 * R ^ (α - 1) := by
    intro R hR
    have hlim1 : Tendsto (fun ε : ℝ =>
        |(∫ x in (0:ℝ)..R, x ^ (α - 1) * Real.sin x) - mellinSineReg α ε|)
        (𝓝[>] (0:ℝ))
        (𝓝 |(∫ x in (0:ℝ)..R, x ^ (α - 1) * Real.sin x)
          - Real.Gamma α * Real.sin (Real.pi * α / 2)|) :=
      (continuous_abs.tendsto _).comp (tendsto_const_nhds.sub (tendsto_mellinSineReg hα0))
    have hexp : Tendsto (fun ε : ℝ => Real.exp (-(ε * R))) (𝓝[>] (0:ℝ)) (𝓝 1) := by
      have hcont : Continuous fun ε : ℝ => Real.exp (-(ε * R)) :=
        Real.continuous_exp.comp ((continuous_id.mul continuous_const).neg)
      have h0 : Tendsto (fun ε : ℝ => Real.exp (-(ε * R))) (𝓝 (0:ℝ))
          (𝓝 (Real.exp (-((0:ℝ) * R)))) := hcont.tendsto 0
      rw [show Real.exp (-((0:ℝ) * R)) = 1 by norm_num] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun ε : ℝ =>
        (1 - Real.exp (-(ε * R))) * (R ^ α / α) + 2 * R ^ (α - 1))
        (𝓝[>] (0:ℝ)) (𝓝 (2 * R ^ (α - 1))) := by
      have hone : Tendsto (fun _ : ℝ => (1:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 1) := tendsto_const_nhds
      have hsub : Tendsto (fun ε : ℝ => 1 - Real.exp (-(ε * R))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
        simpa using hone.sub hexp
      have hmul : Tendsto (fun ε : ℝ => (1 - Real.exp (-(ε * R))) * (R ^ α / α))
          (𝓝[>] (0:ℝ)) (𝓝 0) := by
        simpa using hsub.mul_const (R ^ α / α)
      simpa using hmul.add_const (2 * R ^ (α - 1))
    refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact abs_sub_mellinSineReg_le hα0 hα1 hε hR
  rw [tendsto_iff_dist_tendsto_zero]
  have hzero : Tendsto (fun R : ℝ => 2 * R ^ (α - 1)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := 1 - α) (by linarith)
    have h2 : Tendsto (fun R : ℝ => R ^ (α - 1)) atTop (𝓝 0) := by
      simpa [show -(1 - α) = α - 1 by ring] using h
    simpa using h2.const_mul (2:ℝ)
  refine squeeze_zero' ?_ ?_ hzero
  · filter_upwards with R using dist_nonneg
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    rw [Real.dist_eq]
    exact hkey R hR

end GaloisForLFunctions.HTGeometry.FDNLS
