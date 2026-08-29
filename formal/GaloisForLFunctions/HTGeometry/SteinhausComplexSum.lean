import GaloisForLFunctions.HTGeometry.SteinhausIntervalBridge

/-!
# The complex Steinhaus sum and its rotated Laplace transform

`Y = ∑ a_i ζ_i` with `ζ_i` independent Haar unit phases.  For every fixed rotation `e^{-is}` the
real part `Re(Y e^{-is})` has EXACTLY the same Laplace transform as the unrotated projection,
because Haar measure on the circle is translation invariant.  This is the only probabilistic input
the large-deviation upper bound needs.
-/

open MeasureTheory Filter Topology

namespace HTGeometry

local instance phaseCirclePositiveSum : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

/-- The complex Steinhaus sum. -/
def steinhausSum {ι : Type*} [Fintype ι] (a : ι → ℝ) (x : ι → PhaseCircle) : ℂ :=
  ∑ i, (a i : ℂ) * steinhausPhase (x i)

/-- The rotated real projection of the Steinhaus sum. -/
def steinhausRotProj {ι : Type*} [Fintype ι] (a : ι → ℝ) (s : ℝ) (x : ι → PhaseCircle) : ℝ :=
  ∑ i, a i * (steinhausPhase (x i) * Complex.exp (-(s * Complex.I))).re

theorem steinhausRotProj_eq_re {ι : Type*} [Fintype ι] (a : ι → ℝ) (s : ℝ)
    (x : ι → PhaseCircle) :
    steinhausRotProj a s x = (steinhausSum a x * Complex.exp (-(s * Complex.I))).re := by
  rw [steinhausSum, steinhausRotProj, Finset.sum_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc]
  simp [Complex.mul_re]

/-- The phase shift. -/
theorem steinhausPhase_add_coe (y : PhaseCircle) (s : ℝ) :
    steinhausPhase (y + (s : PhaseCircle)) = steinhausPhase y * Complex.exp (s * Complex.I) := by
  induction y using QuotientAddGroup.induction_on with
  | H t =>
    have hcoe : ((t : PhaseCircle) + (s : PhaseCircle)) = ((t + s : ℝ) : PhaseCircle) := by
      rw [QuotientAddGroup.mk_add]
    rw [hcoe, steinhausPhase, steinhausPhase, fourier_coe_apply, fourier_coe_apply,
      ← Complex.exp_add]
    congr 1
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp

/-- **The rotated one-circle Laplace transform is the unrotated one.** -/
theorem integral_exp_rot (r s : ℝ) :
    ∫ y : PhaseCircle, Real.exp (r * (steinhausPhase y * Complex.exp (-(s * Complex.I))).re)
        ∂AddCircle.haarAddCircle
      = steinhausLaplace r := by
  have hshift := MeasureTheory.integral_add_right_eq_self
    (μ := (AddCircle.haarAddCircle : Measure PhaseCircle))
    (fun y : PhaseCircle =>
      Real.exp (r * (steinhausPhase y * Complex.exp (-(s * Complex.I))).re))
    ((s : ℝ) : PhaseCircle)
  rw [← hshift, steinhausLaplace]
  refine integral_congr_ae ?_
  filter_upwards with y
  congr 2
  rw [steinhausPhase_add_coe, mul_assoc, ← Complex.exp_add]
  rw [show (s : ℂ) * Complex.I + -((s : ℂ) * Complex.I) = 0 by ring, Complex.exp_zero, mul_one]
  rw [steinhausProjection]

/-- **The rotated Laplace product.** -/
theorem integral_exp_steinhausRotProj {ι : Type*} [Fintype ι] (a : ι → ℝ) (r s : ℝ) :
    ∫ x : ι → PhaseCircle, Real.exp (r * steinhausRotProj a s x)
        ∂(Measure.pi fun _ : ι => AddCircle.haarAddCircle) =
      ∏ i, steinhausLaplace (r * a i) := by
  simp_rw [steinhausRotProj, Finset.mul_sum, Real.exp_sum]
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun i (y : PhaseCircle) =>
      Real.exp (r * (a i * (steinhausPhase y * Complex.exp (-(s * Complex.I))).re)))]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp_rw [← mul_assoc]
  exact integral_exp_rot (r * a i) s


/-- The rotated projection in polar form. -/
theorem rot_re_eq (z : ℂ) (s : ℝ) :
    (z * Complex.exp (-(s * Complex.I))).re = ‖z‖ * Real.cos (Complex.arg z - s) := by
  have hre : ‖z‖ * Real.cos (Complex.arg z) = z.re := Complex.norm_mul_cos_arg z
  have him : ‖z‖ * Real.sin (Complex.arg z) = z.im := Complex.norm_mul_sin_arg z
  rw [Real.cos_sub]
  have hexp : Complex.exp (-(s * Complex.I)) = Real.cos s - Real.sin s * Complex.I := by
    rw [show -((s : ℂ) * Complex.I) = ((-s : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hexp]
  simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  linear_combination (-Real.cos s) * hre + (-Real.sin s) * him

/-- **The rotational average of the exponential is the Bessel transform of the modulus.** -/
theorem steinhausLaplace_norm_eq_rot_average (z : ℂ) (t : ℝ) :
    steinhausLaplace (t * ‖z‖)
      = (1 / (2 * Real.pi)) *
        ∫ s in (0 : ℝ)..(2 * Real.pi), Real.exp (t * (z * Complex.exp (-(s * Complex.I))).re) := by
  have hper : Function.Periodic
      (fun u : ℝ => Real.exp (t * ‖z‖ * Real.cos u)) (2 * Real.pi) := by
    intro u
    simp only []
    rw [Real.cos_add_two_pi]
  have hcongr : (∫ s in (0 : ℝ)..(2 * Real.pi),
        Real.exp (t * (z * Complex.exp (-(s * Complex.I))).re))
      = ∫ s in (0 : ℝ)..(2 * Real.pi),
        Real.exp (t * ‖z‖ * Real.cos (Complex.arg z - s)) := by
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [rot_re_eq]
    ring_nf
  have hsub : (∫ s in (0 : ℝ)..(2 * Real.pi),
        Real.exp (t * ‖z‖ * Real.cos (Complex.arg z - s)))
      = ∫ u in (Complex.arg z - 2 * Real.pi)..(Complex.arg z),
        Real.exp (t * ‖z‖ * Real.cos u) := by
    have := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := 2 * Real.pi)
      (fun u : ℝ => Real.exp (t * ‖z‖ * Real.cos u)) (Complex.arg z)
    rw [this, sub_zero]
  have hshift : (∫ u in (Complex.arg z - 2 * Real.pi)..(Complex.arg z),
        Real.exp (t * ‖z‖ * Real.cos u))
      = ∫ u in (0 : ℝ)..(2 * Real.pi), Real.exp (t * ‖z‖ * Real.cos u) := by
    have h := hper.intervalIntegral_add_eq (Complex.arg z - 2 * Real.pi) 0
    rw [show Complex.arg z - 2 * Real.pi + 2 * Real.pi = Complex.arg z by ring, zero_add] at h
    exact h
  rw [hcongr, hsub, hshift, steinhausLaplace_eq_intervalIntegral]


theorem abs_steinhausRotProj_le {ι : Type*} [Fintype ι] (a : ι → ℝ) (s : ℝ)
    (x : ι → PhaseCircle) : |steinhausRotProj a s x| ≤ ∑ i, |a i| := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have hphase : ‖steinhausPhase (x i) * Complex.exp (-((s : ℂ) * Complex.I))‖ = 1 := by
    rw [norm_mul, norm_steinhausPhase, Complex.norm_exp]
    simp
  have hre : |(steinhausPhase (x i) * Complex.exp (-((s : ℂ) * Complex.I))).re| ≤ 1 := by
    rw [← hphase]
    exact Complex.abs_re_le_norm _
  nlinarith only [hre, abs_nonneg (a i)]

theorem continuous_steinhausRotProj {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Continuous fun p : (ι → PhaseCircle) × ℝ => steinhausRotProj a p.2 p.1 := by
  refine continuous_finsetSum _ fun i _ => ?_
  refine continuous_const.mul (Complex.continuous_re.comp ?_)
  exact ((continuous_steinhausPhase.comp ((continuous_apply i).comp continuous_fst)).mul
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_snd).mul
      continuous_const).neg))

/-- **The Bessel transform of the modulus integrates to the Laplace product.** -/
theorem integral_steinhausLaplace_norm {ι : Type*} [Fintype ι] (a : ι → ℝ) (t : ℝ) :
    ∫ x : ι → PhaseCircle, steinhausLaplace (t * ‖steinhausSum a x‖)
        ∂(Measure.pi fun _ : ι => AddCircle.haarAddCircle)
      = ∏ i, steinhausLaplace (t * a i) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set μ : Measure (ι → PhaseCircle) := Measure.pi fun _ : ι => AddCircle.haarAddCircle with hμ
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)) with hν
  set F : (ι → PhaseCircle) → ℝ → ℝ :=
    fun x s => Real.exp (t * steinhausRotProj a s x) with hF
  have hcont : Continuous (Function.uncurry F) := by
    rw [hF]
    exact Real.continuous_exp.comp (continuous_const.mul (continuous_steinhausRotProj a))
  have hbound : ∀ p : (ι → PhaseCircle) × ℝ,
      ‖Function.uncurry F p‖ ≤ Real.exp (|t| * ∑ i, |a i|) := by
    rintro ⟨x, s⟩
    rw [Function.uncurry_apply_pair, hF, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have h1 := abs_steinhausRotProj_le a s x
    have h2 : t * steinhausRotProj a s x ≤ |t| * |steinhausRotProj a s x| := by
      have := abs_mul t (steinhausRotProj a s x)
      have h3 := le_abs_self (t * steinhausRotProj a s x)
      linarith [h3, this.le, this.ge]
    have h4 : |t| * |steinhausRotProj a s x| ≤ |t| * ∑ i, |a i| :=
      mul_le_mul_of_nonneg_left h1 (abs_nonneg t)
    linarith
  have hint : Integrable (Function.uncurry F) (μ.prod ν) := by
    refine Integrable.mono' (integrable_const (Real.exp (|t| * ∑ i, |a i|)))
      hcont.aestronglyMeasurable ?_
    filter_upwards with p
    exact hbound p
  have hswap := MeasureTheory.integral_integral_swap hint
  have hstep : ∀ x : ι → PhaseCircle,
      steinhausLaplace (t * ‖steinhausSum a x‖) = (1 / (2 * Real.pi)) * ∫ s, F x s ∂ν := by
    intro x
    rw [steinhausLaplace_norm_eq_rot_average, intervalIntegral.integral_of_le hpi.le, hν]
    have heq : ∀ s ∈ Set.Ioc (0 : ℝ) (2 * Real.pi),
        Real.exp (t * (steinhausSum a x * Complex.exp (-((s : ℝ) * Complex.I))).re) = F x s := by
      intro s _
      simp only [hF]
      rw [steinhausRotProj_eq_re]
    rw [setIntegral_congr_fun (measurableSet_Ioc (a := (0 : ℝ)) (b := 2 * Real.pi)) heq]
  have hinner : ∀ s : ℝ, ∫ x, F x s ∂μ = ∏ i, steinhausLaplace (t * a i) := by
    intro s
    rw [hF, hμ]
    exact integral_exp_steinhausRotProj a t s
  calc ∫ x : ι → PhaseCircle, steinhausLaplace (t * ‖steinhausSum a x‖) ∂μ
      = ∫ x, (1 / (2 * Real.pi)) * ∫ s, F x s ∂ν ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with x
        exact hstep x
    _ = (1 / (2 * Real.pi)) * ∫ x, (∫ s, F x s ∂ν) ∂μ := integral_const_mul _ _
    _ = (1 / (2 * Real.pi)) * ∫ s, (∫ x, F x s ∂μ) ∂ν := by rw [hswap]
    _ = (1 / (2 * Real.pi)) * ∫ _s in Set.Ioc (0 : ℝ) (2 * Real.pi),
          ∏ i, steinhausLaplace (t * a i) := by
        rw [hν]
        congr 1
        exact setIntegral_congr_fun (measurableSet_Ioc (a := (0 : ℝ)) (b := 2 * Real.pi))
          fun s _ => hinner s
    _ = ∏ i, steinhausLaplace (t * a i) := by
        rw [setIntegral_const, measureReal_def, Real.volume_Ioc, sub_zero,
          ENNReal.toReal_ofReal hpi.le, smul_eq_mul]
        field_simp

end

end HTGeometry
