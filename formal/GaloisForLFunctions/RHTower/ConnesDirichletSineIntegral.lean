import Mathlib

/-!
# The Dirichlet integral `∫_0^∞ sin t / t dt = π/2`

mathlib has no cosine or sine integral, and the corpus search turns up nothing either, so this
classical improper integral is built here from scratch.  It is the analytic gate for the Fourier
transform of `sgn`, hence for the identification of §V of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068,

between `−∫ ĝ(u) log|u| du` and the log-regularised principal value.

The proof is the elementary Laplace-kernel one: `1/t = ∫_0^∞ e^{-ts} ds` for `t > 0`, Fubini on
the finite rectangle `(0,R] × (0,∞)` (legitimate because `|sin t| ≤ t` makes the double integral
bounded by `R`), the explicit primitive of `e^{-ts} sin t`, and the elementary bound
`|(cos R + s sin R)/(1+s²)| ≤ 3/2` for the error term, which therefore is `O(1/R)`.
-/

open MeasureTheory Set Filter Topology Real

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The primitive of `e^{-ts} sin t` in `t`. -/
theorem connes_hasDerivAt_dampedSine (s t : ℝ) :
    HasDerivAt (fun t : ℝ =>
        -Real.exp (-(t * s)) * (Real.cos t + s * Real.sin t) / (1 + s ^ (2 : ℕ)))
      (Real.exp (-(t * s)) * Real.sin t) t := by
  have hA : (1 : ℝ) + s ^ (2 : ℕ) ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t : ℝ => -(t * s)) (-s) t := by
    have h := (hasDerivAt_id t).mul_const s
    rw [one_mul] at h
    exact h.neg
  have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(t * s)))
      (Real.exp (-(t * s)) * (-s)) t := (Real.hasDerivAt_exp _).comp t h1
  have h3 : HasDerivAt (fun t : ℝ => Real.cos t + s * Real.sin t)
      (-Real.sin t + s * Real.cos t) t := (Real.hasDerivAt_cos t).add
        ((Real.hasDerivAt_sin t).const_mul s)
  have h4 : HasDerivAt (fun t : ℝ => -Real.exp (-(t * s)) * (Real.cos t + s * Real.sin t))
      (-(Real.exp (-(t * s)) * (-s)) * (Real.cos t + s * Real.sin t)
        + -Real.exp (-(t * s)) * (-Real.sin t + s * Real.cos t)) t := h2.neg.mul h3
  have h5 := h4.div_const (1 + s ^ (2 : ℕ))
  refine h5.congr_deriv ?_
  rw [div_eq_iff hA]
  ring

theorem connes_intervalIntegral_sin_mul_exp (s R : ℝ) :
    (∫ t in (0 : ℝ)..R, Real.exp (-(t * s)) * Real.sin t)
      = (1 - Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R)) / (1 + s ^ (2 : ℕ)) := by
  have hA : (1 : ℝ) + s ^ (2 : ℕ) ≠ 0 := by positivity
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) R,
      HasDerivAt (fun t : ℝ =>
        -Real.exp (-(t * s)) * (Real.cos t + s * Real.sin t) / (1 + s ^ (2 : ℕ)))
        (Real.exp (-(t * s)) * Real.sin t) t := fun t _ => connes_hasDerivAt_dampedSine s t
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-(t * s)) * Real.sin t)
      volume 0 R := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [zero_mul, neg_zero, Real.exp_zero, Real.cos_zero, Real.sin_zero, mul_zero,
    add_zero]
  field_simp
  ring

/-- `∫_0^∞ ds/(1+s²) = π/2`. -/
theorem connes_integral_inv_one_add_sq_Ioi :
    (∫ s in Ioi (0 : ℝ), (1 + s ^ (2 : ℕ))⁻¹) = Real.pi / 2 := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt Real.arctan (1 + x ^ (2 : ℕ))⁻¹ x := by
    intro x _
    simpa using Real.hasDerivAt_arctan x
  have hint : IntegrableOn (fun x : ℝ => (1 + x ^ (2 : ℕ))⁻¹) (Ioi (0 : ℝ)) :=
    (integrable_inv_one_add_sq).integrableOn
  have htend : Tendsto Real.arctan atTop (𝓝 (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto
    (f := Real.arctan) (f' := fun x : ℝ => (1 + x ^ (2 : ℕ))⁻¹) (a := (0 : ℝ))
    (Real.continuous_arctan.continuousWithinAt) hderiv hint htend
  simpa using h

/-- `∫_0^∞ e^{-t s} ds = 1/t` for `t > 0`. -/
theorem connes_integral_exp_neg_mul_Ioi {t : ℝ} (ht : 0 < t) :
    (∫ s in Ioi (0 : ℝ), Real.exp (-(t * s))) = 1 / t := by
  have h := integral_comp_mul_left_Ioi (fun x : ℝ => Real.exp (-x)) 0 ht
  rw [mul_zero] at h
  rw [show (fun s : ℝ => Real.exp (-(t * s))) = fun s : ℝ => (fun x : ℝ => Real.exp (-x)) (t * s)
    from rfl, h, integral_exp_neg_Ioi_zero, smul_eq_mul, mul_one, one_div]

/-- **The Laplace representation.**  `sin t / t = ∫_0^∞ sin t · e^{-ts} ds` for `t > 0`. -/
theorem connes_sinDiv_eq_laplace {t : ℝ} (ht : 0 < t) :
    Real.sin t / t = ∫ s in Ioi (0 : ℝ), Real.sin t * Real.exp (-(t * s)) := by
  rw [MeasureTheory.integral_const_mul, connes_integral_exp_neg_mul_Ioi ht]
  field_simp

/-- The inner Laplace integral of the absolute value. -/
theorem connes_integral_abs_sin_mul_exp {t : ℝ} (ht : 0 < t) :
    (∫ s in Ioi (0 : ℝ), ‖Real.sin t * Real.exp (-(t * s))‖) = |Real.sin t| / t := by
  have hcongr : ∀ s ∈ Ioi (0 : ℝ), ‖Real.sin t * Real.exp (-(t * s))‖
      = |Real.sin t| * Real.exp (-(t * s)) := by
    intro s _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr,
    MeasureTheory.integral_const_mul, connes_integral_exp_neg_mul_Ioi ht]
  field_simp

theorem connes_laplaceKernel_integrable (R : ℝ) :
    Integrable (Function.uncurry fun t s : ℝ => Real.sin t * Real.exp (-(t * s)))
      ((volume.restrict (Ioc (0 : ℝ) R)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hcont : Continuous (Function.uncurry fun t s : ℝ => Real.sin t * Real.exp (-(t * s))) := by
    unfold Function.uncurry
    fun_prop
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun t s : ℝ => Real.sin t * Real.exp (-(t * s)))
      ((volume.restrict (Ioc (0 : ℝ) R)).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    hcont.aestronglyMeasurable
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) R)) := by
    constructor
    simpa using (measure_Ioc_lt_top (μ := (volume : Measure ℝ)) (a := (0 : ℝ)) (b := R))
  rw [MeasureTheory.integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : (0 : ℝ) < t := ht.1
    have hbase := (exp_neg_integrableOn_Ioi (0 : ℝ) ht0).const_mul (Real.sin t)
    have hfun : (fun s : ℝ => Real.sin t * Real.exp (-t * s))
        = fun s : ℝ => Real.sin t * Real.exp (-(t * s)) := by
      funext s
      rw [neg_mul]
    rw [hfun] at hbase
    exact hbase
  · have hmeasnorm := hmeas.norm.integral_prod_right'
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeasnorm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : (0 : ℝ) < t := ht.1
    show ‖∫ y in Ioi (0 : ℝ), ‖Real.sin t * Real.exp (-(t * y))‖‖ ≤ (1 : ℝ)
    rw [Real.norm_eq_abs, connes_integral_abs_sin_mul_exp ht0,
      abs_of_nonneg (by positivity), div_le_one ht0]
    calc |Real.sin t| ≤ |t| := Real.abs_sin_le_abs
      _ = t := abs_of_pos ht0

/-- **The Fubini step.**  The truncated Dirichlet integral as a Laplace-side integral. -/
theorem connes_sinDiv_fubini {R : ℝ} (hR : 0 < R) :
    (∫ t in Ioc (0 : ℝ) R, Real.sin t / t)
      = ∫ s in Ioi (0 : ℝ),
          (1 - Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R)) / (1 + s ^ (2 : ℕ)) := by
  have h1 : (∫ t in Ioc (0 : ℝ) R, Real.sin t / t)
      = ∫ t in Ioc (0 : ℝ) R, ∫ s in Ioi (0 : ℝ), Real.sin t * Real.exp (-(t * s)) :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      fun t ht => connes_sinDiv_eq_laplace ht.1
  rw [h1, MeasureTheory.integral_integral_swap (connes_laplaceKernel_integrable R)]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  have hclosed := connes_intervalIntegral_sin_mul_exp s R
  rw [intervalIntegral.integral_of_le hR.le] at hclosed
  rw [← hclosed]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  ring

/-- The elementary bound on the error density. -/
theorem connes_dirichlet_error_density_le {s R : ℝ} (hs : 0 ≤ s) :
    |(Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ))| ≤ 3 / 2 := by
  have hA : (0 : ℝ) < 1 + s ^ (2 : ℕ) := by positivity
  have h1 : |Real.cos R + s * Real.sin R| ≤ 1 + s := by
    have hc := Real.abs_cos_le_one R
    have hsn := Real.abs_sin_le_one R
    calc |Real.cos R + s * Real.sin R| ≤ |Real.cos R| + |s * Real.sin R| := abs_add_le _ _
      _ = |Real.cos R| + s * |Real.sin R| := by rw [abs_mul, abs_of_nonneg hs]
      _ ≤ 1 + s * 1 := by
          refine add_le_add hc ?_
          exact mul_le_of_le_one_right hs hsn |>.trans (le_of_eq (mul_one s).symm)
      _ = 1 + s := by ring
  rw [abs_div, abs_of_pos hA, div_le_iff₀ hA]
  nlinarith [sq_nonneg (s - 1), sq_nonneg s]

theorem connes_dirichlet_error_integrable {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun s : ℝ =>
      Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ))) (Ioi (0 : ℝ)) := by
  have hmaj : IntegrableOn (fun s : ℝ => (3 / 2 : ℝ) * Real.exp (-(R * s))) (Ioi (0 : ℝ)) := by
    have hbase := (exp_neg_integrableOn_Ioi (0 : ℝ) hR).const_mul (3 / 2 : ℝ)
    have hfun : (fun s : ℝ => (3 / 2 : ℝ) * Real.exp (-R * s))
        = fun s : ℝ => (3 / 2 : ℝ) * Real.exp (-(R * s)) := by
      funext s
      rw [neg_mul]
    rw [hfun] at hbase
    exact hbase
  refine Integrable.mono' hmaj ?_ ?_
  · refine AEStronglyMeasurable.restrict ?_
    refine Continuous.aestronglyMeasurable ?_
    have hden : Continuous fun s : ℝ => (1 : ℝ) + s ^ (2 : ℕ) := by fun_prop
    have hnum : Continuous fun s : ℝ =>
        Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R) := by fun_prop
    exact hnum.div hden (fun s => by positivity)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
    have heq : Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ))
        = Real.exp (-(R * s)) * ((Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ))) := by ring
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul_of_nonneg_left (connes_dirichlet_error_density_le (R := R) hs0)
      (le_of_lt (Real.exp_pos (-(R * s))))
    calc Real.exp (-(R * s)) * |(Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ))|
        ≤ Real.exp (-(R * s)) * (3 / 2) := h
      _ = (3 / 2 : ℝ) * Real.exp (-(R * s)) := by ring

theorem connes_dirichlet_error_bound {R : ℝ} (hR : 0 < R) :
    ‖∫ s in Ioi (0 : ℝ),
        Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ))‖ ≤ (3 / 2) / R := by
  have hmaj : IntegrableOn (fun s : ℝ => (3 / 2 : ℝ) * Real.exp (-(R * s))) (Ioi (0 : ℝ)) := by
    have hbase := (exp_neg_integrableOn_Ioi (0 : ℝ) hR).const_mul (3 / 2 : ℝ)
    have hfun : (fun s : ℝ => (3 / 2 : ℝ) * Real.exp (-R * s))
        = fun s : ℝ => (3 / 2 : ℝ) * Real.exp (-(R * s)) := by
      funext s
      rw [neg_mul]
    rw [hfun] at hbase
    exact hbase
  have hle : ∀ s ∈ Ioi (0 : ℝ),
      ‖Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ))‖
        ≤ (3 / 2 : ℝ) * Real.exp (-(R * s)) := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := le_of_lt hs
    have heq : Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ))
        = Real.exp (-(R * s)) * ((Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ))) := by ring
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul_of_nonneg_left (connes_dirichlet_error_density_le (R := R) hs0)
      (le_of_lt (Real.exp_pos (-(R * s))))
    calc Real.exp (-(R * s)) * |(Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ))|
        ≤ Real.exp (-(R * s)) * (3 / 2) := h
      _ = (3 / 2 : ℝ) * Real.exp (-(R * s)) := by ring
  have hFint := connes_dirichlet_error_integrable hR
  calc ‖∫ s in Ioi (0 : ℝ),
        Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ))‖
      ≤ ∫ s in Ioi (0 : ℝ),
          ‖Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioi (0 : ℝ), (3 / 2 : ℝ) * Real.exp (-(R * s)) :=
        MeasureTheory.setIntegral_mono_on hFint.norm hmaj measurableSet_Ioi hle
    _ = (3 / 2 : ℝ) / R := by
        rw [MeasureTheory.integral_const_mul, connes_integral_exp_neg_mul_Ioi hR]
        ring

/-- **The truncated Dirichlet integral.** -/
theorem connes_dirichlet_truncated {R : ℝ} (hR : 0 < R) :
    (∫ t in (0 : ℝ)..R, Real.sin t / t)
      = Real.pi / 2
        - ∫ s in Ioi (0 : ℝ),
            Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ)) := by
  rw [intervalIntegral.integral_of_le hR.le, connes_sinDiv_fubini hR]
  have hsplit : ∀ s ∈ Ioi (0 : ℝ),
      (1 - Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R)) / (1 + s ^ (2 : ℕ))
        = (1 + s ^ (2 : ℕ))⁻¹
          - Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ)) := by
    intro s _
    have h : (1 : ℝ) + s ^ (2 : ℕ) ≠ 0 := by positivity
    field_simp
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hsplit,
    MeasureTheory.integral_sub (integrable_inv_one_add_sq).integrableOn
      (connes_dirichlet_error_integrable hR),
    connes_integral_inv_one_add_sq_Ioi]

/-- **The Dirichlet integral.**  `∫_0^∞ sin t / t dt = π/2`. -/
theorem connes_dirichlet_integral :
    Tendsto (fun R : ℝ => ∫ t in (0 : ℝ)..R, Real.sin t / t) atTop (𝓝 (Real.pi / 2)) := by
  have hbound : Tendsto (fun R : ℝ => (3 / 2 : ℝ) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hE : Tendsto (fun R : ℝ =>
      ∫ s in Ioi (0 : ℝ), Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ)))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact connes_dirichlet_error_bound hR
  have hmain : Tendsto (fun R : ℝ => Real.pi / 2 -
      ∫ s in Ioi (0 : ℝ), Real.exp (-(R * s)) * (Real.cos R + s * Real.sin R) / (1 + s ^ (2 : ℕ)))
      atTop (𝓝 (Real.pi / 2)) := by
    simpa using (tendsto_const_nhds (x := Real.pi / 2) (α := ℝ) (f := atTop)).sub hE
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  exact (connes_dirichlet_truncated hR).symm

end

end GaloisForLFunctions.RHTower
