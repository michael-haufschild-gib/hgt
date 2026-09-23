import Mathlib.Analysis.Complex.MeanValue
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Circle averages of the Cauchy coefficients

The `n`-th Cauchy coefficient of a function on the circle of radius `R` about the origin is the
circle average of `z⁻ⁿ·f`, while the circle average of `zⁿ·f` vanishes for `n ≥ 1` whenever `f` is
holomorphic on the closed disc.  These are the two halves of the averaging argument behind
Carathéodory's coefficient inequality: the first identifies the coefficient with a negative-frequency
average, the second says the positive-frequency averages carry no information, so the coefficient is
an average of the real part alone.
-/

open Complex Metric

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The `n`-th Cauchy coefficient at the centre `0` on the circle of radius `R`. -/
def cauchyCoeff (f : ℂ → ℂ) (R : ℝ) (n : ℕ) : ℂ :=
  cauchyPowerSeries f 0 R n fun _ => 1

/-- **The Cauchy coefficient is the negative-frequency circle average.** -/
theorem cauchyCoeff_eq_circleAverage (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    cauchyCoeff f R n = Real.circleAverage (fun z : ℂ => (z⁻¹) ^ n * f z) 0 R := by
  rw [cauchyCoeff, cauchyPowerSeries_apply, Real.circleAverage_eq_circleIntegral (ne_of_gt hR)]
  congr 1
  refine circleIntegral.integral_congr (le_of_lt hR) fun z _ => ?_
  simp only [sub_zero, one_div, smul_eq_mul]
  ring

/-- The circle point in exponential form. -/
theorem circleMap_zero_eq (R θ : ℝ) :
    circleMap 0 R θ = (R : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  rw [circleMap]
  simp [Complex.exp_mul_I]

theorem diffContOnCl_pow_mul {f : ℂ → ℂ} {R : ℝ} (hf : DiffContOnCl ℂ f (ball 0 R)) (n : ℕ) :
    DiffContOnCl ℂ (fun z : ℂ => z ^ n * f z) (ball 0 R) :=
  ⟨((differentiable_pow n).differentiableOn).mul hf.differentiableOn,
   ((continuous_pow n).continuousOn).mul hf.continuousOn⟩

/-- **The positive-frequency circle averages of a holomorphic function vanish.** -/
theorem circleAverage_pow_mul_eq_zero {f : ℂ → ℂ} {R : ℝ}
    (hf : DiffContOnCl ℂ f (ball 0 |R|)) {n : ℕ} (hn : 1 ≤ n) :
    Real.circleAverage (fun z : ℂ => z ^ n * f z) 0 R = 0 := by
  rw [(diffContOnCl_pow_mul hf n).circleAverage, zero_pow (by omega : n ≠ 0), zero_mul]


/-! ## Elementary properties of the circle average -/

theorem circleAverage_conj (g : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    Real.circleAverage (fun z : ℂ => (starRingEnd ℂ) (g z)) c R
      = (starRingEnd ℂ) (Real.circleAverage g c R) := by
  rw [Real.circleAverage_def, Real.circleAverage_def, intervalIntegral.intervalIntegral_conj]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal]

theorem circleAverage_const_mul (a : ℂ) (g : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    Real.circleAverage (fun z : ℂ => a * g z) c R = a * Real.circleAverage g c R := by
  rw [Real.circleAverage_def, Real.circleAverage_def, intervalIntegral.integral_const_mul]
  simp only [Complex.real_smul]
  ring

theorem norm_circleAverage_le (g : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    ‖Real.circleAverage g c R‖
      ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ‖g (circleMap c R θ)‖ := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [Real.circleAverage_def, norm_smul]
  have hnorm : ‖((2 * Real.pi)⁻¹ : ℝ)‖ = (2 * Real.pi)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hnorm]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm hpi.le) (by positivity)


/-! ## Carathéodory's coefficient inequality -/

theorem inv_eq_conj_div {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ = R) :
    z⁻¹ = (starRingEnd ℂ) z / ((R : ℂ) ^ (2 : ℕ)) := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact (ne_of_gt hR) hz.symm
  have hmul : z * (starRingEnd ℂ) z = ((R : ℂ)) ^ (2 : ℕ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    push_cast
    ring
  have hRne : ((R : ℂ)) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (by exact_mod_cast ne_of_gt hR)
  rw [eq_div_iff hRne, inv_mul_eq_iff_eq_mul₀ hzne, ← hmul]

theorem continuousOn_closedBall_of_diffContOnCl {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R)) : ContinuousOn f (closedBall (0 : ℂ) R) := by
  have hcl : closure (ball (0 : ℂ) R) = closedBall 0 R := closure_ball 0 (ne_of_gt hR)
  rw [← hcl]
  exact hf.continuousOn

theorem continuous_circle_comp {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R)) :
    Continuous fun θ : ℝ => f (circleMap 0 R θ) := by
  refine (continuousOn_closedBall_of_diffContOnCl hR hf).comp_continuous
    (continuous_circleMap 0 R) fun θ => ?_
  exact sphere_subset_closedBall (circleMap_mem_sphere 0 hR.le θ)

theorem circleAverage_sub {g h : ℂ → ℂ} {R : ℝ}
    (hg : Continuous fun θ : ℝ => g (circleMap 0 R θ))
    (hh : Continuous fun θ : ℝ => h (circleMap 0 R θ)) :
    Real.circleAverage (fun z : ℂ => g z - h z) 0 R
      = Real.circleAverage g 0 R - Real.circleAverage h 0 R := by
  rw [Real.circleAverage_def, Real.circleAverage_def, Real.circleAverage_def,
    intervalIntegral.integral_sub (hg.intervalIntegrable 0 (2 * Real.pi))
      (hh.intervalIntegrable 0 (2 * Real.pi)), smul_sub]

/-- **The negative-frequency average of the conjugate vanishes.** -/
theorem circleAverage_inv_pow_mul_conj_eq_zero (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R)) {n : ℕ} (hn : 1 ≤ n) :
    Real.circleAverage (fun z : ℂ => (z⁻¹) ^ n * (starRingEnd ℂ) (f z)) 0 R = 0 := by
  have habs : |R| = R := abs_of_pos hR
  have hf' : DiffContOnCl ℂ f (ball 0 |R|) := by rwa [habs]
  have hzero := circleAverage_pow_mul_eq_zero hf' hn
  have hRne : ((R : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hR
  have hcongr : Real.circleAverage (fun z : ℂ => (z⁻¹) ^ n * (starRingEnd ℂ) (f z)) 0 R
      = Real.circleAverage
          (fun z : ℂ => (((R : ℂ)) ^ (2 * n))⁻¹ * (starRingEnd ℂ) (z ^ n * f z)) 0 R := by
    refine Real.circleAverage_congr_sphere fun z hz => ?_
    rw [habs] at hz
    have hznorm : ‖z‖ = R := by
      simpa using mem_sphere_zero_iff_norm.1 hz
    have hinv : z⁻¹ = (starRingEnd ℂ) z / ((R : ℂ) ^ (2 : ℕ)) := inv_eq_conj_div hR hznorm
    rw [hinv, div_pow, map_mul, map_pow, ← pow_mul, mul_comm 2 n, pow_mul]
    field_simp
  rw [hcongr, circleAverage_const_mul, circleAverage_conj, hzero, map_zero, mul_zero]


theorem circleMap_ne_zero_caratheodoryCoefficient {R : ℝ} (hR : 0 < R) (θ : ℝ) : circleMap 0 R θ ≠ 0 := by
  intro h
  have hmem := circleMap_mem_sphere 0 hR.le θ
  rw [h] at hmem
  have : (0 : ℝ) = R := by simpa using mem_sphere_zero_iff_norm.1 hmem
  exact (ne_of_gt hR) this.symm

theorem circleAverage_re (g : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hg : Continuous fun θ : ℝ => g (circleMap c R θ)) :
    Real.circleAverage (fun z : ℂ => ((g z).re : ℝ)) c R = (Real.circleAverage g c R).re := by
  have hint : (∫ θ in (0 : ℝ)..2 * Real.pi, ((g (circleMap c R θ)).re : ℝ))
      = (∫ θ in (0 : ℝ)..2 * Real.pi, g (circleMap c R θ)).re := by
    have h := ContinuousLinearMap.intervalIntegral_comp_comm (μ := MeasureTheory.volume)
      Complex.reCLM (hg.intervalIntegrable 0 (2 * Real.pi))
    simpa using h
  rw [Real.circleAverage_def, Real.circleAverage_def, hint]
  simp

/-- **The Cauchy coefficient is twice the negative-frequency average of the real part.** -/
theorem cauchyCoeff_eq_two_mul_re_average (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R)) {n : ℕ} (hn : 1 ≤ n) :
    cauchyCoeff f R n
      = 2 * Real.circleAverage (fun z : ℂ => (z⁻¹) ^ n * ((f z).re : ℂ)) 0 R := by
  have hcont := continuous_circle_comp hR hf
  have hinvcont : Continuous fun θ : ℝ => ((circleMap 0 R θ)⁻¹) ^ n :=
    (((continuous_circleMap 0 R).inv₀ (circleMap_ne_zero_caratheodoryCoefficient hR))).pow n
  have hg1 : Continuous fun θ : ℝ =>
      2 * (((circleMap 0 R θ)⁻¹) ^ n * (((f (circleMap 0 R θ)).re : ℝ) : ℂ)) :=
    continuous_const.mul (hinvcont.mul
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hcont)))
  have hg2 : Continuous fun θ : ℝ =>
      ((circleMap 0 R θ)⁻¹) ^ n * (starRingEnd ℂ) (f (circleMap 0 R θ)) :=
    hinvcont.mul (Complex.continuous_conj.comp hcont)
  have hsplit : (fun z : ℂ => (z⁻¹) ^ n * f z)
      = fun z : ℂ => 2 * ((z⁻¹) ^ n * (((f z).re : ℝ) : ℂ))
          - (z⁻¹) ^ n * (starRingEnd ℂ) (f z) := by
    funext z
    have hfz : (2 : ℂ) * (((f z).re : ℝ) : ℂ) - (starRingEnd ℂ) (f z) = f z := by
      apply Complex.ext
      · simp
        ring
      · simp
    calc (z⁻¹) ^ n * f z
        = (z⁻¹) ^ n * (2 * (((f z).re : ℝ) : ℂ) - (starRingEnd ℂ) (f z)) := by rw [hfz]
      _ = 2 * ((z⁻¹) ^ n * (((f z).re : ℝ) : ℂ))
            - (z⁻¹) ^ n * (starRingEnd ℂ) (f z) := by ring
  rw [cauchyCoeff_eq_circleAverage f hR n, hsplit, circleAverage_sub hg1 hg2,
    circleAverage_inv_pow_mul_conj_eq_zero f hR hf hn, sub_zero, circleAverage_const_mul]

/-- **Carathéodory's coefficient inequality.**  A holomorphic function on the closed disc of radius
`R` with nonnegative real part on the boundary circle has Cauchy coefficients bounded by twice its
real part at the centre. -/
theorem norm_cauchyCoeff_mul_pow_le (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R))
    (hpos : ∀ z ∈ sphere (0 : ℂ) R, 0 ≤ (f z).re) {n : ℕ} (hn : 1 ≤ n) :
    ‖cauchyCoeff f R n‖ * R ^ n ≤ 2 * (f 0).re := by
  have habs : |R| = R := abs_of_pos hR
  have hcont := continuous_circle_comp hR hf
  have hmvp : Real.circleAverage f 0 R = f 0 := by
    have hf' : DiffContOnCl ℂ f (ball 0 |R|) := by rwa [habs]
    exact hf'.circleAverage
  have hre : Real.circleAverage (fun z : ℂ => ((f z).re : ℝ)) 0 R = (f 0).re := by
    rw [circleAverage_re f 0 R hcont, hmvp]
  have hreInt : (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ((f (circleMap 0 R θ)).re : ℝ)
      = (f 0).re := by
    have hdef : Real.circleAverage (fun z : ℂ => ((f z).re : ℝ)) 0 R
        = (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..2 * Real.pi, ((f (circleMap 0 R θ)).re : ℝ) :=
      Real.circleAverage_def
    rw [smul_eq_mul] at hdef
    rw [← hdef, hre]
  have hbound := norm_circleAverage_le (fun z : ℂ => (z⁻¹) ^ n * (((f z).re : ℝ) : ℂ)) 0 R
  have hpt : ∀ θ : ℝ,
      ‖((circleMap 0 R θ)⁻¹) ^ n * (((f (circleMap 0 R θ)).re : ℝ) : ℂ)‖
        = (R ^ n)⁻¹ * ((f (circleMap 0 R θ)).re : ℝ) := by
    intro θ
    have hnorm : ‖circleMap 0 R θ‖ = R := by
      simpa using mem_sphere_zero_iff_norm.1 (circleMap_mem_sphere 0 hR.le θ)
    have hposθ : 0 ≤ (f (circleMap 0 R θ)).re := hpos _ (circleMap_mem_sphere 0 hR.le θ)
    rw [norm_mul, norm_pow, norm_inv, hnorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hposθ, ← inv_pow]
  simp only [hpt] at hbound
  rw [intervalIntegral.integral_const_mul] at hbound
  have hfinal : ‖Real.circleAverage (fun z : ℂ => (z⁻¹) ^ n * (((f z).re : ℝ) : ℂ)) 0 R‖
      ≤ (R ^ n)⁻¹ * (f 0).re := by
    refine le_trans hbound (le_of_eq ?_)
    rw [← hreInt]
    ring
  have hEq := cauchyCoeff_eq_two_mul_re_average f hR hf hn
  have hstep : ‖cauchyCoeff f R n‖
      = 2 * ‖Real.circleAverage (fun z : ℂ => (z⁻¹) ^ n * (((f z).re : ℝ) : ℂ)) 0 R‖ := by
    rw [hEq, norm_mul]
    norm_num
  have hRpow : (0 : ℝ) < R ^ n := by positivity
  have hRne : (R ^ n : ℝ) ≠ 0 := ne_of_gt hRpow
  rw [hstep]
  calc 2 * ‖Real.circleAverage (fun z : ℂ => (z⁻¹) ^ n * (((f z).re : ℝ) : ℂ)) 0 R‖ * R ^ n
      ≤ 2 * ((R ^ n)⁻¹ * (f 0).re) * R ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ hRpow.le
        linarith [hfinal]
    _ = 2 * (f 0).re := by field_simp

end GaloisForLFunctions.HTGeometry

end
