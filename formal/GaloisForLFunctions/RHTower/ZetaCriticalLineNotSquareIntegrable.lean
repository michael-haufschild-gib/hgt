import GaloisForLFunctions.RHTower.FractionalPartZeta
import GaloisForLFunctions.RHTower.BurnolCoPoissonBerezinFaithful
import Mathlib.Analysis.Fourier.Inversion

/-!
# The fractional-part carrier of the critical line

The function `phi y = frac (exp y) * exp (-y/2)` is the logarithmic carrier of the fractional-part
Mellin identity: after the substitution `x = exp y` its Fourier transform along the critical line
is `-zeta w / w`.  This module builds the carrier, records the substitution identity that turns a
Mellin integrand on the ray into the carrier on the line, and proves that the carrier is both
integrable and square integrable.
-/

open Complex Real MeasureTheory Set Filter Topology FourierTransform FourierTransformInv

noncomputable section

namespace RHTower

/-- Logarithmic carrier of the fractional part. -/
def fractLogCarrier (y : ℝ) : ℂ :=
  ((Int.fract (Real.exp y) : ℝ) : ℂ) * ((Real.exp (-(y / 2)) : ℝ) : ℂ)

theorem exp_mul_rpow_neg_three_halves (y : ℝ) :
    Real.exp y * Real.exp y ^ (-(3 / 2 : ℝ)) = Real.exp (-(y / 2)) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp, ← Real.exp_add]
  congr 1
  ring

/-- The carrier is the logarithmic substitution of the Mellin integrand at the critical abscissa
`3/2` of the fractional part. -/
theorem fractLogCarrier_eq_exp_smul (y : ℝ) :
    fractLogCarrier y =
      Real.exp y • (((Int.fract (Real.exp y) : ℝ) : ℂ) *
        ((Real.exp y ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ)) := by
  rw [fractLogCarrier, Complex.real_smul, ← exp_mul_rpow_neg_three_halves y]
  push_cast
  ring

/-- Square modulus of the carrier is the logarithmic substitution of the squared Mellin
integrand. -/
theorem norm_sq_fractLogCarrier_eq_exp_smul (y : ℝ) :
    ‖fractLogCarrier y‖ ^ 2 =
      Real.exp y • (Int.fract (Real.exp y) ^ 2 * Real.exp y ^ (-(2 : ℝ))) := by
  have hpos : (0 : ℝ) < Real.exp y := Real.exp_pos y
  have hfr : 0 ≤ Int.fract (Real.exp y) := Int.fract_nonneg _
  have hreal : Real.exp y * Real.exp y ^ (-(2 : ℝ)) = Real.exp (-(y / 2)) ^ 2 := by
    rw [Real.rpow_def_of_pos hpos, Real.log_exp, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [fractLogCarrier, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hfr, abs_of_nonneg (Real.exp_pos _).le, mul_pow,
    smul_eq_mul, ← mul_assoc, mul_comm (Real.exp y), mul_assoc, hreal]


/-- **The carrier is integrable.**  Its logarithmic substitution is the Mellin integrand of the
fractional part at abscissa `1/2`, which the corpus already knows to be integrable on the ray. -/
theorem integrable_fractLogCarrier : Integrable fractLogCarrier volume := by
  have hbase : IntegrableOn
      (fun u : ℝ => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-(((1 : ℂ) / 2) + 1))) (Ioi 0) :=
    integrableOn_Ioi_zero_fract_cpow (by norm_num) (by norm_num)
  rw [integrableOn_Ioi_iff_integrable_exp_smul] at hbase
  refine (integrable_congr ?_).mp hbase
  filter_upwards with t
  rw [fractLogCarrier_eq_exp_smul]
  congr 2
  rw [show (-(((1 : ℂ) / 2) + 1)) = (((-(3 / 2 : ℝ)) : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_cpow (Real.exp_pos t).le]


/-! ## The Fourier transform of the carrier -/

/-- The critical abscissa attached to a Fourier frequency. -/
def criticalAbscissa (xi : ℝ) : ℂ := 1 / 2 + ((2 * Real.pi * xi : ℝ) : ℂ) * Complex.I

@[simp] theorem criticalAbscissa_re (xi : ℝ) : (criticalAbscissa xi).re = 1 / 2 := by
  simp [criticalAbscissa]

@[simp] theorem criticalAbscissa_im (xi : ℝ) : (criticalAbscissa xi).im = 2 * Real.pi * xi := by
  simp [criticalAbscissa]

theorem criticalAbscissa_ne_zero (xi : ℝ) : criticalAbscissa xi ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [criticalAbscissa_re] at this
  norm_num at this

theorem continuous_criticalAbscissa : Continuous criticalAbscissa := by
  unfold criticalAbscissa
  fun_prop

/-- **The Fourier transform of the fractional-part carrier.**  It is the completed Mellin quotient
`- zeta w / w` read along the critical line. -/
theorem fourier_fractLogCarrier (xi : ℝ) :
    𝓕 fractLogCarrier xi = -(riemannZeta (criticalAbscissa xi) / criticalAbscissa xi) := by
  have hw0 : 0 < (criticalAbscissa xi).re := by rw [criticalAbscissa_re]; norm_num
  have hw1 : (criticalAbscissa xi).re < 1 := by rw [criticalAbscissa_re]; norm_num
  rw [Real.fourier_eq, ← integral_Ioi_zero_fract_cpow hw0 hw1,
    integral_Ioi_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have hne : ((Real.exp t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
  have hlog : Complex.log ((Real.exp t : ℝ) : ℂ) = (t : ℂ) := by
    rw [← Complex.ofReal_log hpos.le, Real.log_exp]
  have hcpow : ((Real.exp t : ℝ) : ℂ) ^ (-(criticalAbscissa xi + 1)) =
      Complex.exp ((t : ℂ) * (-(criticalAbscissa xi + 1))) := by
    rw [Complex.cpow_def_of_ne_zero hne, hlog]
  have hinner : (inner ℝ t xi : ℝ) = t * xi := inner_apply t xi
  have hkey : Complex.exp (((2 * Real.pi * -(t * xi) : ℝ) : ℂ) * Complex.I) *
        ((Real.exp (-(t / 2)) : ℝ) : ℂ) =
      ((Real.exp t : ℝ) : ℂ) * Complex.exp ((t : ℂ) * (-(criticalAbscissa xi + 1))) := by
    rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [criticalAbscissa]
    push_cast
    ring
  rw [hcpow, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, fractLogCarrier,
    Complex.real_smul, hinner]
  rw [show Complex.exp (((2 * Real.pi * -(t * xi) : ℝ) : ℂ) * Complex.I) *
      (((Int.fract (Real.exp t) : ℝ) : ℂ) * ((Real.exp (-(t / 2)) : ℝ) : ℂ)) =
      ((Int.fract (Real.exp t) : ℝ) : ℂ) *
        (Complex.exp (((2 * Real.pi * -(t * xi) : ℝ) : ℂ) * Complex.I) *
          ((Real.exp (-(t / 2)) : ℝ) : ℂ)) from by ring]
  rw [hkey]
  ring

/-! ## The reciprocal abscissa is square integrable -/

theorem memLp_inv_criticalAbscissa :
    MemLp (fun xi : ℝ => (criticalAbscissa xi)⁻¹) 2 volume := by
  have hmeas : AEStronglyMeasurable (fun xi : ℝ => (criticalAbscissa xi)⁻¹) volume := by
    refine (Continuous.aestronglyMeasurable ?_)
    exact continuous_criticalAbscissa.inv₀ criticalAbscissa_ne_zero
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hbound : Integrable (fun xi : ℝ => 4 * (1 + xi ^ 2)⁻¹) volume :=
    (integrable_inv_one_add_sq).const_mul 4
  refine Integrable.mono' hbound (hmeas.norm.pow 2) ?_
  filter_upwards with xi
  have hnormsq : ‖criticalAbscissa xi‖ ^ 2 = 1 / 4 + (2 * Real.pi * xi) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, criticalAbscissa_re,
      criticalAbscissa_im]
    ring
  have hpos : (0 : ℝ) < ‖criticalAbscissa xi‖ :=
    norm_pos_iff.mpr (criticalAbscissa_ne_zero xi)
  have hpi : (1 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
    nlinarith [Real.pi_gt_three]
  have hlower : (1 / 4) * (1 + xi ^ 2) ≤ ‖criticalAbscissa xi‖ ^ 2 := by
    rw [hnormsq]
    nlinarith [sq_nonneg xi, hpi]
  have hinvsq : ‖(criticalAbscissa xi)⁻¹‖ ^ 2 = (‖criticalAbscissa xi‖ ^ 2)⁻¹ := by
    rw [norm_inv, inv_pow]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hinvsq]
  have h1 : (0 : ℝ) < 1 / 4 * (1 + xi ^ 2) := by positivity
  calc (‖criticalAbscissa xi‖ ^ 2)⁻¹ ≤ (1 / 4 * (1 + xi ^ 2))⁻¹ := inv_anti₀ h1 hlower
    _ = 4 * (1 + xi ^ 2)⁻¹ := by field_simp


/-! ## Integrability of the transform under the square-integrability hypothesis -/

theorem integrable_fourier_fractLogCarrier
    (h : MemLp (fun xi : ℝ => riemannZeta (criticalAbscissa xi)) 2 volume) :
    Integrable (𝓕 fractLogCarrier) volume := by
  have hmul : Integrable ((fun xi : ℝ => riemannZeta (criticalAbscissa xi)) *
      fun xi : ℝ => (criticalAbscissa xi)⁻¹) volume :=
    h.integrable_mul memLp_inv_criticalAbscissa
  refine hmul.neg.congr ?_
  filter_upwards with xi
  rw [fourier_fractLogCarrier]
  simp [Pi.mul_apply, div_eq_mul_inv]

theorem continuous_fourierInv_of_integrable {g : ℝ → ℂ} (hg : Integrable g volume) :
    Continuous (𝓕⁻ g) := by
  have hrfl : (𝓕⁻ g) = VectorFourier.fourierIntegral 𝐞 volume (-innerₗ ℝ) g := rfl
  rw [hrfl]
  refine VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar ?_ hg
  have : (fun p : ℝ × ℝ => ((-innerₗ ℝ) p.1) p.2) = fun p : ℝ × ℝ => -(p.1 * p.2) := by
    funext p
    simp [innerₗ]
    ring
  rw [this]
  fun_prop

/-! ## The explicit two-sided values of the carrier at `log 2` -/

theorem fract_eq_sub_of_mem_Ioo {x : ℝ} {n : ℤ} (h : (n : ℝ) < x) (h' : x < n + 1) :
    Int.fract x = x - n := by
  rw [Int.fract, Int.floor_eq_iff.mpr ⟨h.le, h'⟩]

theorem fractLogCarrier_eq_left {y : ℝ} (hy0 : 0 < y) (hy : y < Real.log 2) :
    fractLogCarrier y = ((Real.exp y - 1 : ℝ) : ℂ) * ((Real.exp (-(y / 2)) : ℝ) : ℂ) := by
  have h1 : (1 : ℝ) < Real.exp y := by
    have := Real.exp_lt_exp.mpr hy0
    rwa [Real.exp_zero] at this
  have h2 : Real.exp y < 2 := by
    have := Real.exp_lt_exp.mpr hy
    rwa [Real.exp_log (by norm_num)] at this
  rw [fractLogCarrier, fract_eq_sub_of_mem_Ioo (n := 1) (by exact_mod_cast h1) (by push_cast; linarith)]
  norm_num

theorem fractLogCarrier_eq_right {y : ℝ} (hy : Real.log 2 < y) (hy3 : y < Real.log 3) :
    fractLogCarrier y = ((Real.exp y - 2 : ℝ) : ℂ) * ((Real.exp (-(y / 2)) : ℝ) : ℂ) := by
  have h1 : (2 : ℝ) < Real.exp y := by
    have := Real.exp_lt_exp.mpr hy
    rwa [Real.exp_log (by norm_num)] at this
  have h2 : Real.exp y < 3 := by
    have := Real.exp_lt_exp.mpr hy3
    rwa [Real.exp_log (by norm_num)] at this
  rw [fractLogCarrier, fract_eq_sub_of_mem_Ioo (n := 2) (by exact_mod_cast h1) (by push_cast; linarith)]
  norm_num

theorem continuousAt_fractLogCarrier_left {y : ℝ} (hy0 : 0 < y) (hy : y < Real.log 2) :
    ContinuousAt fractLogCarrier y := by
  have hcont : ContinuousAt
      (fun z : ℝ => ((Real.exp z - 1 : ℝ) : ℂ) * ((Real.exp (-(z / 2)) : ℝ) : ℂ)) y := by
    fun_prop
  refine hcont.congr ?_
  filter_upwards [Ioo_mem_nhds hy0 hy] with z hz
  exact (fractLogCarrier_eq_left hz.1 hz.2).symm

theorem continuousAt_fractLogCarrier_right {y : ℝ} (hy : Real.log 2 < y) (hy3 : y < Real.log 3) :
    ContinuousAt fractLogCarrier y := by
  have hcont : ContinuousAt
      (fun z : ℝ => ((Real.exp z - 2 : ℝ) : ℂ) * ((Real.exp (-(z / 2)) : ℝ) : ℂ)) y := by
    fun_prop
  refine hcont.congr ?_
  filter_upwards [Ioo_mem_nhds hy hy3] with z hz
  exact (fractLogCarrier_eq_right hz.1 hz.2).symm


/-! ## Zeta is not square integrable on the critical line -/

/-- Left branch of the carrier near `log 2`. -/
def fractLogLeft (w : ℝ) : ℂ :=
  ((Real.exp w - 1 : ℝ) : ℂ) * ((Real.exp (-(w / 2)) : ℝ) : ℂ)

/-- Right branch of the carrier near `log 2`. -/
def fractLogRight (w : ℝ) : ℂ :=
  ((Real.exp w - 2 : ℝ) : ℂ) * ((Real.exp (-(w / 2)) : ℝ) : ℂ)

theorem continuous_fractLogLeft : Continuous fractLogLeft := by
  unfold fractLogLeft; fun_prop

theorem continuous_fractLogRight : Continuous fractLogRight := by
  unfold fractLogRight; fun_prop

/-- **Zeta is not square integrable along the critical line, in the Fourier parametrisation.** -/
theorem not_memLp_riemannZeta_criticalAbscissa :
    ¬ MemLp (fun xi : ℝ => riemannZeta (criticalAbscissa xi)) 2 volume := by
  intro h
  have hFint : Integrable (𝓕 fractLogCarrier) volume := integrable_fourier_fractLogCarrier h
  have hcont : Continuous (𝓕⁻ (𝓕 fractLogCarrier)) :=
    continuous_fourierInv_of_integrable hFint
  have hval : ∀ {y : ℝ}, ContinuousAt fractLogCarrier y →
      𝓕⁻ (𝓕 fractLogCarrier) y = fractLogCarrier y := fun hy =>
    integrable_fractLogCarrier.fourierInv_fourier_eq hFint hy
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  have hdiv : ∀ c : ℝ, Tendsto (fun k : ℕ => c / ((k : ℝ) + 2)) atTop (nhds 0) := by
    intro c
    apply Filter.Tendsto.div_atTop tendsto_const_nhds
    exact tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hytend : Tendsto (fun k : ℕ => Real.log 2 - Real.log 2 / ((k : ℝ) + 2)) atTop
      (nhds (Real.log 2)) := by
    have := (tendsto_const_nhds (x := Real.log 2) (f := atTop (α := ℕ))).sub (hdiv (Real.log 2))
    simpa using this
  have hztend : Tendsto
      (fun k : ℕ => Real.log 2 + (Real.log 3 - Real.log 2) / ((k : ℝ) + 2)) atTop
      (nhds (Real.log 2)) := by
    have := (tendsto_const_nhds (x := Real.log 2) (f := atTop (α := ℕ))).add
      (hdiv (Real.log 3 - Real.log 2))
    simpa using this
  have hkpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 2 := fun k => by positivity
  have hk1 : ∀ k : ℕ, (1 : ℝ) < (k : ℝ) + 2 := fun k => by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hmemy : ∀ k : ℕ, Real.log 2 - Real.log 2 / ((k : ℝ) + 2) ∈ Ioo 0 (Real.log 2) := by
    intro k
    have hlt : Real.log 2 / ((k : ℝ) + 2) < Real.log 2 :=
      div_lt_self hlog2 (hk1 k)
    have hgt : 0 < Real.log 2 / ((k : ℝ) + 2) := by positivity
    exact ⟨by linarith, by linarith⟩
  have hmemz : ∀ k : ℕ,
      Real.log 2 + (Real.log 3 - Real.log 2) / ((k : ℝ) + 2) ∈ Ioo (Real.log 2) (Real.log 3) := by
    intro k
    have hpos : 0 < Real.log 3 - Real.log 2 := by linarith
    have hlt : (Real.log 3 - Real.log 2) / ((k : ℝ) + 2) < Real.log 3 - Real.log 2 :=
      div_lt_self hpos (hk1 k)
    have hgt : 0 < (Real.log 3 - Real.log 2) / ((k : ℝ) + 2) := by positivity
    exact ⟨by linarith, by linarith⟩
  have hleft : 𝓕⁻ (𝓕 fractLogCarrier) (Real.log 2) = fractLogLeft (Real.log 2) := by
    refine tendsto_nhds_unique ((hcont.tendsto _).comp hytend) ?_
    have heq : ∀ k : ℕ,
        𝓕⁻ (𝓕 fractLogCarrier) (Real.log 2 - Real.log 2 / ((k : ℝ) + 2)) =
          fractLogLeft (Real.log 2 - Real.log 2 / ((k : ℝ) + 2)) := by
      intro k
      rw [hval (continuousAt_fractLogCarrier_left (hmemy k).1 (hmemy k).2),
        fractLogCarrier_eq_left (hmemy k).1 (hmemy k).2, fractLogLeft]
    simp only [Function.comp_def, heq]
    exact (continuous_fractLogLeft.tendsto _).comp hytend
  have hright : 𝓕⁻ (𝓕 fractLogCarrier) (Real.log 2) = fractLogRight (Real.log 2) := by
    refine tendsto_nhds_unique ((hcont.tendsto _).comp hztend) ?_
    have heq : ∀ k : ℕ,
        𝓕⁻ (𝓕 fractLogCarrier)
            (Real.log 2 + (Real.log 3 - Real.log 2) / ((k : ℝ) + 2)) =
          fractLogRight (Real.log 2 + (Real.log 3 - Real.log 2) / ((k : ℝ) + 2)) := by
      intro k
      rw [hval (continuousAt_fractLogCarrier_right (hmemz k).1 (hmemz k).2),
        fractLogCarrier_eq_right (hmemz k).1 (hmemz k).2, fractLogRight]
    simp only [Function.comp_def, heq]
    exact (continuous_fractLogRight.tendsto _).comp hztend
  have hjump : fractLogLeft (Real.log 2) = fractLogRight (Real.log 2) := by
    rw [← hleft, hright]
  rw [fractLogLeft, fractLogRight, Real.exp_log (by norm_num : (0:ℝ) < 2)] at hjump
  norm_num at hjump
  have hexp : (0 : ℝ) < Real.exp (-(Real.log 2 / 2)) := Real.exp_pos _
  rw [Complex.ofReal_eq_zero] at hjump
  linarith

end RHTower
