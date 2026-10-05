import GaloisForLFunctions.RHTower.RieszFunctionMellinCriterion
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa

/-!
# The Hardy--Littlewood function and its Mellin transform

Hardy and Littlewood's function is `H(x) = Σ_{k ≥ 1} (-x)^k / (k! ζ(2k+1))`.  Expanding
`1/ζ(2k+1)` as a Möbius series and summing over `k` first gives the absolutely convergent form
`H(x) = Σ_n μ(n) n^{-1}(e^{-x/n²} - 1)` (`hardyLittlewoodFunction_eq_tsum`), with `|H(x)| ≤ ζ(3) x`.

The shifted Gamma integral `∫_0^∞ t^{s-1}(e^{-t} - 1) dt = Γ(s)` for `-1 < Re s < 0` (integration by
parts against `t^s/s`) gives, termwise, `∫_0^∞ H(t) t^{s-1} dt = Γ(s) Σ_n μ(n) n^{2s-1}
= Γ(s)/ζ(1 - 2s)` on `-1 < Re s < 0`.  If `H(x) = O(x^{-b})` at infinity, the transform is
holomorphic on `-1 < Re s < b`, and `mellin H (s) · Z(1 - 2s) = -2Γ(s + 1)` (`Z(w) = (w-1)ζ(w)`)
extends there by the identity theorem; a zero `ρ` with `Re ρ > 1 - 2b` kills the left side at
`s = (1 - ρ)/2`.  So `H(x) = O(x^b)` forces every zeta zero to `Re ρ ≤ 1 + 2b`, and `H` is never
`O(x^b)` with `b < -¼`.
-/

open Complex Filter MeasureTheory Set Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- `|e^{-t} - 1| ≤ min(t, 1)` for `t ≥ 0`, as two bounds. -/
theorem abs_exp_neg_sub_one_le_min {t : ℝ} (ht : 0 ≤ t) :
    |Real.exp (-t) - 1| ≤ t ∧ |Real.exp (-t) - 1| ≤ 1 := by
  have h1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h2 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have h3 := Real.exp_pos (-t)
  rw [abs_of_nonpos (by linarith)]
  exact ⟨by linarith, by linarith⟩

theorem norm_cexp_neg_sub_one_le {t : ℝ} (ht : 0 ≤ t) :
    ‖cexp (-(t : ℂ)) - 1‖ ≤ t ∧ ‖cexp (-(t : ℂ)) - 1‖ ≤ 1 := by
  have h : cexp (-(t : ℂ)) - 1 = ((Real.exp (-t) - 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [h, Complex.norm_real, Real.norm_eq_abs]
  exact abs_exp_neg_sub_one_le_min ht

/-- The majorant `t^{σ-1} min(t, 1)` is integrable on `(0, ∞)` for `-1 < σ < 0`. -/
theorem integrableOn_rpow_mul_min_Ioi {σ : ℝ} (hσ1 : -1 < σ) (hσ0 : σ < 0) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * min t 1) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h : IntegrableOn (fun t : ℝ => t ^ σ) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hσ1)
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioc
    rw [min_eq_left ht.2, ← Real.rpow_add_one ht.1.ne']
    ring_nf
  · have h := integrableOn_Ioi_rpow_of_lt (a := σ - 1) (by linarith) one_pos
    refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
    rw [min_eq_right (le_of_lt ht), mul_one]

/-- **The shifted Gamma integral.**  For `-1 < Re s < 0`,
`∫_0^∞ t^{s-1}(e^{-t} - 1) dt = Γ(s)` (integration by parts against `t^s/s`). -/
theorem integral_cpow_mul_cexp_neg_sub_one {s : ℂ} (hs1 : -1 < s.re) (hs0 : s.re < 0) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (cexp (-(t : ℂ)) - 1) = Complex.Gamma s := by
  have hs : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
  set u : ℝ → ℂ := fun t => cexp (-(t : ℂ)) - 1 with hu
  set v : ℝ → ℂ := fun t => (t : ℂ) ^ s / s with hv
  have hu' : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (-cexp (-(x : ℂ))) x := by
    intro x _
    have h1 : HasDerivAt (fun w : ℂ => cexp (-w)) (-cexp (-(x : ℂ))) (x : ℂ) := by
      have := (hasDerivAt_neg (x : ℂ)).cexp
      simpa using this
    exact h1.comp_ofReal.sub_const 1
  have hv' : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v ((x : ℂ) ^ (s - 1)) x := by
    intro x hx
    have h := (hasDerivAt_ofReal_cpow_const (ne_of_gt hx) hs).div_const s
    exact h.congr_deriv (mul_div_cancel_left₀ _ hs)
  have hnorm : ∀ t : ℝ, 0 < t → ‖(t : ℂ) ^ (s - 1)‖ = t ^ (s.re - 1) := fun t ht => by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht]; simp
  have huv' : IntegrableOn (u * fun t : ℝ => (t : ℂ) ^ (s - 1)) (Ioi 0) := by
    refine (integrableOn_rpow_mul_min_Ioi hs1 hs0).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
      refine ContinuousAt.continuousWithinAt ?_
      have hc1 : ContinuousAt u t := by
        simp only [hu]; fun_prop
      have hc2 : ContinuousAt (fun t : ℝ => (t : ℂ) ^ (s - 1)) t :=
        (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht)))
      exact hc1.mul hc2
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      simp only [Pi.mul_apply, hu]
      rw [norm_mul, hnorm t ht0, mul_comm]
      obtain ⟨h1, h2⟩ := norm_cexp_neg_sub_one_le ht0.le
      exact mul_le_mul_of_nonneg_left (le_min h1 h2) (Real.rpow_nonneg ht0.le _)
  have hGint : IntegrableOn (fun x : ℝ => ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (s + 1 - 1))
      (Ioi 0) := Complex.GammaIntegral_convergent (by simp; linarith)
  have hu'v : IntegrableOn ((fun t : ℝ => -cexp (-(t : ℂ))) * v) (Ioi 0) := by
    have := hGint.const_mul (-(1 / s))
    refine IntegrableOn.congr_fun this (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.mul_apply, hv, add_sub_cancel_right, Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  have hzero : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => t ^ (s.re + 1) / ‖s‖) (𝓝[>] 0) (𝓝 0) := by
      have h := ((Real.continuousAt_rpow_const 0 (s.re + 1) (Or.inr (by linarith))).tendsto)
      rw [Real.zero_rpow (by linarith)] at h
      simpa using (h.div_const ‖s‖).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    simp only [Pi.mul_apply, hu, hv]
    rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
      Real.rpow_add ht0, Real.rpow_one]
    obtain ⟨h1, -⟩ := norm_cexp_neg_sub_one_le ht0.le
    have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs
    rw [mul_div_assoc', le_div_iff₀ hsn, div_mul_cancel₀ _ hsn.ne']
    calc ‖cexp (-(t : ℂ)) - 1‖ * t ^ s.re ≤ t * t ^ s.re :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht0.le _)
      _ = t ^ s.re * t := mul_comm _ _
  have hinfty : Tendsto (u * v) atTop (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ => t ^ s.re / ‖s‖) atTop (𝓝 0) := by
      have h := tendsto_rpow_neg_atTop (y := -s.re) (by linarith)
      simp only [neg_neg] at h
      simpa using h.div_const ‖s‖
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_gt_atTop 0] with t ht0
    simp only [Pi.mul_apply, hu, hv]
    rw [norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    obtain ⟨-, h2⟩ := norm_cexp_neg_sub_one_le ht0.le
    have hsn : 0 < ‖s‖ := norm_pos_iff.mpr hs
    calc ‖cexp (-(t : ℂ)) - 1‖ * (t ^ s.re / ‖s‖) ≤ 1 * (t ^ s.re / ‖s‖) :=
          mul_le_mul_of_nonneg_right h2 (div_nonneg (Real.rpow_nonneg ht0.le _) hsn.le)
      _ = t ^ s.re / ‖s‖ := one_mul _
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu' hv' huv' hu'v hzero hinfty
  have hcomm : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (cexp (-(t : ℂ)) - 1) =
      ∫ t in Ioi (0 : ℝ), u t * (t : ℂ) ^ (s - 1) :=
    integral_congr_ae (Eventually.of_forall fun t => by simp only [hu]; ring)
  rw [hcomm, hibp]
  have hG : ∫ t in Ioi (0 : ℝ), -cexp (-(t : ℂ)) * v t = -(1 / s) * Complex.Gamma (s + 1) := by
    rw [Complex.Gamma_eq_integral (by simp; linarith), Complex.GammaIntegral, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hv, add_sub_cancel_right, Complex.ofReal_exp, Complex.ofReal_neg]
    ring
  rw [hG, Complex.Gamma_add_one s hs]
  field_simp
  ring

/-- The scaled shifted Gamma integral: `∫_0^∞ t^{s-1}(e^{-rt} - 1) dt = r^{-s} Γ(s)`. -/
theorem integral_cpow_mul_cexp_neg_mul_sub_one {s : ℂ} (hs1 : -1 < s.re) (hs0 : s.re < 0)
    {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (cexp (-((r : ℂ) * t)) - 1) =
      (1 / r) ^ s * Complex.Gamma s := by
  have aux : (1 / r : ℂ) ^ s = 1 / r * (1 / r) ^ (s - 1) := by
    nth_rewrite 2 [← cpow_one (1 / r : ℂ)]
    rw [← cpow_add _ _ (one_div_ne_zero <| ofReal_ne_zero.mpr hr.ne'), add_sub_cancel]
  calc
    _ = ∫ (t : ℝ) in Ioi 0, (1 / r) ^ (s - 1) * (r * t) ^ (s - 1) *
          (cexp (-((r : ℂ) * t)) - 1) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ ?_)
      rw [mem_Ioi] at hx
      rw [mul_cpow_ofReal_nonneg hr.le hx.le, ← mul_assoc, one_div, ← ofReal_inv,
        ← mul_cpow_ofReal_nonneg (inv_pos.mpr hr).le hr.le, ← ofReal_mul r⁻¹,
        inv_mul_cancel₀ hr.ne', ofReal_one, one_cpow, one_mul]
    _ = 1 / r * ∫ (t : ℝ) in Ioi 0, (1 / r) ^ (s - 1) * t ^ (s - 1) * (cexp (-(t : ℂ)) - 1) := by
      simp_rw [← ofReal_mul]
      rw [integral_comp_mul_left_Ioi (fun x ↦ _ * (x : ℂ) ^ (s - 1) * (cexp (-(x : ℂ)) - 1)) _
        hr, mul_zero, real_smul, ← one_div, ofReal_div, ofReal_one]
    _ = 1 / r * (1 / r : ℂ) ^ (s - 1) *
          (∫ (t : ℝ) in Ioi 0, (t : ℂ) ^ (s - 1) * (cexp (-(t : ℂ)) - 1)) := by
      simp_rw [← MeasureTheory.integral_const_mul, mul_assoc]
    _ = (1 / r) ^ s * Complex.Gamma s := by
      rw [aux, integral_cpow_mul_cexp_neg_sub_one hs1 hs0]

/-- The real form: `∫_0^∞ t^{σ-1}(1 - e^{-rt}) dt = -r^{-σ} Γ(σ)` for `-1 < σ < 0`. -/
theorem integral_rpow_mul_one_sub_exp_neg_mul {σ : ℝ} (hσ1 : -1 < σ) (hσ0 : σ < 0) {r : ℝ}
    (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * (1 - Real.exp (-(r * t))) =
      -((1 / r) ^ σ * Real.Gamma σ) := by
  have h := integral_cpow_mul_cexp_neg_mul_sub_one (s := (σ : ℂ)) (by simpa using hσ1)
    (by simpa using hσ0) hr
  have hcongr : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((σ : ℂ) - 1) * (cexp (-((r : ℂ) * t)) - 1) =
      ∫ t in Ioi (0 : ℝ), ((-(t ^ (σ - 1) * (1 - Real.exp (-(r * t)))) : ℝ) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    rw [show ((σ : ℂ) - 1) = ((σ - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht0.le]
    push_cast
    ring
  rw [hcongr, integral_complex_ofReal, integral_neg,
    show ((1 / r : ℂ)) ^ (σ : ℂ) = (((1 / r) ^ σ : ℝ) : ℂ) by
      rw [Complex.ofReal_cpow (by positivity)]; push_cast; rfl,
    Complex.Gamma_ofReal, ← Complex.ofReal_mul, Complex.ofReal_inj] at h
  linarith

/-! ## The Hardy--Littlewood function -/

/-- The regularized term `μ(n) n^{-1}(e^{-x/n²} - 1)`. -/
def hardyLittlewoodTerm (x : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) * ((n : ℝ)⁻¹ * (Real.exp (-(x * ((n : ℝ) ^ 2)⁻¹)) - 1))

/-- **The Hardy--Littlewood function** `H(x) = Σ_n μ(n) n^{-1}(e^{-x/n²} - 1)`, which equals
`Σ_{k ≥ 1} (-x)^k/(k! ζ(2k+1))`. -/
def hardyLittlewoodFunction (x : ℝ) : ℝ := ∑' n : ℕ, hardyLittlewoodTerm x n

theorem abs_hardyLittlewoodTerm_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    |hardyLittlewoodTerm x n| ≤ x * ((n : ℝ) ^ 3)⁻¹ := by
  unfold hardyLittlewoodTerm
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hy : 0 ≤ x * ((n : ℝ) ^ 2)⁻¹ := by positivity
  have he := (abs_exp_neg_sub_one_le_min hy).1
  rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hn')]
  calc |(ArithmeticFunction.moebius n : ℝ)| * ((n : ℝ)⁻¹ *
        |Real.exp (-(x * ((n : ℝ) ^ 2)⁻¹)) - 1|)
      ≤ 1 * ((n : ℝ)⁻¹ * (x * ((n : ℝ) ^ 2)⁻¹)) := by gcongr
    _ = x * ((n : ℝ) ^ 3)⁻¹ := by field_simp

theorem summable_natCast_cube_inv : Summable fun n : ℕ => ((n : ℝ) ^ 3)⁻¹ :=
  Real.summable_nat_pow_inv.mpr (by norm_num)

theorem summable_hardyLittlewoodTerm {x : ℝ} (hx : 0 ≤ x) : Summable (hardyLittlewoodTerm x) :=
  Summable.of_norm_bounded (summable_natCast_cube_inv.mul_left x) fun n => by
    rw [Real.norm_eq_abs]; exact abs_hardyLittlewoodTerm_le hx n

theorem abs_hardyLittlewoodFunction_le {x : ℝ} (hx : 0 ≤ x) :
    |hardyLittlewoodFunction x| ≤ x * ∑' n : ℕ, ((n : ℝ) ^ 3)⁻¹ := by
  unfold hardyLittlewoodFunction
  rw [← Real.norm_eq_abs, ← tsum_mul_left]
  refine (norm_tsum_le_tsum_norm (summable_hardyLittlewoodTerm hx).norm).trans ?_
  exact (summable_hardyLittlewoodTerm hx).norm.tsum_le_tsum (fun n => by
    rw [Real.norm_eq_abs]; exact abs_hardyLittlewoodTerm_le hx n)
    (summable_natCast_cube_inv.mul_left x)

theorem continuousOn_hardyLittlewoodFunction_Icc (B : ℝ) :
    ContinuousOn hardyLittlewoodFunction (Icc 0 B) := by
  refine continuousOn_tsum (u := fun n : ℕ => |B| * ((n : ℝ) ^ 3)⁻¹) (fun n => ?_)
    (summable_natCast_cube_inv.mul_left _) (fun n x hx => ?_)
  · unfold hardyLittlewoodTerm
    fun_prop
  · rw [Real.norm_eq_abs]
    refine (abs_hardyLittlewoodTerm_le hx.1 n).trans ?_
    exact mul_le_mul_of_nonneg_right (hx.2.trans (le_abs_self B)) (by positivity)

theorem continuousOn_hardyLittlewoodFunction : ContinuousOn hardyLittlewoodFunction (Ioi 0) := by
  intro x hx
  have hx0 : (0 : ℝ) < x := hx
  refine ((continuousOn_hardyLittlewoodFunction_Icc (x + 1)).continuousAt ?_).continuousWithinAt
  exact Icc_mem_nhds hx0 (by linarith)

/-! ## The Mellin transform of `H` -/

theorem ofReal_hardyLittlewoodTerm (t : ℝ) (n : ℕ) :
    ((hardyLittlewoodTerm t n : ℝ) : ℂ) = ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      ((n : ℂ)⁻¹ * (cexp (-(((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * t)) - 1)) := by
  unfold hardyLittlewoodTerm
  push_cast
  rw [mul_comm (t : ℂ)]

theorem integral_cpow_mul_hardyLittlewoodTerm {s : ℂ} (hs1 : -1 < s.re) (hs0 : s.re < 0)
    (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * ((hardyLittlewoodTerm t n : ℝ) : ℂ) =
      Complex.Gamma s * LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        (1 - 2 * s) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hardyLittlewoodTerm]
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hr : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹ := by positivity
  simp_rw [ofReal_hardyLittlewoodTerm]
  have hrw : ∀ t : ℝ, (t : ℂ) ^ (s - 1) * (((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      ((n : ℂ)⁻¹ * (cexp (-(((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * t)) - 1))) =
      (((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ)⁻¹) *
        ((t : ℂ) ^ (s - 1) * (cexp (-(((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * t)) - 1)) := fun t => by ring
  simp_rw [hrw]
  rw [integral_const_mul, integral_cpow_mul_cexp_neg_mul_sub_one hs1 hs0 hr,
    LSeries.term_of_ne_zero hn]
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h1 : (1 / ((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) = (n : ℂ) ^ 2 := by push_cast; simp
  have h2 : ((n : ℂ) ^ 2) ^ s = (n : ℂ) ^ (2 * s) := by
    rw [← Complex.natCast_cpow_natCast_mul]; norm_num
  have h3 : (n : ℂ) ^ (1 - 2 * s) = (n : ℂ) / (n : ℂ) ^ (2 * s) := by
    rw [Complex.cpow_sub _ _ hnc, Complex.cpow_one]
  rw [h1, h2, h3]
  have h4 : (n : ℂ) ^ (2 * s) ≠ 0 := by
    intro h; exact hnc ((cpow_eq_zero_iff _ _).mp h).1
  field_simp

theorem integrable_cpow_mul_hardyLittlewoodTerm {s : ℂ} (hs1 : -1 < s.re) (hs0 : s.re < 0)
    (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * ((hardyLittlewoodTerm t n : ℝ) : ℂ))
      (Ioi 0) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hardyLittlewoodTerm]
  have hr : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹ := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  have hbase : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) *
      (cexp (-(((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * t)) - 1)) (Ioi 0) := by
    refine Integrable.of_integral_ne_zero ?_
    rw [integral_cpow_mul_cexp_neg_mul_sub_one hs1 hs0 hr]
    refine mul_ne_zero (fun h => ?_) (Complex.Gamma_ne_zero fun m hm => ?_)
    · have := ((cpow_eq_zero_iff _ _).mp h).1
      simp at this
      exact hn this
    · have : s.re = -(m : ℝ) := by rw [hm]; simp
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0] at this; simp at this; linarith
      · have : (1 : ℝ) ≤ m := by exact_mod_cast h0
        linarith
  have h := hbase.const_mul (((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ)⁻¹)
  have hfun : (fun t : ℝ => (t : ℂ) ^ (s - 1) * ((hardyLittlewoodTerm t n : ℝ) : ℂ)) =
      fun t : ℝ => (((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ)⁻¹) *
        ((t : ℂ) ^ (s - 1) * (cexp (-(((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * t)) - 1)) := by
    funext t
    rw [ofReal_hardyLittlewoodTerm]
    ring
  rw [hfun]
  exact h

theorem neg_Gamma_nonneg {σ : ℝ} (hσ1 : -1 < σ) (hσ0 : σ < 0) : 0 ≤ -Real.Gamma σ := by
  have h := integral_rpow_mul_one_sub_exp_neg_mul hσ1 hσ0 one_pos
  have hnn : 0 ≤ ∫ t in Ioi (0 : ℝ), t ^ (σ - 1) * (1 - Real.exp (-(1 * t))) := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    refine mul_nonneg (Real.rpow_nonneg ht0.le _) ?_
    have : Real.exp (-(1 * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  rw [h] at hnn
  simpa using hnn

theorem integral_norm_cpow_mul_hardyLittlewoodTerm_le {s : ℂ} (hs1 : -1 < s.re)
    (hs0 : s.re < 0) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * ((hardyLittlewoodTerm t n : ℝ) : ℂ)‖ ≤
      -Real.Gamma s.re * (n : ℝ) ^ (2 * s.re - 1) := by
  have hΓ := neg_Gamma_nonneg hs1 hs0
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : ∀ t : ℝ, hardyLittlewoodTerm t 0 = 0 := fun t => by simp [hardyLittlewoodTerm]
    simp only [h0, Complex.ofReal_zero, mul_zero, norm_zero, integral_zero]
    exact mul_nonneg hΓ (Real.rpow_nonneg (Nat.cast_nonneg 0) _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set r : ℝ := ((n : ℝ) ^ 2)⁻¹ with hr_def
  have hr : 0 < r := by positivity
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * ((hardyLittlewoodTerm t n : ℝ) : ℂ)‖ =
      (|(ArithmeticFunction.moebius n : ℝ)| * (n : ℝ)⁻¹) *
        (t ^ (s.re - 1) * (1 - Real.exp (-(r * t)))) := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real, Real.norm_eq_abs]
    unfold hardyLittlewoodTerm
    have he : Real.exp (-(t * r)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hn'),
      abs_of_nonpos (a := Real.exp (-(t * r)) - 1) (by linarith),
      Complex.sub_re, Complex.one_re, mul_comm t r]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_rpow_mul_one_sub_exp_neg_mul hs1 hs0 hr]
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hpow : (n : ℝ)⁻¹ * (1 / r) ^ s.re = (n : ℝ) ^ (2 * s.re - 1) := by
    rw [hr_def, one_div, inv_inv, Real.rpow_sub hn', Real.rpow_mul hn'.le, Real.rpow_one]
    norm_cast
    ring
  calc |(ArithmeticFunction.moebius n : ℝ)| * (n : ℝ)⁻¹ * -((1 / r) ^ s.re * Real.Gamma s.re)
      ≤ 1 * (n : ℝ)⁻¹ * -((1 / r) ^ s.re * Real.Gamma s.re) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hμ (by positivity)) ?_
        have : 0 ≤ (1 / r) ^ s.re := Real.rpow_nonneg (by positivity) _
        nlinarith
    _ = -Real.Gamma s.re * (n : ℝ) ^ (2 * s.re - 1) := by rw [← hpow]; ring

/-- **The Mellin transform of the Hardy--Littlewood function.**  For `-1 < Re s < 0`,
`∫_0^∞ H(t) t^{s-1} dt = Γ(s) Σ_n μ(n) n^{2s-1} = Γ(s)/ζ(1 - 2s)`. -/
theorem mellin_hardyLittlewoodFunction {s : ℂ} (hs1 : -1 < s.re) (hs0 : s.re < 0) :
    mellin (fun t => ((hardyLittlewoodFunction t : ℝ) : ℂ)) s =
      Complex.Gamma s * LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        (1 - 2 * s) := by
  unfold mellin
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • ((hardyLittlewoodFunction t : ℝ) : ℂ) =
      ∑' n : ℕ, (t : ℂ) ^ (s - 1) * ((hardyLittlewoodTerm t n : ℝ) : ℂ) := by
    intro t _
    rw [smul_eq_mul, hardyLittlewoodFunction, Complex.ofReal_tsum, tsum_mul_left]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hsum : Summable fun n : ℕ =>
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * ((hardyLittlewoodTerm t n : ℝ) : ℂ)‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
      (integral_norm_cpow_mul_hardyLittlewoodTerm_le hs1 hs0) ?_
    exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  rw [← integral_tsum_of_summable_integral_norm
    (integrable_cpow_mul_hardyLittlewoodTerm hs1 hs0) hsum]
  simp_rw [integral_cpow_mul_hardyLittlewoodTerm hs1 hs0]
  rw [tsum_mul_left]
  rfl

/-! ## Decay of `H` and the zeros of `ζ` -/

/-- On `-1 < Re s < 0`: `mellin H (s) · Z(1 - 2s) = -2Γ(s + 1)`, with `Z(w) = (w - 1)ζ(w)`. -/
theorem mellin_hardyLittlewoodFunction_mul_zetaResidueUnit {s : ℂ} (hs1 : -1 < s.re)
    (hs0 : s.re < 0) :
    mellin (fun t => ((hardyLittlewoodFunction t : ℝ) : ℂ)) s * zetaResidueUnit (1 - 2 * s) =
      -2 * Complex.Gamma (s + 1) := by
  have hw : 1 < (1 - 2 * s).re := by simp; linarith
  have hw1 : (1 - 2 * s) ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hw; exact lt_irrefl _ hw
  have hs : s ≠ 0 := by intro h; rw [h, Complex.zero_re] at hs0; exact lt_irrefl _ hs0
  rw [mellin_hardyLittlewoodFunction hs1 hs0, zetaResidueUnit, Function.update_of_ne hw1,
    Complex.Gamma_add_one s hs]
  have hL := LSeries_moebius_mul_riemannZeta hw
  calc Complex.Gamma s * LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (1 - 2 * s) *
        ((1 - 2 * s - 1) * riemannZeta (1 - 2 * s))
      = -2 * (s * Complex.Gamma s) *
          (LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (1 - 2 * s) *
            riemannZeta (1 - 2 * s)) := by ring
    _ = -2 * (s * Complex.Gamma s) := by rw [hL, mul_one]

/-- The open strip `-1 < Re s < b`. -/
def hardyLittlewoodStrip (b : ℝ) : Set ℂ := {s : ℂ | -1 < s.re ∧ s.re < b}

theorem isOpen_hardyLittlewoodStrip (b : ℝ) : IsOpen (hardyLittlewoodStrip b) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem differentiableOn_mellin_hardyLittlewoodFunction {b C X : ℝ}
    (hbound : ∀ x : ℝ, X ≤ x → |hardyLittlewoodFunction x| ≤ C * x ^ (-b)) :
    DifferentiableOn ℂ (mellin fun t => ((hardyLittlewoodFunction t : ℝ) : ℂ))
      (hardyLittlewoodStrip b) := by
  intro s hs
  refine DifferentiableAt.differentiableWithinAt ?_
  refine mellin_differentiableAt_of_isBigO_rpow (a := b) (b := -1) ?_ ?_ hs.2 ?_ hs.1
  · exact (Complex.continuous_ofReal.comp_continuousOn
      continuousOn_hardyLittlewoodFunction).locallyIntegrableOn measurableSet_Ioi
  · refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (max X 1)] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    exact hbound x ((le_max_left _ _).trans hx)
  · refine Asymptotics.IsBigO.of_bound (∑' n : ℕ, ((n : ℝ) ^ 3)⁻¹) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [Complex.norm_real, Real.norm_eq_abs, neg_neg, Real.rpow_one, Real.norm_eq_abs,
      abs_of_pos hx0, mul_comm]
    exact abs_hardyLittlewoodFunction_le hx0.le

/-- **Hardy--Littlewood decay pushes zeta zeros left.**  If `|H(x)| ≤ C x^{-b}` for large `x`,
then `ζ` has no zero with `Re ρ > 1 - 2b`. -/
theorem riemannZeta_ne_zero_of_hardyLittlewoodFunction_le {b C X : ℝ}
    (hbound : ∀ x : ℝ, X ≤ x → |hardyLittlewoodFunction x| ≤ C * x ^ (-b)) {ρ : ℂ}
    (hρ : 1 - 2 * b < ρ.re) : riemannZeta ρ ≠ 0 := by
  intro hzero
  have hρ1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hzero
  set U := hardyLittlewoodStrip b
  set f : ℂ → ℂ := fun s =>
    mellin (fun t => ((hardyLittlewoodFunction t : ℝ) : ℂ)) s * zetaResidueUnit (1 - 2 * s)
  set g : ℂ → ℂ := fun s => -2 * Complex.Gamma (s + 1)
  have hf : AnalyticOnNhd ℂ f U := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_hardyLittlewoodStrip b)
    refine (differentiableOn_mellin_hardyLittlewoodFunction hbound).mul ?_
    intro s _
    exact ((analyticAt_zetaResidueUnit _).differentiableAt.comp s
      ((differentiableAt_const _).sub ((differentiableAt_const _).mul
        differentiableAt_id))).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ g U := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_hardyLittlewoodStrip b)
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (differentiableAt_const _).mul ?_
    refine (Complex.differentiableAt_Gamma (s + 1) fun m hm => ?_).comp s
      (differentiableAt_id.add (differentiableAt_const _))
    have : s.re + 1 = -(m : ℝ) := by
      have := congrArg Complex.re hm; simpa using this
    have := hs.1
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hb0 : 0 < b := by linarith
  have hs₀ : ((-1 / 2 : ℝ) : ℂ) ∈ U := ⟨by norm_num, by simp; linarith⟩
  have hfg : f =ᶠ[𝓝 ((-1 / 2 : ℝ) : ℂ)] g := by
    have hopen : IsOpen (hardyLittlewoodStrip 0) := isOpen_hardyLittlewoodStrip _
    have hmem : ((-1 / 2 : ℝ) : ℂ) ∈ hardyLittlewoodStrip 0 := ⟨by norm_num, by norm_num⟩
    filter_upwards [hopen.mem_nhds hmem] with s hs
    exact mellin_hardyLittlewoodFunction_mul_zetaResidueUnit hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg
    ((convex_halfSpace_re_gt (-1) |>.inter (convex_halfSpace_re_lt b)).isPreconnected) hs₀ hfg
  set s : ℂ := (1 - ρ) / 2 with hs_def
  have hsre : s.re = (1 - ρ.re) / 2 := by simp [hs_def]
  have hsU : s ∈ U := ⟨by rw [hsre]; linarith, by rw [hsre]; linarith⟩
  have h2s : 1 - 2 * s = ρ := by rw [hs_def]; ring
  have hfs : f s = 0 := by
    simp only [f, h2s]
    have hne : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hρ1; exact lt_irrefl _ hρ1
    rw [zetaResidueUnit, Function.update_of_ne hne, hzero, mul_zero, mul_zero]
  have hgs : g s ≠ 0 := by
    refine mul_ne_zero (by norm_num) (Complex.Gamma_ne_zero_of_re_pos ?_)
    simp only [Complex.add_re, Complex.one_re]
    rw [hsre]; linarith
  exact hgs (heq hsU ▸ hfs)

/-- **Lower half of the Hardy--Littlewood exponent law.**  If `|H(x)| ≤ C x^b` for large `x`,
every zeta zero has `Re ρ ≤ 1 + 2b`. -/
theorem zetaZeroAbscissa_le_of_hardyLittlewoodFunction_le {b C X : ℝ}
    (h : ∀ x : ℝ, X ≤ x → |hardyLittlewoodFunction x| ≤ C * x ^ b) :
    zetaZeroAbscissa ≤ 1 + 2 * b := by
  by_contra hcon
  obtain ⟨ρ, hzero, hρ⟩ := exists_zetaZero_lt_re (not_le.mp hcon)
  exact riemannZeta_ne_zero_of_hardyLittlewoodFunction_le (b := -b) (C := C) (X := X)
    (fun x hx => by rw [neg_neg]; exact h x hx) (by linarith) hzero

/-- `H` is never `O(x^b)` with `b < -¼`. -/
theorem not_hardyLittlewoodFunction_le_of_lt {b : ℝ} (hb : b < -(1 / 4)) (C X : ℝ) :
    ¬ ∀ x : ℝ, X ≤ x → |hardyLittlewoodFunction x| ≤ C * x ^ b := fun h => by
  have := zetaZeroAbscissa_le_of_hardyLittlewoodFunction_le h
  have := half_le_zetaZeroAbscissa
  linarith

/-! ## The Hardy--Littlewood power series -/

/-- The tail of the exponential series: `Σ_{k ≥ 0} y^{k+1}/(k+1)! = e^y - 1`. -/
theorem tsum_pow_succ_div_factorial_eq_exp_sub_one (y : ℝ) :
    ∑' k : ℕ, y ^ (k + 1) / ((k + 1).factorial : ℝ) = Real.exp y - 1 := by
  have h := (Real.summable_pow_div_factorial y).tsum_eq_zero_add
  rw [tsum_pow_div_factorial_eq_exp] at h
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  linarith

/-- The double series `μ(n) n^{-1} (-x/n²)^{k+1}/(k+1)!`. -/
def hardyLittlewoodDoubleTerm (x : ℝ) (n k : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) * (n : ℝ)⁻¹ * (-(x * ((n : ℝ) ^ 2)⁻¹)) ^ (k + 1) /
    ((k + 1).factorial : ℝ)

theorem summable_uncurry_hardyLittlewoodDoubleTerm {x : ℝ} (hx : 0 ≤ x) :
    Summable (Function.uncurry (hardyLittlewoodDoubleTerm x)) := by
  set b : ℕ × ℕ → ℝ := fun p => (p.1 : ℝ)⁻¹ *
    ((x * ((p.1 : ℝ) ^ 2)⁻¹) ^ (p.2 + 1) / ((p.2 + 1).factorial : ℝ))
  have hb0 : 0 ≤ b := fun p => by positivity
  have hb : Summable b := by
    refine (summable_prod_of_nonneg hb0).mpr ⟨fun n => ?_, ?_⟩
    · exact ((summable_nat_add_iff 1).mpr (Real.summable_pow_div_factorial
        (x * ((n : ℝ) ^ 2)⁻¹))).mul_left ((n : ℝ)⁻¹)
    · have hrow : ∀ n : ℕ, ∑' k : ℕ, b (n, k) =
          (n : ℝ)⁻¹ * (Real.exp (x * ((n : ℝ) ^ 2)⁻¹) - 1) := fun n => by
        simp only [b]
        rw [tsum_mul_left, tsum_pow_succ_div_factorial_eq_exp_sub_one]
      simp_rw [hrow]
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
        (summable_natCast_cube_inv.mul_left (x * Real.exp x))
      · have : 1 ≤ Real.exp (x * ((n : ℝ) ^ 2)⁻¹) := Real.one_le_exp (by positivity)
        have : 0 ≤ (n : ℝ)⁻¹ := by positivity
        nlinarith
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
        set y := x * ((n : ℝ) ^ 2)⁻¹ with hy
        have hy0 : 0 ≤ y := by positivity
        have hyx : y ≤ x := by
          rw [hy]
          calc x * ((n : ℝ) ^ 2)⁻¹ ≤ x * 1 := by
                gcongr; exact inv_le_one_of_one_le₀ (by nlinarith)
            _ = x := mul_one x
        have hey : Real.exp y - 1 ≤ y * Real.exp y := by
          have h := Real.add_one_le_exp (-y)
          have hE := Real.exp_pos y
          have : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
          nlinarith
        have hexp : Real.exp y ≤ Real.exp x := Real.exp_le_exp.mpr hyx
        calc (n : ℝ)⁻¹ * (Real.exp y - 1) ≤ (n : ℝ)⁻¹ * (y * Real.exp x) := by
              gcongr
              exact hey.trans (mul_le_mul_of_nonneg_left hexp hy0)
          _ = x * Real.exp x * ((n : ℝ) ^ 3)⁻¹ := by rw [hy]; field_simp
  refine Summable.of_norm_bounded hb fun p => ?_
  obtain ⟨n, k⟩ := p
  simp only [Function.uncurry_apply_pair, hardyLittlewoodDoubleTerm, b, Real.norm_eq_abs]
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤
    (n : ℝ)⁻¹), abs_of_nonneg (by positivity : (0 : ℝ) ≤ x * ((n : ℝ) ^ 2)⁻¹),
    abs_of_pos (by positivity : (0 : ℝ) < ((k + 1).factorial : ℝ))]
  calc |(ArithmeticFunction.moebius n : ℝ)| * (n : ℝ)⁻¹ * (x * ((n : ℝ) ^ 2)⁻¹) ^ (k + 1) /
        ((k + 1).factorial : ℝ)
      ≤ 1 * (n : ℝ)⁻¹ * (x * ((n : ℝ) ^ 2)⁻¹) ^ (k + 1) / ((k + 1).factorial : ℝ) := by gcongr
    _ = (n : ℝ)⁻¹ * ((x * ((n : ℝ) ^ 2)⁻¹) ^ (k + 1) / ((k + 1).factorial : ℝ)) := by ring

theorem tsum_hardyLittlewoodDoubleTerm_eq (x : ℝ) (n : ℕ) :
    ∑' k : ℕ, hardyLittlewoodDoubleTerm x n k = hardyLittlewoodTerm x n := by
  unfold hardyLittlewoodDoubleTerm hardyLittlewoodTerm
  simp_rw [mul_div_assoc]
  rw [tsum_mul_left, tsum_pow_succ_div_factorial_eq_exp_sub_one]
  ring

theorem tsum_hardyLittlewoodDoubleTerm_eq_LSeries (x : ℝ) (k : ℕ) :
    ((∑' n : ℕ, hardyLittlewoodDoubleTerm x n k : ℝ) : ℂ) =
      (-x : ℂ) ^ (k + 1) / ((k + 1).factorial : ℂ) *
        LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 * k + 3) := by
  rw [Complex.ofReal_tsum, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hardyLittlewoodDoubleTerm]
  rw [LSeries.term_of_ne_zero hn, show (2 * (k : ℂ) + 3) = ((2 * k + 3 : ℕ) : ℂ) by
    push_cast; ring, Complex.cpow_natCast]
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  unfold hardyLittlewoodDoubleTerm
  push_cast
  have e : (n : ℂ) ^ (2 * k + 3) = (n : ℂ) * ((n : ℂ) ^ 2) ^ (k + 1) := by ring
  rw [e, neg_pow, mul_pow, inv_pow]
  field_simp
  rw [neg_pow]
  ring

/-- **The Hardy--Littlewood power series.**
`H(x) = Σ_{k ≥ 1} (-x)^k / (k! ζ(2k+1))` for `x ≥ 0`. -/
theorem hardyLittlewoodFunction_eq_tsum {x : ℝ} (hx : 0 ≤ x) :
    ((hardyLittlewoodFunction x : ℝ) : ℂ) = ∑' k : ℕ,
      (-1) ^ (k + 1) * (x : ℂ) ^ (k + 1) /
        (((k + 1).factorial : ℂ) * riemannZeta (2 * k + 3)) := by
  have hswap := (summable_uncurry_hardyLittlewoodDoubleTerm hx).tsum_comm
  have hH : hardyLittlewoodFunction x = ∑' k : ℕ, ∑' n : ℕ, hardyLittlewoodDoubleTerm x n k := by
    rw [hswap, hardyLittlewoodFunction]
    exact tsum_congr fun n => (tsum_hardyLittlewoodDoubleTerm_eq x n).symm
  rw [hH, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [tsum_hardyLittlewoodDoubleTerm_eq_LSeries]
  have hw : 1 < (2 * (k : ℂ) + 3).re := by
    rw [show (2 * (k : ℂ) + 3) = ((2 * k + 3 : ℕ) : ℂ) by push_cast; ring, Complex.natCast_re]
    exact_mod_cast (by omega : 1 < 2 * k + 3)
  have hL := LSeries_moebius_mul_riemannZeta hw
  have hζ : riemannZeta (2 * k + 3) ≠ 0 := right_ne_zero_of_mul_eq_one hL
  have hfac : ((k + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (k + 1).factorial_ne_zero
  rw [eq_div_iff (mul_ne_zero hfac hζ)]
  calc (-x : ℂ) ^ (k + 1) / ((k + 1).factorial : ℂ) *
        LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 * k + 3) *
        (((k + 1).factorial : ℂ) * riemannZeta (2 * k + 3))
      = (-x : ℂ) ^ (k + 1) * (LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
          (2 * k + 3) * riemannZeta (2 * k + 3)) := by field_simp
    _ = (-1) ^ (k + 1) * (x : ℂ) ^ (k + 1) := by rw [hL, neg_pow]; ring

end

end RHTower
